import OAI.AlgebraicGeometry.PlaneCurves.AnalyticJets
import OAI.AlgebraicGeometry.PlaneCurves.FrechetMultiplicity
import OAI.AlgebraicGeometry.PlaneCurves.NormalCharts

namespace OAI

/-!
# Divided analytic families, moving centres, and specialization jets; Local graph representation of inverse normal charts
-/

section

noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators

/-- Actual argument of the inverse normal chart in parameter and fiber variables. -/
def normalFamilyArgument (z : ℂ × ComplexPlane) : ComplexPlane := (z.2.1, z.1 * z.2.2)

/-- Finite divided normal family; every exponent is a natural number, so the
formula defines an actual function at the central parameter zero. -/
def dividedAnalyticFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ) (κ : ComplexPlane → ComplexPlane)
    (z : ℂ × ComplexPlane) : ℂ :=
  ∑ α ∈ I, z.1 ^ (α + j α - u) * z.2.2 ^ j α *
    planePolynomialEval (R α) (κ (normalFamilyArgument z))

theorem normalFamilyArgument_analyticAt (z : ℂ × ComplexPlane) :
    AnalyticAt ℂ normalFamilyArgument z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ ComplexPlane).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ ComplexPlane).analyticAt z
  have hu := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  exact hu.prod (hs.mul hw)

/-- Joint holomorphy of the actual divided normal family follows from actual
holomorphy of the inverse chart at its argument. -/
theorem dividedAnalyticFamily_analyticAt
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (κ : ComplexPlane → ComplexPlane) (z : ℂ × ComplexPlane)
    (hκ : AnalyticAt ℂ κ (normalFamilyArgument z)) :
    AnalyticAt ℂ (dividedAnalyticFamily I j R u κ) z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ ComplexPlane).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ ComplexPlane).analyticAt z
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hc := hκ.comp (normalFamilyArgument_analyticAt z)
  apply I.analyticAt_fun_sum
  intro α hα
  exact ((hs.pow (α + j α - u)).mul (hw.pow (j α))).mul
    ((planePolynomialEval_analyticAt (R α) (κ (normalFamilyArgument z))).comp (f := κ ∘ normalFamilyArgument) hc)

/-- Exact scalar factorization of the original G-adic family in normal coordinates. -/
theorem originalFamily_eq_power_mul_divided
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (κ : ComplexPlane → ComplexPlane)
    (z : ℂ × ComplexPlane)
    (hG : planePolynomialEval G (κ (normalFamilyArgument z)) = z.1 * z.2.2) :
    (∑ α ∈ I, z.1 ^ α * planePolynomialEval G (κ (normalFamilyArgument z)) ^ j α *
      planePolynomialEval (R α) (κ (normalFamilyArgument z))) =
      z.1 ^ u * dividedAnalyticFamily I j R u κ z := by
  classical
  unfold dividedAnalyticFamily
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hw : u + (α + j α - u) = α + j α := Nat.add_sub_of_le (hmin α hα)
  rw [hG, mul_pow]
  simp only [← mul_assoc, ← pow_add, hw]

/-- The actual central value is the initial normal polynomial with the
remainder polynomials restricted through the chart at normal coordinate zero. -/
theorem dividedAnalyticFamily_zero
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (κ : ComplexPlane → ComplexPlane) (q : ComplexPlane) :
    dividedAnalyticFamily I j R u κ (0, q) =
      ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (κ (q.1, 0)) := by
  classical
  unfold dividedAnalyticFamily
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases heq : α + j α = u
  · simp [heq, normalFamilyArgument]
  · have hpos : 0 < α + j α - u := Nat.sub_pos_of_lt
      (lt_of_le_of_ne (hmin α hα) (Ne.symm heq))
    simp [heq, zero_pow (Nat.ne_of_gt hpos)]

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology

/-- The actual divided normal coordinate, extended at zero by the derivative. -/
def dividedNormalCoordinate (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) : ℂ → ℂ :=
  Function.update (fun s : ℂ => s⁻¹ * G (p + s • V)) 0 (L V)

/-- Actual center in the rescaled normal chart for an affine moving point. -/
def dividedNormalCenter (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) (s : ℂ) : ComplexPlane :=
  ((p + s • V).1, dividedNormalCoordinate G L p V s)

theorem dividedNormalCenter_zero (G : ComplexPlane → ℂ)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane) :
    dividedNormalCenter G L p V 0 = (p.1, L V) := by
  simp [dividedNormalCenter, dividedNormalCoordinate]

theorem dividedNormalCenter_continuousAt
    (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    ContinuousAt (dividedNormalCenter G L p V) 0 := by
  have hn : ContinuousAt (dividedNormalCoordinate G L p V) 0 :=
    continuousAt_update_same.mpr (normal_equation_affine_velocity_limit G L p V hG hp)
  exact ((continuous_const.add (continuous_id.smul continuous_const)).fst.continuousAt).prodMk hn

/-- Away from zero the rescaled divided center is exactly the actual normal
chart image of the moving affine point. -/
theorem scale_dividedNormalCenter
    (G : MvPolynomial (Fin 2) ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) (s : ℂ) (hs : s ≠ 0) :
    analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s) =
      polynomialNormalCoordinates G (p + s • V) := by
  ext <;> simp [analyticNormalScale, dividedNormalCenter, dividedNormalCoordinate,
    polynomialNormalCoordinates, hs]

/-- The actual moving point is recovered by the inverse chart at the divided
normal center, wherever that moving point lies in the chart source. -/
theorem inverse_at_dividedNormalCenter
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane) (s : ℂ) (hs : s ≠ 0)
    (hsource : p + s • V ∈ e.source) :
    e.symm (analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s)) =
      p + s • V := by
  rw [scale_dividedNormalCenter G L p V s hs, ← he]
  exact e.left_inv hsource

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology

/-- Actual affine motions remain inside the chosen normal chart near zero,
and their rescaled center lies in the inverse chart's analytic neighborhood. -/
theorem eventually_divided_center_chart_conditions
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hp : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p)) :
    ∀ᶠ s : ℂ in 𝓝 0, s ≠ 0 →
      p + s • V ∈ e.source ∧
      analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s) ∈ e.target ∧
      AnalyticAt ℂ e.symm
        (analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s)) := by
  have hm : ContinuousAt (fun s : ℂ => p + s • V) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hs : ∀ᶠ s : ℂ in 𝓝 0, p + s • V ∈ e.source := by
    apply hm.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using e.open_source.mem_nhds hp
  have hec : ContinuousAt e p := e.continuousAt hp
  have hm' : ContinuousAt (fun s : ℂ => e (p + s • V)) 0 := by
    have hh : ContinuousAt e (p + (0 : ℂ) • V) := by simpa using hec
    exact hh.comp (f := fun s : ℂ => p + s • V) hm
  have hinv : ∀ᶠ s : ℂ in 𝓝 0, AnalyticAt ℂ e.symm (e (p + s • V)) := by
    have hlocal : ∀ᶠ y in 𝓝 (e (p + (0 : ℂ) • V)), AnalyticAt ℂ e.symm y := by
      simpa only [zero_smul, add_zero] using hi.eventually_analyticAt
    exact hm'.tendsto.eventually hlocal
  filter_upwards [hs, hinv] with s hs hi hs0
  refine ⟨hs, ?_, ?_⟩
  · rw [scale_dividedNormalCenter G L p V s hs0, ← he]
    exact e.map_source hs
  · rwa [scale_dividedNormalCenter G L p V s hs0, ← he]

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- The actual polynomial in the original affine plane at fixed parameter s,
with its finite G-adic coefficient decomposition made explicit. -/
def factoredPlaneFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ α ∈ I, MvPolynomial.C (s ^ α) * (G ^ j α * R α)

theorem eval_factoredPlaneFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) (p : ComplexPlane) :
    planePolynomialEval (factoredPlaneFamily I j R G s) p =
      ∑ α ∈ I, s ^ α * planePolynomialEval G p ^ j α * planePolynomialEval (R α) p := by
  simp [factoredPlaneFamily, planePolynomialEval, mul_assoc]

/-- Actual polynomial multiplicity of the moving plane curve transfers to the
divided holomorphic family for every nonzero parameter. All chart conditions
are local statements about the actual inverse map at the actual point. -/
theorem factored_family_order_implies_divided_order
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (s : ℂ) (hs : s ≠ 0) (q : ComplexPlane) (m : ℕ)
    (htarget : analyticNormalScale s q ∈ e.target)
    (hei : AnalyticAt ℂ e.symm (analyticNormalScale s q))
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s q)).1
        else (e.symm (analyticNormalScale s q)).2)
      m (factoredPlaneFamily I j R G s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x => dividedAnalyticFamily I j R u e.symm (s, x)) q m := by
  have h := polynomial_order_in_rescaled_inverse_chart
    (factoredPlaneFamily I j R G s) e s q m hei hP
  apply (Nagata.Workers.W17.analytic_order_const_mul_iff
    (fun x => dividedAnalyticFamily I j R u e.symm (s, x)) q m
    (s ^ u) (pow_ne_zero _ hs)).mp
  apply h.congr
  have ht : ∀ᶠ x in 𝓝 q, analyticNormalScale s x ∈ e.target :=
    (analyticNormalScale_analyticAt s q).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
  exact ht.mono fun x hx => by
    change planePolynomialEval (factoredPlaneFamily I j R G s)
      (e.symm (analyticNormalScale s x)) = _
    rw [eval_factoredPlaneFamily]
    apply originalFamily_eq_power_mul_divided I j R u hmin G e.symm (s, x)
    exact rescaled_inverse_normal_chart_equation G e he s x hx

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- Local normal specialization for an actual finite polynomial family.
The hypotheses assert its original ordinary ideal-power multiplicities along
an affine motion. The conclusion asserts genuine central derivative jets;
no analytic jet hypothesis or derivative-continuity assumption is supplied. -/
theorem normal_specialization_central_jets
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hsource : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p))
    (hG : HasFDerivAt (planePolynomialEval G) L p)
    (hp : planePolynomialEval G p = 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (factoredPlaneFamily I j R G s)) :
    ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane =>
        ∑ α ∈ I.filter (fun α => α + j α = u),
          q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
      (p.1, L V) = 0 := by
  classical
  let center := dividedNormalCenter (planePolynomialEval G) L p V
  let family : ℂ → ComplexPlane → ℂ := fun s q => dividedAnalyticFamily I j R u e.symm (s, q)
  have hc : ContinuousAt center 0 := dividedNormalCenter_continuousAt _ L p V hG hp
  have hc0 : center 0 = (p.1, L V) := dividedNormalCenter_zero _ L p V
  have harg : normalFamilyArgument (0, center 0) = e p := by
    rw [hc0, he]
    simp [normalFamilyArgument, polynomialNormalCoordinates, hp]
  have hf : AnalyticAt ℂ (Function.uncurry family) (0, center 0) := by
    apply dividedAnalyticFamily_analyticAt
    rwa [harg]
  have hchart := eventually_divided_center_chart_conditions G e he L p V hsource hi
  have hjets : ∀ᶠ s : ℂ in 𝓝 0, s ∉ insert 0 exceptional → ∀ n < m,
      iteratedFDeriv ℂ n (family s) (center s) = 0 := by
    filter_upwards [hchart, horders] with s hs ho hex
    have hs0 : s ≠ 0 := fun hz => hex (hz ▸ Finset.mem_insert_self _ _)
    have hexc : s ∉ exceptional := fun h => hex (Finset.mem_insert_of_mem h)
    obtain ⟨hsour, htar, hainv⟩ := hs hs0
    have hpoint := inverse_at_dividedNormalCenter G e he L p V s hs0 hsour
    have hord : Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s (center s))).1
          else (e.symm (analyticNormalScale s (center s))).2)
        m (factoredPlaneFamily I j R G s) := by
      simpa only [center, hpoint] using ho hexc
    obtain ⟨P, hP, hz⟩ := factored_family_order_implies_divided_order
      I j R u hmin G e he s hs0 (center s) m htar hainv hord
    exact Nagata.W19.total_taylor_vanishing_of_powerSeries hP m hz
  have hlim := Nagata.Workers.W17.analytic_local_cofinite_moving_derivative_jets
    family center 0 (insert 0 exceptional) m hf hc hjets
  intro n hn
  have hh := hlim n hn
  simp only [family, hc0] at hh
  simpa only [dividedAnalyticFamily_zero I j R u hmin] using hh

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators

/-- A genuine local graph on G=0 is the zero-normal slice of the constructed
normal chart, by its actual local inverse identity. -/
theorem inverse_normal_chart_eq_graph_locally
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0) :
    ∀ᶠ z in 𝓝 ξ, e.symm (z, 0) = (z, b z) := by
  have hc : ContinuousAt (fun z => (z, b z)) ξ := continuousAt_id.prodMk hb
  have hs : ∀ᶠ z in 𝓝 ξ, (z, b z) ∈ e.source :=
    hc.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hs, hG] with z hz hg
  have hh := e.left_inv hz
  simpa only [he, polynomialNormalCoordinates, hg] using hh

/-- The actual central expression in inverse normal coordinates agrees as a
local function germ with the expression restricted to an actual graph on G=0. -/
theorem central_expression_eq_graph_locally
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ c : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0) :
    (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
      q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0))) =ᶠ[𝓝 (ξ, c)]
    (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
      q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) := by
  have hgraph := inverse_normal_chart_eq_graph_locally G e he b ξ hb hsource hG
  have hc : ContinuousAt (Prod.fst : ComplexPlane → ℂ) (ξ, c) := continuousAt_fst
  have hh := hc.tendsto.eventually hgraph
  exact hh.mono fun q hq => by simp only [hq]

end Nagata.Workers.W28

end
end

end OAI
