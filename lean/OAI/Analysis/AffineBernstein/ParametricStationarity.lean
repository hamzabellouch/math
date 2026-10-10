import Mathlib
import OAI.Analysis.AffineBernstein.ParametricFirstVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Every compact smooth parametric velocity has a genuinely smooth compact
normal graph component, without extending the original graph smoothly. -/
lemma normalVariation_compact {n : ℕ} {Ω K : Set (Space n)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {u β : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    ContDiff ℝ ∞ (normalVariation u β a) ∧
      HasCompactSupport (normalVariation u β a) ∧ tsupport (normalVariation u β a) ⊆ K := by
  have hg (k : Fin n) : ContDiff ℝ ∞
      (fun y => dirDeriv (coordinateVector n k) u y * a k y) :=
    contDiff_mul_at_tsupport (ha k) (fun x hx =>
      contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds (hKΩ (haK k hx)))) _)
  have hs : tsupport (normalVariation u β a) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxn
    have hb : β x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxn (hβK h))
    have ha0 (k : Fin n) : a k x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxn (haK k h))
    exact hx (by simp [normalVariation, hb, ha0])
  exact ⟨hβ.sub (ContDiff.sum (fun k _ => hg k)),
    hK.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

/- The exact pointwise first variation under every compact smooth parametric
velocity is integrable and has zero integral. The density uses the actual
varying conormal and horizontal Jacobian. -/
theorem affineMaximal_parametric_first_variation {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    IntegrableOn (fun x => deriv (graphVariationArea u β a x) 0) Ω ∧
      (∫ x in Ω, deriv (graphVariationArea u β a x) 0) = 0 := by
  let η := normalVariation u β a
  have hn := normalVariation_compact hΩ hK hKΩ hu hβ hβK ha haK
  have heβ : verticalVariation u η a = β := by
    funext x
    simp [verticalVariation, η, normalVariation]
  let N := fun x => (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j))
  let F (k : Fin n) (x : Space n) := affineAreaDensity u x * a k x
  let D (k : Fin n) := dirDeriv (coordinateVector n k) (F k)
  have hF (k : Fin n) : ContDiff ℝ ∞ (F k) :=
    contDiff_mul_at_tsupport (ha k) (fun x hx =>
      contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ (haK k hx))))
        (hp x (hKΩ (haK k hx))))
  have hFs (k : Fin n) : tsupport (F k) ⊆ K := tsupport_mul_subset_right.trans (haK k)
  have hFc (k : Fin n) : HasCompactSupport (F k) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hFs k)
  have hD (k : Fin n) : Integrable (D k) :=
    integrable_of_support_subset_compact (hFc k).isCompact
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _))
      (contDiff_dirDeriv (hF k) _).continuous.continuousOn
  have hD0 (k : Fin n) : (∫ x in Ω, D k x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_dirDeriv_compact _ (hF k) (hFc k) _
    · intro x hx
      change fderiv ℝ (F k) x (coordinateVector n k) = 0
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hKΩ (hFs k h)))]
      rfl
  have hN : IntegrableOn N Ω :=
    (integrableOn_area_variation hΩ hu hp η hn.1 hn.2.1 (hn.2.2.trans hKΩ)).const_mul _
  have hN0 : (∫ x in Ω, N x) = 0 := by
    rw [show N = fun x => (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) from rfl, integral_const_mul,
      affineMaximal_area_stationarity hΩ hu hp hm η hn.1 hn.2.1 (hn.2.2.trans hKΩ), mul_zero]
  have hDs : IntegrableOn (fun x => ∑ k, D k x) Ω :=
    (integrable_finsetSum _ (fun k _ => hD k)).integrableOn
  have he (x : Space n) (hx : x ∈ Ω) :
      deriv (graphVariationArea u β a x) 0 = N x + ∑ k, D k x := by
    have hh := hasDerivAt_graphVariationArea_normal hΩ hu hn.1.contDiffOn
      (fun k => (ha k).contDiffOn) hx (hp x hx)
    rw [heβ] at hh
    simpa only [N, F, D, mul_assoc] using hh.deriv
  refine ⟨(hN.add hDs).congr_fun (fun x hx => (he x hx).symm) hΩ.measurableSet, ?_⟩
  rw [setIntegral_congr_fun hΩ.measurableSet he, integral_add hN hDs, hN0,
    integral_finsetSum _ (fun k _ => (hD k).integrableOn)]
  simp only [hD0, Finset.sum_const_zero, add_zero]

end AffineBernstein
end

end OAI
