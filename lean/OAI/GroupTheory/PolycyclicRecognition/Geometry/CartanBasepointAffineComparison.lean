import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallLeftShift
import OAI.GroupTheory.PolycyclicRecognition.Analysis.DominatedAffineLabels

namespace OAI

/-! # Finite-label comparison for the actual changed Cartan profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module MeasureTheory Filter Metric Set
open scoped Manifold Topology ENNReal

variable {EG G W I L : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [DecidableEq I] [Fintype L] [Nonempty L]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]

omit [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier] [Fintype L] [Nonempty L] [FiniteDimensional ℝ W] in
/-- Continuity in the nilpotent sample, including restriction to any compact
chart. This supplies all measurable bad sets below. -/
theorem continuous_realScaleProfile_restrict
    (hD : Continuous F.ExpD) (J : G → W) (hJ : Continuous J) (x : G)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (r : ℝ) (Z : Set (Fin (finrank ℝ H) → ℝ)) :
    Continuous (fun k => (F.realScaleProfile hD J hJ x X S β r k).restrict Z) :=
  (ContinuousMap.continuous_restrict Z).comp
    ((continuous_rescaledContinuousProfile J hJ x (max (Real.log r) 0)
      (F.profileChart (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)))
      (F.continuous_profileChart hD _)).comp F.closedN.continuous)

omit [FiniteDimensional ℝ W] [IsTopologicalGroup F.N.carrier] in
/-- The actual chart and group identities turn affine concentration into
agreement of finite labels and a sublinear center-height error. The sampling
and concentration assumptions are supplied by the preceding proved bridges. -/
theorem basepoint_affine_labels_of_sampling
    (hD : Continuous F.ExpD)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (π : G →* Multiplicative W) (height : H →ₗ[ℝ] W)
    (hheight : Function.Surjective height)
    (hchartheight : ∀ v, (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v)
    (hkill : ∀ u v : H, height ⁅u, v⁆ = 0)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    (X : I → H) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {R R' t : ℝ} (hR : 0 < R) (hR' : 0 < R') (ht : 0 < t)
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (htr : ∀ᶠ n in atTop, 1 ≤ t * r n)
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x y : ℕ → G)
    (u : ℕ → F.N.carrier) (k : ℕ → F.D.carrier)
    (hfactor : ∀ᶠ n in atTop, y n = x n * (F.inclusionN (u n) * F.inclusionD (k n)))
    (hkheight : ∀ᶠ n in atTop,
      (π (F.inclusionD (k n))).toAdd = (π ((x n)⁻¹ * y n)).toAdd)
    (φ : ℕ → C(closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
      closedBall (0 : Fin (finrank ℝ H) → ℝ) R'))
    (hφ : ∀ᶠ n in atTop, ∀ z,
      (φ n z : Fin (finrank ℝ H) → ℝ) = wordChartLeftShift F.D.equiv chartD
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (r n)))
        (exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log (t * r n)))
        (k n) z)
    (ξ μ ν : ℕ → ProbabilityMeasure F.N.carrier) {D : ℝ≥0∞} (hDfinite : D ≠ ∞)
    (hdom : ∀ᶠ n in atTop, ∀ U : Set F.N.carrier, MeasurableSet U →
      (ξ n : Measure F.N.carrier) ((fun a => F.action (k n)⁻¹ ((u n)⁻¹ * a)) ⁻¹' U) ≤
        D * (μ n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
          {p | p.1 * p.2 ∈ U})
    (a a' : ℕ → L) (b b' : ℕ → W)
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0)) :
    let q := (height.comp (WordBasisSelections.basis X S β).equivFun.symm.toLinearMap).toContinuousLinearMap
    let raw := fun n z => F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z
    let raw' := fun n z => F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n) z
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ξ n : Measure F.N.carrier)
      {z | ε ≤ dist (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
        ((raw n z).restrict (closedBall 0 R))}) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n : Measure F.N.carrier)
      {z | ε ≤ dist ((raw' n z).restrict (closedBall 0 R'))
        (linearBallProfile q (A (a' n)) R' + ContinuousMap.const _ (b' n))}) atTop (𝓝 0)) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure F.N.carrier).prod (ν n : Measure F.N.carrier)
      {p | ε ≤ dist ((raw' n (p.1 * p.2)).restrict (closedBall 0 R'))
        ((raw' n p.1).restrict (closedBall 0 R'))}) atTop (𝓝 0)) →
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => (r n)⁻¹ • (J n (y n) - J n (x n) -
        A (a' n) ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  dsimp only
  intro hsource hord hsuffix
  let bD := WordBasisSelections.basis X S β
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let c := fun n => (r n)⁻¹ • (J n (y n) - J n (x n))
  let v := fun n => (r n)⁻¹ • (π ((x n)⁻¹ * y n)).toAdd
  let f := fun n z => (F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z).restrict (closedBall 0 R)
  let g := fun n z => (F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n) z).restrict (closedBall 0 R')
  have hq : Function.Surjective q := hheight.comp bD.equivFun.symm.surjective
  have hnormalized : ∀ n, (t * r n) / r n = t := fun n =>
    mul_div_cancel_right₀ t (ne_of_gt (zero_lt_one.trans_le (hr n)))
  have hheight' : ∀ᶠ n in atTop, ∀ z, t • q (φ n z) = q z - v n := by
    filter_upwards [hφ, htr, hkheight] with n hn htn hk z
    change t • height (bD.equivFun.symm (φ n z)) =
      height (bD.equivFun.symm z) - (r n)⁻¹ • (π ((x n)⁻¹ * y n)).toAdd
    have hh := wordChartLeftShift_normalized_height F.D.equiv chartD
      (π.comp F.inclusionD) height hchartheight hkill X S β
      (zero_lt_one.trans_le (hr n)) (zero_lt_one.trans_le htn) (k n) z
    simpa only [hnormalized, ← hn z, MonoidHom.comp_apply, hk, q, bD, v,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply] using hh
  have hmatch : ∀ᶠ n in atTop, ∀ z,
      f n z = transportCompactProfile t (φ n) (c n)
        (g n (F.action (k n)⁻¹ ((u n)⁻¹ * z))) := by
    filter_upwards [hφ, hfactor, htr] with n hn hy htn z
    ext w
    change F.realScaleProfile hD (J n) (hJ n) (x n) X S β (r n) z w =
      t • F.realScaleProfile hD (J n) (hJ n) (y n) X S β (t * r n)
        (F.action (k n)⁻¹ ((u n)⁻¹ * z)) (φ n w) + c n
    have hh := F.realScaleProfile_basepoint_change chartD hchartD hD (J n) (hJ n)
      (x n) (u n) z (k n) X S β (hr n) htn w
    dsimp only at hh
    rw [← hy, ← hn w] at hh
    have he := congrArg (fun z : W => (r n)⁻¹ • z) hh
    have hs : (r n)⁻¹ * (t * r n) = t := by
      rw [mul_comm, ← div_eq_mul_inv, hnormalized]
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le (hr n))),
      one_smul, hs] using he
  have hmeas n ε : MeasurableSet {z | ε ≤ dist (g n z)
      (linearBallProfile q (A (a' n)) R' + ContinuousMap.const _ (b' n))} := by
    exact (isClosed_Ici.preimage ((F.continuous_realScaleProfile_restrict hD (J n)
      (hJ n) (y n) X S β (t * r n) (closedBall 0 R')).dist continuous_const)).measurableSet
  obtain ⟨heq, herr⟩ := affine_labels_center_error_of_dominated_transport q hq A hA hR hR'
    ξ μ ν a a' b b' c v ht φ (fun n z => F.action (k n)⁻¹ ((u n)⁻¹ * z))
    (fun _ z z' => z * z') f g hheight' hmatch hDfinite hmeas hdom hsource hord hsuffix hb hb'
  refine ⟨heq, ?_⟩
  simpa only [c, v, map_smul, ← smul_sub] using herr

end PolycyclicRecognition.CartanFactorModel

end

end OAI
