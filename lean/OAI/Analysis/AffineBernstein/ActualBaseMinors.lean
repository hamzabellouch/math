import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeArea
import OAI.Analysis.AffineBernstein.HessianMinors

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- A bounded convex function on a full larger ball has bounded actual
Euclidean gradient at its center. No derivative estimate is assumed. -/
lemma norm_gradient_le_of_convex_bounded {Ω : Set E} {f : E → ℝ}
    (hc : ConvexOn ℝ Ω f) {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ f x)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : Metric.closedBall x r ⊆ Ω) (hb : ∀ y ∈ Ω, |f y| ≤ M) :
    ‖gradient f x‖ ≤ 2*M/r := by
  by_cases hg : gradient f x = 0
  · simp only [hg,norm_zero]
    positivity
  have hgp : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  let y := x + (r/‖gradient f x‖) • gradient f x
  have hdist : dist y x = r := by
    rw [dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hgp),
      div_mul_cancel₀ _ hgp.ne']
  have hy : y ∈ Ω := hball (by rw [Metric.mem_closedBall,hdist])
  have hs := convex_fderiv_support hc hx hy hd
  have he : fderiv ℝ f x (y-x) = r*‖gradient f x‖ := by
    dsimp [y]
    rw [add_sub_cancel_left,map_smul,smul_eq_mul,← inner_gradient_left,
      real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hs
  have hfx := (abs_le.mp (hb x hx)).1
  have hfy := (abs_le.mp (hb y hy)).2
  apply (le_div_iff₀ hr).mpr
  nlinarith

end ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

lemma hessian_neg {k : ℕ} (f : Space k → ℝ) (x : Space k) :
    hessian (fun y => -f y) x = -hessian f x := by
  ext i j
  simp only [hessian,fderiv_fun_neg,neg_apply,Matrix.neg_apply]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma tubeBaseMatrix_basisFun {k : ℕ} {H : Space k × E → ℝ}
    {s : Space k} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e)) :
    tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis =
      hessian (fun x => -H (x,e)) s := by
  have hh : ContDiffAt ℝ ∞ (fun x => H (x,e)) s :=
    hH.comp s (contDiffAt_id.prodMk contDiffAt_const)
  rw [hessian_neg]
  ext i j
  simp only [tubeBaseMatrix,Matrix.of_apply,Matrix.neg_apply]
  rw [hessian_eq_second hh,second_fderiv_prod_left hH]
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,coordinateVector]

/- The uniform large-principal-minor bound for the actual negative support
of an affine epigraph. The larger base domain supplies the gradient bound;
hence no derivative or determinant bound is added as a hypothesis. -/
theorem affineEpigraph_base_minors_bound {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : e ≠ 0) {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D,
      |homogeneousSupport {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e| ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × E =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun s => tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ s in Q, ENNReal.ofReal ((B s).det * (1 + (B s)⁻¹.trace))) ≤
      ((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R)) := by
  let H := fun q : Space k × E =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let f : Space k → ℝ := fun s => -H (s,e)
  have hh (s : Space k) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  have hf (s : Space k) (hs : s ∈ D) : ContDiffAt ℝ ∞ f s :=
    ((hh s hs).comp s (contDiffAt_id.prodMk contDiffAt_const)).neg
  have hpf (s : Space k) (hs : s ∈ D) : (hessian f s).PosDef := by
    rw [← tubeBaseMatrix_basisFun (hh s hs)]
    apply tubeBaseMatrix_posDef (hh s hs)
    intro v hv
    rw [← second_fderiv_prod_left (hh s hs)]
    exact affineEpigraph_base_hessian_negative hΩ hcv hu hp a L hD hK hzero hs he hv
  have hfD : ContDiffOn ℝ ∞ f D := fun s hs => (hf s hs).contDiffWithinAt
  have hcf := convexOn_of_hessian_posSemidef hD hcD hfD (fun s hs => (hpf s hs).posSemidef)
  have hg (s : Space k) (hs : s ∈ Q) : ‖gradient f s‖ ≤ 2*M/r := by
    apply norm_gradient_le_of_convex_bounded hcf (hQD hs)
      ((hf s (hQD hs)).differentiableAt (by simp)) hr hM (hball s hs)
    intro x hx
    simpa only [f,abs_neg] using hbound x hx
  have hb := lintegral_hessian_minors_le_ball hcD hf hpf hQ hQD hg hR
  change (∫⁻ s in Q, ENNReal.ofReal
    ((tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det *
      (1+(tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.trace))) ≤ _
  convert hb using 1
  apply setLIntegral_congr_fun hQ
  intro s hs
  dsimp only
  rw [tubeBaseMatrix_basisFun (hh s (hQD hs))]

/- A compact fiber radius controls the literal support function in all unit
normal directions. -/
omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma homogeneousSupport_abs_le_of_radius {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (he : ‖e‖ = 1) {M : ℝ}
    (hM : ∀ y ∈ K, ‖y‖ ≤ M) : |homogeneousSupport K e| ≤ M := by
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hy hmax]
  exact (abs_real_inner_le_norm e y).trans (by simpa only [he,one_mul] using hM y hy)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma homogeneousSupport_ge_of_ball {K : Set E} (hK : IsCompact K)
    {e : E} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0:E) r ⊆ K) : r ≤ homogeneousSupport K e := by
  have hmem : r • e ∈ K := hball (by
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hr,he,mul_one,le_refl])
  have hi := homogeneousSupport_le hK hmem e
  simpa only [inner_smul_right,real_inner_self_eq_norm_sq,he,one_pow,mul_one] using hi

/- Fully geometric formulation of the actual large-minor estimate: only the
fibers' position in a fixed ball and a base collar are needed. -/
theorem affineEpigraph_base_minors_of_fiber_radius {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : ‖e‖ = 1) {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × E =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun s => tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ s in Q, ENNReal.ofReal ((B s).det * (1 + (B s)⁻¹.trace))) ≤
      ((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R)) := by
  have he0 : e ≠ 0 := fun h => by simp [h] at he
  apply affineEpigraph_base_minors_bound hΩ hcv hu hp a L hD hcD hK hzero he0 hQ hQD hr hM hball
  · intro s hs
    exact homogeneousSupport_abs_le_of_radius (hK s hs)
      ⟨0,interior_subset (hzero s hs)⟩ he (hbound s hs)
  · exact hR

end AffineBernstein
end

end OAI
