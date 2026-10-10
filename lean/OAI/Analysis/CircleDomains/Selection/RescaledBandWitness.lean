import OAI.Analysis.CircleDomains.Sobolev.AffineSobolevWitness
import OAI.Analysis.CircleDomains.Sobolev.RescaledScalarBump
import OAI.Analysis.CircleDomains.Sobolev.ScalarCutoffEnergy

namespace OAI

/-! At graph scale s the domain and value rescalings cancel in the
chain-rule term. The remaining gradient is the original physical one. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def rescaledBandWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C) :
    DeGiorgi.MemW1pWitness 2
      (fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)) univ :=
  smoothScalarCutoffWitness
    (hu.comp (planarAffineHomeomorph a s hs.ne').continuous)
    (affineSobolevWitness W a hs)
    (hsu.comp_homeomorph (planarAffineHomeomorph a s hs.ne'))
    (rescaledScalarBump_contDiff t s) (rescaledScalarBump_unit t s)
    (rescaledScalarBump_deriv_bound hC t hs)
    spatialCapacityBump.contDiff spatialCapacityBump.hasCompactSupport

lemma rescaledBandWitness_gradient {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (x : EuclideanPlane) (i : Fin 2) :
    (rescaledBandWitness hu W hsu a t hs hC).weakGrad x i =
      spatialCapacityBump x *
        (deriv scalarCapacityBump ((u (a+s • x)-t)/s) * W.weakGrad (a+s • x) i) +
      fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1) *
        scalarCapacityBump ((u (a+s • x)-t)/s) := by
  change spatialCapacityBump x *
      (deriv (rescaledScalarBump t s) (u (a+s • x)) * (s • W.weakGrad (a+s • x)) i) +
      fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1) *
        rescaledScalarBump t s (u (a+s • x)) = _
  rw [rescaledScalarBump_deriv, PiLp.smul_apply, smul_eq_mul]
  dsimp only [rescaledScalarBump]
  field_simp [hs.ne']

lemma rescaledBandWitness_one {u : EuclideanPlane → ℝ}
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s) {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ Metric.closedBall 0 1)
    (hu : |u (a+s • x)-t| ≤ s) :
    spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s) = 1 := by
  rw [spatialCapacityBump_one hx]
  exact one_mul _ |>.trans (rescaledScalarBump_one t hs hu)

lemma rescaledBandWitness_zero {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C) {x : EuclideanPlane}
    (hx : 4 < ‖x‖ ∨ 2*s < |u (a+s • x)-t|) :
    spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s) = 0 ∧
      (rescaledBandWitness hu W hsu a t hs hC).weakGrad x = 0 := by
  rcases hx with hx | hx
  · obtain ⟨hz,hd⟩ := spatialCapacityBump_zero hx
    refine ⟨by rw [hz,zero_mul],?_⟩
    ext i
    simp only [rescaledBandWitness_gradient, hz, hd, zero_apply,
      zero_mul, add_zero, PiLp.zero_apply]
  · have hlarge : 2 < |(u (a+s • x)-t)/s| := by
      rw [abs_div, abs_of_pos hs]
      exact (lt_div_iff₀ hs).mpr hx
    obtain ⟨hz,hd⟩ := scalarCapacityBump_zero hlarge
    refine ⟨by rw [hz,mul_zero],?_⟩
    ext i
    simp only [rescaledBandWitness_gradient, hz, hd, mul_zero, zero_mul,
      add_zero, PiLp.zero_apply]

lemma rescaledBandWitness_energy {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) (x : EuclideanPlane) :
    let Q := rescaledBandWitness hu W hsu a t hs hC
    (spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s))^2 +
      (|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2 ≤
      ({y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}).indicator
        (fun y => (1+8*C^2)*(1+(|W.weakGrad (a+s • y) 0|+|W.weakGrad (a+s • y) 1|)^2)) x := by
  dsimp only
  by_cases hx : x ∈ {y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}
  · rw [indicator_of_mem hx]
    rw [rescaledBandWitness_gradient, rescaledBandWitness_gradient]
    have hd (i : Fin 2) : |fderiv ℝ spatialCapacityBump x (EuclideanSpace.single i 1)| ≤ C := by
      have he := (fderiv ℝ spatialCapacityBump x).le_opNorm (EuclideanSpace.single i 1)
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
        using he.trans (mul_le_mul_of_nonneg_right (hηd x) (norm_nonneg _))
    apply scalar_cutoff_energy_algebra hC0
    · exact abs_le.mpr ⟨by linarith [spatialCapacityBump.nonneg (x := x)],
        spatialCapacityBump.le_one⟩
    · exact abs_le.mpr ⟨by linarith [scalarCapacityBump.nonneg (x := (u (a+s • x)-t)/s)],
        scalarCapacityBump.le_one⟩
    · exact hC _
    · exact hd 0
    · exact hd 1
  · rw [indicator_of_notMem hx]
    have hh : 4 < ‖x‖ ∨ 2*s < |u (a+s • x)-t| := by
      simpa only [mem_ofPred_eq, not_and_or, not_le] using hx
    obtain ⟨hz,hg⟩ := rescaledBandWitness_zero hu W hsu a t hs hC hh
    simp only [hz, hg, PiLp.zero_apply, abs_zero, zero_add, zero_pow (by decide : 2 ≠ 0), le_rfl]

end CircleDomainRigidity

end

end OAI
