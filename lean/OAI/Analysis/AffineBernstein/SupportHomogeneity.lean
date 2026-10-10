import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates
import OAI.Analysis.AffineBernstein.TubeDensityVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_smul {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (e : E) {c : ℝ} (hc : 0 < c) :
    homogeneousSupport K (c • e) = c * homogeneousSupport K e := by
  obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hz hm]
  have hmc : IsMaxOn (fun y => inner ℝ (c • e) y) K z := by
    intro y hy
    change inner ℝ (c • e) y ≤ inner ℝ (c • e) z
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (hm hy) hc.le
  rw [homogeneousSupport_eq_of_max hz hmc,real_inner_smul_left]

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

def normalScale (c : ℝ) : S × E →L[ℝ] S × E :=
  (ContinuousLinearMap.id ℝ S).prodMap (c • ContinuousLinearMap.id ℝ E)

omit [CompleteSpace E] in
@[simp] lemma normalScale_apply (c : ℝ) (q : S × E) :
    normalScale c q = (q.1,c • q.2) := rfl

omit [CompleteSpace E] in
lemma second_fderiv_const_mul {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (c : ℝ) (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q => c * H q)) x v w =
      c * fderiv ℝ (fderiv ℝ H) x v w := by
  have hh : (fun q => c * H q) = (c • ContinuousLinearMap.id ℝ ℝ) ∘ H := by
    ext q
    simp
  rw [hh]
  simpa [Function.comp_def] using second_fderiv_clm_comp
    (c • ContinuousLinearMap.id ℝ ℝ) hH v w

lemma homogeneous_fiber_hessian_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2))
      (s,c • e) (normalScale c v) (normalScale c w) =
    c * fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2)) (s,e) v w := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have he : (fun q => H (normalScale c q)) =ᶠ[𝓝 (s,e)] (fun q => c * H q) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hD.mem_nhds hs)] with q hq
    exact homogeneousSupport_smul (hK _ hq) (hne _ hq) q.2 hc
  have hh := congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ => A v w)
    ((he.fderiv (𝕜 := ℝ)).fderiv_eq)
  rw [second_fderiv_const_mul hH] at hh
  have hj := second_fderiv_affine_comp (normalScale (S := S) c) (0 : S × E)
    (x := (s,e)) (by simpa using hHc) v w
  simp only [zero_add] at hj
  exact hj.symm.trans hh

end AffineBernstein
end

end OAI
