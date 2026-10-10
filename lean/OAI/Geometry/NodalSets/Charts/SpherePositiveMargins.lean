import OAI.Geometry.NodalSets.Charts.RoundCotangentTensor
import OAI.Geometry.NodalSets.Elliptic.AmbientMatrixForm
import OAI.Geometry.NodalSets.Elliptic.IntrinsicAmbientSmooth
import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma intrinsic_sphere_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c > 0, ∀ x v, c*roundCotangentTensor x v v ≤ A x v v := by
  let B := fun x ↦ ambientMatrixForm (intrinsicAmbientMatrix A x)
  have hB : Continuous B := (ambientMatrixForm_smooth _ (intrinsicAmbientMatrix_smooth A hA)).continuous
  have hpos (x : Base) (v : AmbientBase) (hv : v ≠ 0) : 0 < B x v v :=
    ambientMatrixForm_pos _ (intrinsicAmbientMatrix_posDef A hs hp x) v hv
  have hc : Continuous (fun z : Base × AmbientBase ↦ B z.1 z.2 z.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:AmbientBase) 1)) _ hc.continuousOn
    (fun z hz ↦ hpos z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hb (x : Base) (v : AmbientBase) : c*‖v‖^2 ≤ B x v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (x,(‖v‖⁻¹:ℝ) • v)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
    have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*B x v v)) = B x v v := by field_simp
    rw [he] at hmul
    nlinarith
  refine ⟨c,hc0,?_⟩
  intro x v
  have hh := hb x (sphereCotangentRepresentative x v)
  rw [show B x = ambientMatrixForm (intrinsicAmbientMatrix A x) from rfl,
    intrinsicAmbientMatrix_pairing,sphereCotangentRepresentative_restriction,
    sphereCotangentRepresentative_orthogonal,zero_mul,add_zero] at hh
  simpa only [roundCotangentTensor_apply,real_inner_self_eq_norm_sq] using hh

lemma intrinsic_pair_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, (∀ x v, c*roundCotangentTensor x v v ≤ A x v v) ∧ ∀ x, c ≤ rho x := by
  obtain ⟨a,ha,hb⟩ := intrinsic_sphere_positive_margin A hA hs hp
  obtain ⟨r,hr0,_,_,hrb⟩ := compact_positive_bounds isCompact_univ rho hr.continuous.continuousOn
    (fun x _ ↦ hrp x)
  refine ⟨min a r,lt_min ha hr0,?_,fun x ↦ (min_le_right _ _).trans (hrb x (mem_univ _)).1⟩
  intro x v
  have hn : 0 ≤ roundCotangentTensor x v v := by
    rw [roundCotangentTensor_apply]; exact real_inner_self_nonneg
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hn).trans (hb x v)

end
end Yau.Target

end OAI
