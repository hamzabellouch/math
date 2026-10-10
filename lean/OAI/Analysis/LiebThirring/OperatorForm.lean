import OAI.Analysis.LiebThirring.CoerciveInverse

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

lemma weightedL_inner {W : ℝ → ℝ} (d : PotentialData W) (u v : H1C) :
    inner ℂ (weightedL d u) (weightedL d v) =
      ∫ x, (W x : ℂ)*star (valL u x)*valL v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(weightedVal_memLp d u).coeFn_toLp,
    (weightedVal_memLp d v).coeFn_toLp,d.nonneg] with x hx hy hw
  change inner ℂ ((weightedVal_memLp d u).toLp (weightedVal d u) x)
    ((weightedVal_memLp d v).toLp (weightedVal d v) x) = _
  rw [hx,hy,RCLike.inner_apply]
  change weightedVal d v x*star (weightedVal d u x) = _
  have hs : (Real.sqrt ‖W x‖ : ℂ)^2 = (W x : ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (norm_nonneg _),Real.norm_of_nonneg hw]
  simp only [weightedVal,star_mul,Complex.star_def,Complex.conj_ofReal]
  calc
    _ = (Real.sqrt ‖W x‖ : ℂ)^2*star (valL u x)*valL v x := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hs]; rfl

lemma form_eq_inner {W : ℝ → ℝ} (d : PotentialData W) (u v : H1C) :
    schrodingerForm W (toH1 u) (toH1 v) =
      inner ℂ (gradL u) (gradL v)-inner ℂ (weightedL d u) (weightedL d v) := by
  rw [schrodingerForm,gradPairing_eq_inner,grad_toLp_toH1,grad_toLp_toH1,weightedL_inner]
  rfl

def shiftedFormMap {W : ℝ → ℝ} (d : PotentialData W) : H1C →L[ℂ] H1C :=
  gradL.adjoint.comp gradL - (weightedL d).adjoint.comp (weightedL d) +
    ((d.b+1 : ℝ) : ℂ) • (valL.adjoint.comp valL)

lemma shiftedFormMap_inner {W : ℝ → ℝ} (d : PotentialData W) (u v : H1C) :
    inner ℂ u (shiftedFormMap d v) =
      inner ℂ (gradL u) (gradL v)-inner ℂ (weightedL d u) (weightedL d v)+
        (d.b+1 : ℂ)*inner ℂ (valL u) (valL v) := by
  change inner ℂ u ((gradL.adjoint (gradL v) -
    (weightedL d).adjoint (weightedL d v)) +
    ((d.b+1 : ℝ) : ℂ) • (valL.adjoint (valL v))) = _
  rw [inner_add_right,inner_sub_right]
  rw [inner_smul_right u (valL.adjoint (valL v)) (((d.b+1 : ℝ) : ℂ))]
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.ofReal_add,Complex.ofReal_one]

lemma shiftedFormMap_coercive {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) :
    (3/4)*‖u‖^2 ≤ (inner ℂ u (shiftedFormMap d u)).re := by
  rw [shiftedFormMap_inner,Complex.add_re,Complex.sub_re]
  have hi (v : L2C) : (inner ℂ v v).re = ‖v‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  have hm : ((d.b+1 : ℂ)*inner ℂ (valL u) (valL u)).re = (d.b+1)*‖valL u‖^2 := by
    rw [Complex.mul_re]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.one_re,Complex.add_im,
      Complex.ofReal_im,Complex.one_im,zero_add,zero_mul,sub_zero,hi]
  rw [hi,hi,hm,h1_norm_sq]
  have h := weightedLM_norm_sq d u
  change ‖weightedL d u‖^2 ≤ _ at h
  linarith

lemma shiftedFormMap_symmetric {W : ℝ → ℝ} (d : PotentialData W) :
    (shiftedFormMap d).IsSymmetric := by
  intro u v
  change inner ℂ (shiftedFormMap d u) v = inner ℂ u (shiftedFormMap d v)
  rw [← inner_conj_symm (𝕜 := ℂ) (shiftedFormMap d u) v, shiftedFormMap_inner,
    shiftedFormMap_inner]
  simp only [map_add,map_sub,map_mul,inner_conj_symm]
  simp

end SharpLiebThirring.OperatorProof

end

end OAI
