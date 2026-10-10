import Mathlib
import OAI.Analysis.HardSphere.Density.DensityOperators

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density
open ContinuousLinearMap
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma Operator.compression_summable (T : Operator H) (A : H →L[ℂ] K) :
    Summable (fun j : basisSet K ↦
      (inner ℂ (A.adjoint (basis K j)) (T.toCLM (A.adjoint (basis K j)))).re) := by
  have hh := (T.entry_summable A (basis K)).prod_symm.prod
  convert hh using 1
  funext j
  change _ = ∑' i : basisSet H,T.entry A (basis K) i j
  rw [(T.entry_col A (basis K) j).tsum_eq,T.root_norm_sq]

lemma Operator.compressionTrace_linear (T U V : Operator H) (A : H →L[ℂ] K)
    (c d : ℝ) (hV : V.toCLM=c • T.toCLM+d • U.toCLM) :
    V.compressionTrace A=c*T.compressionTrace A+d*U.compressionTrace A := by
  unfold Operator.compressionTrace
  simp only [hV,add_apply,smul_apply,inner_add_right,inner_smul_right_eq_smul,
    Complex.add_re,Complex.smul_re,smul_eq_mul]
  rw [((T.compression_summable A).mul_left c).tsum_add ((U.compression_summable A).mul_left d),
    tsum_mul_left,tsum_mul_left]

omit [CompleteSpace H] in
lemma rankOne_diagonal (x y : H) :
    (inner ℂ x ((InnerProductSpace.rankOne ℂ y y) x)).re=‖inner ℂ x y‖^2 := by
  rw [InnerProductSpace.rankOne_apply,inner_smul_right,←inner_conj_symm y x]
  rw [Complex.conj_mul']
  norm_cast

def pure (x : H) (hx : ‖x‖=1) : Operator H where
  toCLM := InnerProductSpace.rankOne ℂ x x
  positive := ContinuousLinearMap.nonneg_iff_isPositive.mpr (InnerProductSpace.isPositive_rankOne_self x)
  trace_one := by
    simpa only [rankOne_diagonal,hx,one_pow] using parseval (basis H) x

lemma pure_compression (x : H) (hx : ‖x‖=1) (A : H →L[ℂ] K) :
    (pure x hx).compressionTrace A=‖A x‖^2 := by
  unfold Operator.compressionTrace
  change (∑' j : basisSet K,(inner ℂ (A.adjoint (basis K j))
    ((InnerProductSpace.rankOne ℂ x x) (A.adjoint (basis K j)))).re)=_
  calc
    _ = ∑' j : basisSet K,‖inner ℂ (A.adjoint (basis K j)) x‖^2 :=
      tsum_congr fun j ↦ rankOne_diagonal _ _
    _ = ∑' j : basisSet K,‖inner ℂ (basis K j) (A x)‖^2 := by simp only [A.adjoint_inner_left]
    _ = _ := (parseval (basis K) (A x)).tsum_eq

end HardSphere.Density

namespace HardSphere.Density
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma projection_diagonal (V : Submodule ℂ H) [FiniteDimensional ℂ V] (x : H) :
    (inner ℂ x (V.starProjection x)).re=
      ∑j : Fin (Module.finrank ℂ V),‖inner ℂ x ((stdOrthonormalBasis ℂ V j : V):H)‖^2 := by
  rw [(stdOrthonormalBasis ℂ V).starProjection_eq_sum_rankOne]
  simp only [sum_apply,inner_sum,Complex.re_sum,rankOne_diagonal]

lemma projection_trace (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    HasSum (fun i : basisSet H ↦ (inner ℂ (basis H i) (V.starProjection (basis H i))).re)
      (Module.finrank ℂ V : ℝ) := by
  have hj (j : Fin (Module.finrank ℂ V)) :
      HasSum (fun i : basisSet H ↦ ‖inner ℂ (basis H i) ((stdOrthonormalBasis ℂ V j : V):H)‖^2) 1 := by
    simpa only [Submodule.norm_coe,(stdOrthonormalBasis ℂ V).norm_eq_one,one_pow] using
      parseval (basis H) ((stdOrthonormalBasis ℂ V j : V):H)
  have hh := hasSum_sum (s:=Finset.univ) (fun j _ ↦ hj j)
  simpa only [projection_diagonal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh

def normalizedProjection (V : Submodule ℂ H) [FiniteDimensional ℂ V] [Nontrivial V] : Operator H where
  toCLM := ((Module.finrank ℂ V:ℝ)⁻¹) • V.starProjection
  positive := smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) isStarProjection_starProjection.nonneg
  trace_one := by
    have hd : (Module.finrank ℂ V:ℝ)≠0 := by exact_mod_cast (Module.finrank_pos (R:=ℂ) (M:=V)).ne'
    have hh := (projection_trace V).mul_left ((Module.finrank ℂ V:ℝ)⁻¹)
    simpa only [smul_apply,inner_smul_right_eq_smul,Complex.smul_re,smul_eq_mul,inv_mul_cancel₀ hd] using hh

lemma normalizedProjection_support (V : Submodule ℂ H) [FiniteDimensional ℂ V] [Nontrivial V] :
    (normalizedProjection V).toCLM.kerᗮ=V := by
  have hd : (Module.finrank ℂ V:ℝ)⁻¹≠0 := inv_ne_zero (by exact_mod_cast (Module.finrank_pos (R:=ℂ) (M:=V)).ne')
  have hk : (normalizedProjection V).toCLM.ker=V.starProjection.ker := by
    ext x
    change ((Module.finrank ℂ V:ℝ)⁻¹) • V.starProjection x=0 ↔ V.starProjection x=0
    simp only [smul_eq_zero,hd,false_or]
  rw [hk,V.ker_starProjection,V.orthogonal_orthogonal]

end HardSphere.Density
end

end OAI
