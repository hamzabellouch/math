import Mathlib
import OAI.Analysis.AffineBernstein.NewtonBasis
import OAI.Analysis.AffineBernstein.RadialAdjugateGL

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter
open scoped Topology

open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeFullRadiusMatrix_linear_comp (B : S →L[ℝ] S) (A : E →L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : OrthonormalBasis κ ℝ E) :
    let P := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
    tubeFullRadiusMatrix (fun z => H (B z.1,A z.2)) q b =
      Pᵀ * tubeFullRadiusMatrix H (B q.1,A q.2) b * P := by
  dsimp only
  have hre (v : E) : ((0:S),v) = ∑ i, b.repr v i • (0,b i) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa only [Prod.snd_sum,Prod.smul_snd,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' v).symm
  ext i j
  change fderiv ℝ (fderiv ℝ (fun z => H (B z.1,A z.2))) q (0,b i) (0,b j) = _
  have hh := second_fderiv_affine_comp (B.prodMap A) (0:S × E)
    (x:=q) (by simpa only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map] using hH) ((0:S),b i) ((0:S),b j)
  simp only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map,map_zero] at hh
  rw [hh,hre (A (b i)),hre (A (b j))]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix_apply,Finset.sum_mul,
    tubeFullRadiusMatrix,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply,
    ContinuousLinearMap.coe_coe]
  ring

lemma tubeBaseMatrix_linear_comp (B : S →L[ℝ] S) (A : E →L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : Module.Basis ι ℝ S) :
    let P := LinearMap.toMatrix b b B.toLinearMap
    tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b =
      Pᵀ * tubeBaseMatrix H (B q.1,A q.2) b * P := by
  dsimp only
  have hre (v : S) : (v,(0:E)) = ∑ i, b.repr v i • (b i,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.smul_fst] using (b.sum_repr v).symm
    · simp [Prod.snd_sum]
  ext i j
  change -fderiv ℝ (fderiv ℝ (fun z => H (B z.1,A z.2))) q (b i,0) (b j,0) = _
  have hh := second_fderiv_affine_comp (B.prodMap A) (0:S × E)
    (x:=q) (by simpa only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map] using hH) (b i,(0:E)) (b j,(0:E))
  simp only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map,map_zero] at hh
  rw [hh,hre (B (b i)),hre (B (b j))]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix_apply,Finset.sum_mul,
    tubeBaseMatrix,Matrix.of_apply,← Finset.sum_neg_distrib,neg_mul,mul_neg]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ContinuousLinearMap.coe_coe]
  ring

lemma tubeAngularDensity_linear_comp (B : S →L[ℝ] S) (A : E ≃L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (he : ‖q.2‖ = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) (B q.1,A q.2) (0,v) (0,A q.2) = 0) :
    tubeAngularDensity (fun z => H (B z.1,A z.2)) q b =
      A.toLinearMap.det^2 / ‖A q.2‖^2 * tubeAngularDensity H (B q.1,A q.2) b := by
  let P := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  let K := tubeFullRadiusMatrix H (B q.1,A q.2) b
  let v : κ ⊕ Unit → ℝ := b.repr q.2
  have hv : (∑ i, v i*v i) = 1 := by
    dsimp only [v]
    rw [show (∑ i, b.repr q.2 i*b.repr q.2 i) = inner ℝ q.2 q.2 by
      simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm q.2] using b.sum_inner_mul_inner q.2 q.2]
    simp [he]
  have hw : P *ᵥ v = b.repr (A q.2) := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A.toLinearMap q.2
  have he0 : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have hw0 : (P *ᵥ v) ≠ 0 := by
    rw [hw]
    intro hz
    have hz' : A q.2 = 0 := b.repr.injective (by simpa using hz)
    exact he0 (A.injective (by simpa using hz'))
  have hrad : K *ᵥ (P *ᵥ v) = 0 := by
    rw [hw]
    exact tubeFullRadiusMatrix_radial b hr
  obtain ⟨c,hc⟩ := radial_adjugate_exists_scalar (tubeFullRadiusMatrix_symm hH b) hw0 hrad
  have ht := adjugate_congruence_trace_radial P K v c hc hv
  have htr : K.adjugate.trace = c * ‖A q.2‖^2 := by
    rw [hc,Matrix.trace_smul,Matrix.trace_vecMulVec,hw]
    change c * (∑ i, b.repr (A q.2) i*b.repr (A q.2) i) = _
    have hh : (∑ i, b.repr (A q.2) i*b.repr (A q.2) i) = inner ℝ (A q.2) (A q.2) := by
      simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm (A q.2)] using
        b.sum_inner_mul_inner (A q.2) (A q.2)
    rw [hh,real_inner_self_eq_norm_sq]
  have hnorm : ‖A q.2‖ ≠ 0 := norm_ne_zero_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  unfold tubeAngularDensity
  have hM : tubeFullRadiusMatrix (fun z => H (B z.1,A z.2)) q b = Pᵀ*K*P :=
    tubeFullRadiusMatrix_linear_comp B A.toContinuousLinearMap hH b
  rw [hM]
  change (Pᵀ*K*P).adjugate.trace = A.toLinearMap.det^2 / ‖A q.2‖^2 * K.adjugate.trace
  rw [ht,htr]
  have hdet : P.det = A.toLinearMap.det := (LinearMap.det_toMatrix b.toBasis _)
  rw [hdet]
  field_simp

end AffineBernstein
end

end OAI
