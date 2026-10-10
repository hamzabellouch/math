import Mathlib
import OAI.Probability.SKGap.Localization.CubeApprox

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma real_eigenvalue_abs_le_opNorm {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (i : ι) :
    |hM.eigenvalues i| ≤ opNorm M := by
  have he : M.toEuclideanLin.toContinuousLinearMap (hM.eigenvectorBasis i)=hM.eigenvalues i • hM.eigenvectorBasis i := by
    ext k
    exact congrFun (hM.mulVec_eigenvectorBasis i) k
  have hn := hM.eigenvectorBasis.orthonormal.norm_eq_one i
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (hM.eigenvectorBasis i)
  rw [he,norm_smul,Real.norm_eq_abs,hn,mul_one,mul_one] at hh
  exact hh

lemma frobenius_sq_le_rank_opNorm_sq (M : Matrix ι ι ℝ) :
    ‖M‖^2 ≤ (M.rank:ℝ)*(opNorm M)^2 := by
  classical
  let Q := Mᵀ*M
  have hQ : Q.PosSemidef := by simpa only [Q,conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self M
  have hqe (i : ι) : hQ.isHermitian.eigenvalues i ≤ (opNorm M)^2 := by
    have hi := (le_abs_self (hQ.isHermitian.eigenvalues i)).trans (real_eigenvalue_abs_le_opNorm hQ.isHermitian i)
    apply hi.trans
    have hh := opNorm_mul Mᵀ M
    rw [opNorm_transpose] at hh
    exact hh.trans_eq (by ring)
  rw [LogDet.frobenius_sq_trace,hQ.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have ht : (∑ i,hQ.isHermitian.eigenvalues i)=∑ i : {i // hQ.isHermitian.eigenvalues i ≠ 0},hQ.isHermitian.eigenvalues i := by
    exact Finset.sum_congr_set {i | hQ.isHermitian.eigenvalues i ≠ 0} _ _
      (fun _ _ => rfl) (fun i hi => by simpa using hi)
  rw [ht]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (i : {i // hQ.isHermitian.eigenvalues i ≠ 0}) _ => hqe i)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← hQ.isHermitian.rank_eq_card_non_zero_eigs,Q,rank_transpose_mul_self] using hh

lemma frobenius_le_sqrt_rank_opNorm (M : Matrix ι ι ℝ) :
    ‖M‖ ≤ sqrt (M.rank:ℝ)*opNorm M := by
  have hop : 0 ≤ opNorm M := norm_nonneg _
  apply (sq_le_sq₀ (norm_nonneg M) (by positivity : 0 ≤ sqrt (M.rank:ℝ)*opNorm M)).mp
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg _)]
  exact frobenius_sq_le_rank_opNorm_sq M
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma logdet_cube_difference {j δ R γ : ℝ} (hj : 0 ≤ j) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hγ : 0 < γ) {a b : ι → ℝ} (ha : ∀ i,0 ≤ a i) (ha1 : ∀ i,a i ≤ 1)
    (hb : ∀ i,0 ≤ b i) (hb1 : ∀ i,b i ≤ 1) (hab : ∀ i,|a i-b i| ≤ δ)
    {M : Matrix ι ι ℝ} (hM : opNorm M ≤ R) :
    |LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a M 1)-
      LogDet.regularizedLogDet γ (logPath (j*coordAverage b) b M 1)| ≤
      ((2*j+R)/sqrt γ)*δ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 < sqrt (Fintype.card ι:ℝ) := sqrt_pos.mpr hn
  have hh := logPath_cube_difference hj hδ hR ha ha1 hb hb1 hab hM
  apply (LogDet.regularizedLogDet_lipschitz hγ _ _).trans
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/sqrt ((Fintype.card ι:ℝ)*γ))).trans_eq
  rw [sqrt_mul hn.le]
  field_simp

lemma logdet_cube_net_transfer {j δ R γ α : ℝ} (hj : 0 ≤ j) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hγ : 0 < γ) (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Icc (0:ℝ) 1)
    (hcover : ∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ s, |x-y| ≤ δ)
    {M : Matrix ι ι ℝ} (hM : opNorm M ≤ R)
    (hnet : ∀ v : ι → s, LogDet.regularizedLogDet γ (logPath (j*coordAverage (fun i => (v i:ℝ)))
      (fun i => (v i:ℝ)) M 1) ≤ j*(coordAverage (fun i => (v i:ℝ)))^2+α)
    {a : ι → ℝ} (ha : ∀ i,0 ≤ a i) (ha1 : ∀ i,a i ≤ 1) :
    LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a M 1) ≤ j*(coordAverage a)^2+
      α+(((2*j+R)/sqrt γ)+2*j)*δ := by
  classical
  choose b hb hab using fun i => hcover (a i) ⟨ha i,ha1 i⟩
  let v : ι → s := fun i => ⟨b i,hb i⟩
  have hb0 (i) : 0 ≤ b i := (hs _ (hb i)).1
  have hb1 (i) : b i ≤ 1 := (hs _ (hb i)).2
  have hn := hnet v
  have hd := (abs_le.mp (logdet_cube_difference hj hδ.le hR hγ ha ha1 hb0 hb1 hab hM)).2
  have hq := (abs_le.mp (coordAverage_sq_sub_le hj ha ha1 hb0 hb1 hab)).1
  change LogDet.regularizedLogDet γ (logPath (j*coordAverage b) b M 1) ≤ j*(coordAverage b)^2+α at hn
  linarith

lemma logdet_rank_perturbation {γ M₂ : ℝ} (hγ : 0 < γ) (_hM₂ : 0 ≤ M₂) {r₀ : ℕ}
    (M E : Matrix ι ι ℝ) (hrank : E.rank ≤ r₀) (hop : opNorm E ≤ M₂) :
    |LogDet.regularizedLogDet γ (M+E)-LogDet.regularizedLogDet γ M| ≤
      M₂*sqrt (r₀:ℝ)/sqrt ((Fintype.card ι:ℝ)*γ) := by
  have hn := frobenius_le_sqrt_rank_opNorm E
  have he := (mul_le_mul (sqrt_le_sqrt (Nat.cast_le.mpr hrank)) hop
    (norm_nonneg _) (sqrt_nonneg (r₀:ℝ)))
  have h := (LogDet.regularizedLogDet_lipschitz hγ (M+E) M)
  rw [add_sub_cancel_left] at h
  apply h.trans
  exact (mul_le_mul_of_nonneg_left (hn.trans he) (by positivity : 0 ≤ 1/sqrt ((Fintype.card ι:ℝ)*γ))).trans_eq (by ring)

lemma product_mesh_absorption {a : ℝ} (ha : 0 < a) (m n : ℕ)
    (hn : ((m:ℝ)+1)/a ≤ (n:ℝ)) :
    (m:ℝ)^n*(2*Real.exp (-a*(n:ℝ)^2)) ≤ 2*Real.exp (-(n:ℝ)) := by
  have hm : (m:ℝ) ≤ Real.exp (m:ℝ) := by linarith [Real.add_one_le_exp (m:ℝ)]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m) hm n
  rw [← Real.exp_nat_mul] at hpow
  have hmn : (m:ℝ)+1 ≤ a*(n:ℝ) := by nlinarith [(div_le_iff₀ ha).mp hn]
  have he : Real.exp ((n:ℝ)*(m:ℝ)-a*(n:ℝ)^2) ≤ Real.exp (-(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hmn)]
  have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 2*Real.exp (-a*(n:ℝ)^2) by positivity)
  calc
    _ ≤ Real.exp ((n:ℝ)*(m:ℝ))*(2*Real.exp (-a*(n:ℝ)^2)) := hh
    _ = 2*Real.exp ((n:ℝ)*(m:ℝ)-a*(n:ℝ)^2) := by rw [sub_eq_add_neg,Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)
end SKGap
end
end

end OAI
