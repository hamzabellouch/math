import Mathlib
import OAI.Probability.SKGap.Localization.FiniteRankPositive

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

end SKGap

namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

lemma positive_from_gram_path {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (Q : Matrix ι κ ℝ) (C : ℝ → Matrix κ κ ℝ) (hc : Continuous C)
    (hherm : ∀ r ∈ Icc 0 a, (C r).IsHermitian) (hz : C 0=0)
    (hdet : ∀ r ∈ Icc 0 a, (1-(d⁻¹ • (Qᵀ*Q)) * C r).det ≠ 0) :
    (d • (1 : Matrix ι ι ℝ)-Q*C a*Qᵀ).PosDef := by
  apply matrix_path_posDef ha (fun r => d • (1 : Matrix ι ι ℝ)-Q*C r*Qᵀ)
  · fun_prop
  · intro r hr
    apply (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial d))).sub
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose Q (hherm r hr)
  · intro r hr
    have hid : d • (1 : Matrix ι ι ℝ)-Q*C r*Qᵀ =
        d • (1-((d⁻¹ • Q)*C r)*Qᵀ) := by
      simp only [smul_sub,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    rw [hid,Matrix.det_smul]
    apply mul_ne_zero (pow_ne_zero _ hd.ne')
    rw [Matrix.det_one_sub_mul_comm,← Matrix.mul_assoc,Matrix.mul_smul,← Matrix.smul_mul]
    simpa only [Matrix.smul_mul] using hdet r hr
  · simpa only [hz,Matrix.mul_zero,Matrix.zero_mul,sub_zero] using
      (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hd

theorem limiting_gram_robust {j b e s : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hb1 : b ≤ 1) (he : 0 ≤ e) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι (Fin 3) ℝ)
        (C : Matrix (Fin 3) (Fin 3) ℝ), C.IsHermitian →
        dist (Qᵀ*Q) (limitingGram b e s) < ρ →
        dist C (rankCoefficient j b s) < ρ →
        ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let H := limitingGram b e s
  let C₀ := rankCoefficient j b s
  let F := fun (p : ℝ × (Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ)) (r : ℝ) =>
    (1-((1-p.1)⁻¹ • p.2.1) *
      (rankCoefficient r b s+(r/j) • (p.2.2-C₀))).det
  have hnear : ∀ᶠ p in 𝓝 (0,(H,C₀)), ∀ r ∈ Icc 0 j, F p r ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hbase : F (0,(H,C₀)) r ≠ 0 := by
      simp only [F,sub_zero,inv_one,one_smul,sub_self,smul_zero,add_zero,H]
      rw [limiting_rank_determinant]
      have hrb : r*b < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hr.1 hb1) (hr.2.trans_lt hj1)
      have hre : 0 ≤ r*e := mul_nonneg hr.1 he
      exact ne_of_gt (mul_pos (by nlinarith) (sq_pos_of_pos (by linarith)))
    have hc : ContinuousAt (fun z => F z.1 z.2) ((0,(H,C₀)),r) := by
      unfold F rankCoefficient
      fun_prop (disch := norm_num)
    exact hc.eventually (eventually_ne_nhds hbase)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ,ε,hδ,hδ1,hε,?_⟩
  intro ι _ _ Q C hC hQ hCC
  have hin : dist (δ,(Qᵀ*Q,C)) (0,(H,C₀)) < ε := by
    simp only [Prod.dist_eq,dist_zero_right,Real.norm_eq_abs,abs_of_pos hδ,max_lt_iff]
    exact ⟨hδε,hQ,hCC⟩
  have hh := hball hin
  let D := fun r => rankCoefficient r b s+(r/j) • (C-C₀)
  have hc : Continuous D := by unfold D rankCoefficient; fun_prop
  have hhD : ∀ r ∈ Icc 0 j, (D r).IsHermitian := by
    intro r _
    exact (rankCoefficient_hermitian r b s).add
      ((hC.sub (rankCoefficient_hermitian j b s)).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (r/j))))
  have hz : D 0=0 := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [D,rankCoefficient]
  have heq : D j=C := by simp [D,C₀,div_self hj.ne']
  rw [← heq]
  apply positive_from_gram_path hj.le (sub_pos.mpr hδ1) Q D hc hhD hz
  intro r hr
  exact hh r hr
end SKGap
end
end

end OAI
