import OAI.Combinatorics.ThinTrees.ResponseFixedPoint

namespace OAI

universe uI uV uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {V : Type uV} [Fintype V] [DecidableEq V]
def mixtureBadWeight (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ) (t : ℝ) (b : V → ℝ) : ℝ :=
  ∑i ∈ C, if t < qform (Y i)⁻¹ b then w i else 0
lemma mixture_resistance (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ)
    (hw : ∀i ∈ C, 0 ≤ w i) (hw1 : (∑i ∈ C, w i)=1)
    (hY : ∀i ∈ C, (Y i).PosDef) {X : Matrix V V ℝ} (hX : X.PosDef)
    (heq : (∑i ∈ C, w i • Y i)=X) {t : ℝ} (ht : 0 < t) (b : V → ℝ)
    (hb : mixtureBadWeight C w Y t b ≤ 1/2) : qform X⁻¹ b ≤ 2*t := by
  classical
  let good : I → ℝ := fun i => if t < qform (Y i)⁻¹ b then 0 else w i
  have hsplit : (∑i ∈ C, good i)+mixtureBadWeight C w Y t b=1 := by
    rw [mixtureBadWeight,←sum_add_distrib,←hw1]
    apply sum_congr rfl
    intro i _
    dsimp [good]
    split_ifs <;> simp
  have hgood : (1/2:ℝ) ≤ ∑i ∈ C, good i := by linarith
  have ho : ∀i ∈ C, good i • vecMulVec b b ≤ (t*w i) • Y i := by
    intro i hi
    dsimp [good]
    split_ifs with h
    · simp only [zero_smul]
      exact smul_nonneg (mul_nonneg ht.le (hw i hi)) (Matrix.nonneg_iff_posSemidef.mpr (hY i hi).posSemidef)
    · have hh : vecMulVec b b ≤ t • Y i := Matrix.le_iff.mpr ((resistance_order (hY i hi) b ht).mp (le_of_not_gt h))
      simpa only [smul_smul,mul_comm] using smul_le_smul_of_nonneg_left hh (hw i hi)
  have hs : (∑i ∈ C, good i) • vecMulVec b b ≤ t • X := by
    have hh := sum_le_sum ho
    rw [←sum_smul] at hh
    rw [←heq,smul_sum]
    convert hh using 1
    apply sum_congr rfl
    intro i _
    rw [smul_smul]
  have hbpsd : 0 ≤ vecMulVec b b := Matrix.nonneg_iff_posSemidef.mpr (by simpa only [star_trivial] using posSemidef_vecMulVec_self_star b)
  have hhalf : (1/2:ℝ) • vecMulVec b b ≤ t • X := (smul_le_smul_of_nonneg_right hgood hbpsd).trans hs
  have hdouble := smul_le_smul_of_nonneg_left hhalf (by norm_num : (0:ℝ) ≤ 2)
  have horder : vecMulVec b b ≤ (2*t) • X := by
    simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using hdouble
  exact (resistance_order hX b (by positivity)).mpr (Matrix.le_iff.mp horder)

lemma mixture_bad_bound {E : Type uE} [DecidableEq E] (B : Finset E) (b : E → V → ℝ)
    (C : Finset I) (w : I → ℝ) (Y : I → Matrix V V ℝ)
    (hw : ∀i ∈ C, 0 ≤ w i) (hw1 : (∑i ∈ C, w i)=1)
    (hY : ∀i ∈ C, (Y i).PosDef) {X : Matrix V V ℝ} (hX : X.PosDef)
    (heq : (∑i ∈ C, w i • Y i)=X) {t δ : ℝ} (ht : 0 < t)
    (hcount : ∀i ∈ C, 0 < w i → ((B.filter (fun e => t < qform (Y i)⁻¹ (b e))).card:ℝ) ≤ δ*B.card) :
    ((B.filter (fun e => 2*t < qform X⁻¹ (b e))).card:ℝ) ≤ 2*δ*B.card := by
  classical
  by_cases hB : B=∅
  · simp [hB]
  have hBp : (0:ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr hB))
  let z := fun e => mixtureBadWeight C w Y t (b e)
  have hz (e : E) : 0 ≤ z e := sum_nonneg (fun i hi => by split_ifs; exact hw i hi; exact le_rfl)
  have hsum : (∑e ∈ B, z e) ≤ δ*B.card := by
    calc
      _ = ∑i ∈ C, w i*((B.filter (fun e => t < qform (Y i)⁻¹ (b e))).card:ℝ) := by
        dsimp [z,mixtureBadWeight]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [←sum_filter]
        simp [mul_comm]
      _ ≤ ∑i ∈ C, w i*(δ*B.card) := by
        apply sum_le_sum
        intro i hi
        rcases (hw i hi).eq_or_lt with hzero | hpos
        · simp [←hzero]
        · exact mul_le_mul_of_nonneg_left (hcount i hi hpos) (hw i hi)
      _ = δ*B.card := by rw [←sum_mul,hw1,one_mul]
  have havg : (B.card:ℝ)⁻¹*(∑e ∈ B, z e) ≤ δ := by
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ hBp).mpr hsum
  have hm := finite_markov B z (fun e _ => hz e) (by norm_num : (0:ℝ)<1/2) havg
  have hsub : B.filter (fun e => 2*t < qform X⁻¹ (b e)) ⊆ B.filter (fun e => 1/2 < z e) := by
    intro e he
    obtain ⟨heB,heR⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨heB,?_⟩
    by_contra h
    have hh := mixture_resistance C w Y hw hw1 hY hX heq ht (b e) (le_of_not_gt h)
    linarith
  have hc : ((B.filter (fun e => 2*t < qform X⁻¹ (b e))).card:ℝ) ≤ (B.filter (fun e => 1/2 < z e)).card := by
    exact_mod_cast card_le_card hsub
  nlinarith

end StrongThinTree

end
end

end OAI
