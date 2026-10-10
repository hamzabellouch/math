import Mathlib
import OAI.Geometry.PrescribedRicci.JetTrim

namespace OAI

/-! Jet Remainder Bound. -/

section

 

noncomputable section
open Set Finset MeasureTheory
open scoped ContDiff Classical BigOperators ENNReal
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] [DecidableEq κ]

omit [Nonempty κ] in
lemma lpNorm_complex_prod_L2_Linf (f : κ → E → ℂ) (i : κ)
    (hf2 : MemLp (f i) 2 volume) (hfi : ∀ j, MemLp (f j) ∞ volume)
    {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ j, lpNorm (f j) ∞ volume ≤ A) (hfb : lpNorm (f i) 2 volume ≤ B) :
    lpNorm (fun x => ∏ j, f j x) 2 volume ≤ B*A^(Fintype.card κ-1) := by
  let p : κ → ℝ≥0∞ := fun j => if j = i then 2 else ∞
  have hp : ∀ j, MemLp (f j) (p j) volume := by
    intro j; by_cases hj : j = i
    · subst j; simpa [p] using hf2
    · simpa [p,hj] using hfi j
  have hs : (∑ j, (p j)⁻¹)⁻¹ = 2 := by
    rw [← Finset.add_sum_erase Finset.univ (fun j => (p j)⁻¹) (Finset.mem_univ i)]
    have he : ∑ j ∈ Finset.univ.erase i, (p j)⁻¹ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [p,(Finset.mem_erase.mp hj).1]
    simp [he,p]
  have hh := lpNorm_complex_finite_prod (μ:=volume) Finset.univ f p (fun j _ => hp j)
  rw [hs] at hh
  apply hh.trans
  rw [← Finset.mul_prod_erase Finset.univ (fun j => lpNorm (f j) (p j) volume) (Finset.mem_univ i)]
  have hi : p i = 2 := by simp [p]
  rw [hi]
  apply mul_le_mul hfb _ (Finset.prod_nonneg fun _ _ => lpNorm_nonneg) hB
  have he : ∏ j ∈ Finset.univ.erase i, lpNorm (f j) (p j) volume ≤
      ∏ _j ∈ Finset.univ.erase i, A := by
    apply Finset.prod_le_prod₀
    · intro j _; exact lpNorm_nonneg
    · intro j hj
      simpa [p,(Finset.mem_erase.mp hj).1] using hfa j
  simpa using he

lemma monoEval_tame_zero (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i))
    (s : κ → List ι) (hm : ∑ i, (trimWord (s i)).length = 0) :
    lpNorm (monoEval e f s) 2 volume ≤
      (2*familyJetNorm e (realComponents (initialJet e f)) 0 2) *
        (2*familyJetNorm e (realComponents (initialJet e f)) 0 ∞)^(Fintype.card κ-1) := by
  have hzero (i : κ) : trimWord (s i) = [] := by
    apply List.length_eq_zero_iff.mp
    exact Nat.eq_zero_of_le_zero (hm ▸ Finset.single_le_sum (f:=fun i => (trimWord (s i)).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  let g := initialJet e f
  let a : κ → κ × Option ι := fun i => (i,baseDirection (s i))
  have he : monoEval e f s = fun x => ∏ i, g (a i) x := by
    funext x; unfold monoEval
    apply Finset.prod_congr rfl
    intro i _
    rw [cword_trim e f i (s i),hzero i]
    rfl
  rw [he]
  have hg := initialJet_smooth e f hf
  have hgc := initialJet_compact e f hc
  let i : κ := Classical.choice inferInstance
  apply lpNorm_complex_prod_L2_Linf (fun i => g (a i)) i
    ((hg _).continuous.memLp_of_hasCompactSupport (hgc _))
    (fun j => (hg _).continuous.memLp_of_hasCompactSupport (hgc _))
    (mul_nonneg (by norm_num) (familyJetNorm_nonneg ..))
    (mul_nonneg (by norm_num) (familyJetNorm_nonneg ..))
  · intro j
    exact cjet_lpNorm_le e g hg hgc (a j) (Fin.elim0 : Fin 0 → ι) (by simp)
  · exact cjet_lpNorm_le e g hg hgc (a i) (Fin.elim0 : Fin 0 → ι) (by norm_num)

theorem monoRemainder_uniform_bound {Z : Type*} (e : ι → E) (F : Z → κ → E → ℂ)
    (hf : ∀ z i, ContDiff ℝ ∞ (F z i)) (hc : ∀ z i, HasCompactSupport (F z i))
    (ws : List ι) (s : κ → List ι) (hs : s ∈ monoRemainder ws)
    {A : ℝ} (hA : 0 ≤ A)
    (h0 : ∀ z, familyJetNorm e (realComponents (initialJet e (F z))) 0 ∞ ≤ A)
    (h2 : ∀ j ≤ ws.length-2, ∃ B : ℝ, 0 ≤ B ∧
      ∀ z, familyJetNorm e (realComponents (initialJet e (F z))) j 2 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, lpNorm (monoEval e (F z) s) 2 volume ≤ C := by
  let m := ∑ i, (trimWord (s i)).length
  have hmle : m ≤ ws.length-2 := remainder_trimmed_order hs
  obtain ⟨B,hB,hb⟩ := h2 m hmle
  by_cases hm : m = 0
  · refine ⟨(2*B)*(2*A)^(Fintype.card κ-1),by positivity,fun z => ?_⟩
    apply (monoEval_tame_zero e (F z) (hf z) (hc z) s hm).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by simpa [hm] using hb z) (by norm_num)
    · exact pow_le_pow_left₀ (mul_nonneg (by norm_num) (familyJetNorm_nonneg ..))
        (mul_le_mul_of_nonneg_left (h0 z) (by norm_num)) _
    · exact pow_nonneg (mul_nonneg (by norm_num) (familyJetNorm_nonneg ..)) _
    · positivity
  · let K : ℝ := 2^(Fintype.card κ) * (2*(m:ℝ))^(∑ i, (trimWord (s i)).length*(m-(trimWord (s i)).length))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨K*A^(Fintype.card κ-1)*B,by positivity,fun z => ?_⟩
    apply (monoEval_tame_positive e (F z) (hf z) (hc z) s (Nat.pos_of_ne_zero hm)).trans
    simp only [← mul_assoc]
    change K * _ * _ ≤ K * _ * _
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (familyJetNorm_nonneg ..) (h0 z) _) hK
    · exact hb z
    · exact familyJetNorm_nonneg ..
    · positivity
end TameInterpolation

end
end

end OAI
