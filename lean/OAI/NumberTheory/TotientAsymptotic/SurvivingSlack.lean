import OAI.NumberTheory.TotientAsymptotic.ActualComparisonCutoffs

namespace OAI

/-! Renumbering the actual surviving indices preserves the good-witness slack. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma orderEmbedding_offset_le {b i : ℕ} (j : Fin b ↪o ℕ) (hb : 0< b)
    (hfirst : j ⟨0,hb⟩=i) (r : Fin b) : i+r.val≤ j r := by
  have hall : ∀ n (hn : n< b), i+n≤ j ⟨n,hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; simpa only [Nat.add_zero,hfirst] using (le_refl i)
    | succ n ih =>
      intro hn
      have hn' : n< b := by omega
      have hprev := ih hn'
      have hs := j.strictMono (show (⟨n,hn'⟩ : Fin b)<⟨n+1,hn⟩ from Nat.lt_succ_self n)
      omega
  exact hall r.val r.isLt

lemma shifted_slack_sum {J i : ℕ} (hi : i≤ J) (u : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (J-i), a k*u (i+k)) =
      ∑ r ∈ Finset.Icc (i+1) J, a (r-i)*u r := by
  apply Finset.sum_bij (fun k _ => i+k)
  · intro k hk
    have := Finset.mem_Icc.mp hk
    apply Finset.mem_Icc.mpr
    omega
  · intro k hk l hl he
    omega
  · intro r hr
    refine ⟨r-i,?_,?_⟩
    · have := Finset.mem_Icc.mp hr
      apply Finset.mem_Icc.mpr
      omega
    · have := Finset.mem_Icc.mp hr
      omega
  · intro k hk
    simp only [Nat.add_sub_cancel_left]

/-- The discarded matching coordinates cannot consume slack. This is stated
for the actual order embedding of survivors, with the original index offset. -/
theorem surviving_weighted_slack {x : ℝ} {H i p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hk : collisionLastIndex x i< L x H)
    (hfirst : wholeWitnessPrime p η i≠wholeWitnessPrime q ξ i)
    (ν : ℕ → ℝ) {Y σ e : ℝ} (hY : 0< Y)
    (hbudget : (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r)≤(1-σ)*Y)
    (hgrid : ∀ r (hr : r ∈ Finset.Icc 1 ((collisionSurvivors p q η ξ i (collisionLastIndex x i)).card-1)),
      ν r≤ remainderCoord x η (survivingIndex p q η ξ i (collisionLastIndex x i)
        ⟨r,by have := Finset.mem_Icc.mp hr; omega⟩)/Y+e) :
    (∑ r ∈ Finset.Icc 1 ((collisionSurvivors p q η ξ i (collisionLastIndex x i)).card-1), a r*ν r)≤
      1-σ+e*(∑ r ∈ Finset.Icc 1 ((collisionSurvivors p q η ξ i (collisionLastIndex x i)).card-1), a r) := by
  obtain ⟨hb,hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change 0 < (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card at hb
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩=i at hidx0
  let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
  let j : ℕ → ℕ := fun r => if hr : r< b then
    survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hr⟩-i else 0
  let u : ℕ → ℝ := fun r => remainderCoord x η (i+r)
  have hir : i≤ L x H := (Nat.le_add_right i (collisionCutoff (m x-i))).trans hk.le
  have hidx (r : ℕ) (hr : r∈Finset.Icc 1 (b-1)) :
      r≤ j r ∧ j r≤ L x H-i := by
    have hrb : r< b := by have := Finset.mem_Icc.mp hr; omega
    have hoff := orderEmbedding_offset_le (survivingIndex p q η ξ i (collisionLastIndex x i)) hb hidx0 ⟨r,hrb⟩
    change i+r ≤ survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩ at hoff
    have hmem := survivingIndex_mem p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩
    have hupper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2
    simp only [j,dite_eq_left hrb]
    constructor <;> omega
  have hinj : Set.InjOn j (↑(Finset.Icc 1 (b-1)) : Set ℕ) := by
    intro r hr s hs he
    have hrb : r< b := by have := Finset.mem_Icc.mp hr; omega
    have hsb : s< b := by have := Finset.mem_Icc.mp hs; omega
    simp only [j,dite_eq_left hrb,dite_eq_left hsb] at he
    have hrlo := (orderEmbedding_offset_le (survivingIndex p q η ξ i (collisionLastIndex x i)) hb hidx0 ⟨r,hrb⟩)
    have hslo := (orderEmbedding_offset_le (survivingIndex p q η ξ i (collisionLastIndex x i)) hb hidx0 ⟨s,hsb⟩)
    change i+r ≤ survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩ at hrlo
    change i+s ≤ survivingIndex p q η ξ i (collisionLastIndex x i) ⟨s,hsb⟩ at hslo
    have heq : survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩=
        survivingIndex p q η ξ i (collisionLastIndex x i) ⟨s,hsb⟩ := by omega
    exact congrArg Fin.val ((survivingIndex p q η ξ i (collisionLastIndex x i)).injective heq)
  apply gridded_weighted_slack (b-1) (L x H-i) j u ν Y σ e hY hinj hidx
  · intro r hr
    have hmem := Finset.mem_Icc.mp hr
    have hirL : i+r∈Finset.Icc 1 (L x H) := by apply Finset.mem_Icc.mpr; omega
    have hu := (hη.2.1 (i+r) hirL).2.1
    exact (mul_nonneg (by norm_num) (bandScale_nonnegative _ _)).trans hu
  · simpa only [u,shifted_slack_sum hir] using hbudget
  · intro r hr
    have hrb : r< b := by have := Finset.mem_Icc.mp hr; omega
    have hoff := orderEmbedding_offset_le (survivingIndex p q η ξ i (collisionLastIndex x i)) hb hidx0 ⟨r,hrb⟩
    have hadd : i+(survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩-i)=
        survivingIndex p q η ξ i (collisionLastIndex x i) ⟨r,hrb⟩ := by omega
    simpa only [u,j,dite_eq_left hrb,hadd] using hgrid r hr

end TotientAsymptotic

end

end OAI
