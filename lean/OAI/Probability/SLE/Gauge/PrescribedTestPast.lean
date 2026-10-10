import OAI.Probability.SLE.Gauge.PrescribedBatchClock

namespace OAI

/-! The history before each test is taken at the preceding test endpoint.
The intervening radius gap is reserved for angular mixing. -/
noncomputable section
open Set Filter

namespace SLEExactGauge.Target

def prescribedTestPastLevel {J : ℕ} (κ : ℝ) (W : WienerLaw) (n : ℕ)
    (e : Fin J → ℤ×ℕ) (A : ℝ) (z : ℂ) (i : ℕ) : ℝ :=
  if i=0 then 0 else prescribedBatchLevel κ W n e A z (i-1)+
    2*a κ*(batchLevel κ W n:ℝ)

lemma prescribedTestPastLevel_nonneg {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw)
    (n : ℕ) {J : ℕ} (e : Fin J → ℤ×ℕ) (A : ℝ) (z : ℂ)
    (hl : ∀ o, 0 ≤ entryPhysicalLevel κ W (n,o) A z) (i : ℕ) :
    0 ≤ prescribedTestPastLevel κ W n e A z i := by
  have ha := internal_a_pos hκ
  unfold prescribedTestPastLevel prescribedBatchLevel
  split_ifs
  · exact le_rfl
  · exact add_nonneg (hl _) (by positivity)
  · exact add_nonneg (hl _) (by positivity)

lemma prescribedTestPastLevel_succ {κ : ℝ} (W : WienerLaw) (n : ℕ)
    {J : ℕ} (e : Fin J → ℤ×ℕ) (A : ℝ) (z : ℂ) (i : Fin J) :
    prescribedTestPastLevel κ W n e A z (i.val+1)=
      entryPhysicalLevel κ W (n,some (e i)) A z+2*a κ*(batchLevel κ W n:ℝ) := by
  simp only [prescribedTestPastLevel,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,
    prescribedBatchLevel,dite_eq_left i.isLt,Fin.eta]

lemma prescribedTestPastLevel_monotone {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw)
    {n J : ℕ} (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) (e : Fin J → ℤ×ℕ)
    (he : ∀ i, (e i).2 < multiplicity κ W n (e i).1)
    (horder : StrictMono (fun i => entryPosition κ W (n,some (e i))))
    (A : ℝ) (z : ℂ) (hl : ∀ o, 0 ≤ entryPhysicalLevel κ W (n,o) A z) :
    Monotone (prescribedTestPastLevel κ W n e A z) := by
  intro i j hij
  by_cases hi : i=0
  · subst i
    simpa only [prescribedTestPastLevel,ite_true] using
      prescribedTestPastLevel_nonneg hκ W n e A z hl j
  · have hj : j ≠ 0 := by omega
    simp only [prescribedTestPastLevel,ite_eq_right hi,ite_eq_right hj]
    exact add_le_add
      (prescribedBatchLevel_monotone hκ W hn hm1 hJ e he horder A z
        (Nat.sub_le_sub_right hij 1)) le_rfl

lemma prescribedTestPastLevel_gap {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw)
    {n J : ℕ} (hn : 1 ≤ n) (e : Fin J → ℤ×ℕ)
    (horder : StrictMono (fun i => entryPosition κ W (n,some (e i))))
    (A : ℝ) (z : ℂ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ entryPhysicalLevel κ W (n,some (e i)) A z)
    (hδ : δ ≤ 2*a κ*(n:ℝ)) (i : Fin J) :
    prescribedTestPastLevel κ W n e A z i.val+δ ≤
      entryPhysicalLevel κ W (n,some (e i)) A z := by
  by_cases hi : i.val=0
  · simpa only [prescribedTestPastLevel,hi,ite_true,zero_add] using hfirst i
  · let j : Fin J := ⟨i.val-1,by omega⟩
    have heq : i.val=j.val+1 := by dsimp only [j]; omega
    rw [heq,prescribedTestPastLevel_succ W n e A z j]
    have hpos := horder (show j < i from by
      dsimp only [j]
      exact Nat.sub_lt (Nat.pos_of_ne_zero hi) (by decide))
    have hh := entryPhysicalLevel_gap hκ W hn hpos A z
    linarith

lemma eventually_prescribedTestPastLevel_gap {κ : ℝ} (hκ : 0 < κ)
    (W : WienerLaw) {A : ℝ} (hA : 0 < A) (δ : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (J : ℕ) (e : Fin J → ℤ×ℕ),
      StrictMono (fun i => entryPosition κ W (n,some (e i))) →
      ∀ z : ℂ, Real.exp (-(n:ℝ)) ≤ z.im → ∀ i : Fin J,
        prescribedTestPastLevel κ W n e A z i.val+δ ≤
          entryPhysicalLevel κ W (n,some (e i)) A z := by
  have ha : 0 < 2*a κ := mul_pos (by norm_num) (internal_a_pos hκ)
  have hn : ∀ᶠ n : ℕ in Filter.atTop, δ/(2*a κ) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_entryPhysicalLevel_large hκ W hA δ,hn,
    Filter.eventually_ge_atTop 1] with n hlevel hδ hn1
  intro J e horder z hz i
  apply prescribedTestPastLevel_gap hκ W hn1 e horder A z δ
    (fun j => (hlevel (some (e j)) z hz).le) _ i
  simpa only [mul_comm] using (div_le_iff₀ ha).mp hδ

end SLEExactGauge.Target

end

end OAI
