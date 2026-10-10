import OAI.Dynamics.EntropyCounterexample.MapSignals
import OAI.Dynamics.EntropyCounterexample.RegisterReset
import OAI.Dynamics.EntropyCounterexample.ClockDynamics

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem rawMap_register_zero_on_inactive_interval
    (D : SphereData) (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (s j : ℕ) (hzero : ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere))
    (hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100)
    (hprep : ∀ n, s ≤ n → n < j → preparationCoeff (t n) = 0) :
    ∀ n, s ≤ n → n ≤ j → ∀ i, (x n).2.2 i = ((0 : ℂ) : Sphere) := by
  intro n hsn hnj i
  apply Register.register_zero_on_interval
    ((0 : ℂ) : Sphere) (fun z : ℂ => (z : Sphere)) rfl D.saturation hS
    (fun m => periodicGain D (x m).1)
    (fun m => input D i (x m).1 (x m).2.1)
    (fun m => (x m).2.2 i) ?_ s j (hzero i) ?_ n hsn hnj
  · intro m
    simp only [horbit m, rawMap, Complex.real_smul]
  · intro m hsm hmj
    rw [← hlift m, input, AddCircle.liftIco_zero_coe_apply (hstrip m hsm hmj)]
    simp [baseInput, hprep m hsm hmj]

theorem concreteMap_register_zero_after_reset_before_preparation
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (r s : ℕ) (hrs : r + 1 ≤ s) (hreset : t r ∈ Set.Icc 2 5)
    (hstrip : ∀ n, r + 1 ≤ n → n < s → t n ∈ Set.Ico 0 100)
    (hprep : ∀ n, r + 1 ≤ n → n < s → preparationCoeff (t n) = 0) :
    ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere) := by
  have hzero : ∀ i, (x (r + 1)).2.2 i = ((0 : ℂ) : Sphere) := by
    intro i
    rw [horbit r]
    change (concreteMap L hL ((x r).1, (x r).2.1, (x r).2.2)).2.2 i = _
    rw [← hlift r]
    exact concreteMap_register_reset L hL hreset _ _ i
  exact rawMap_register_zero_on_inactive_interval (concreteData L hL)
    (concrete_saturation_zero L hL) x horbit t hlift (r + 1) s hzero
    hstrip hprep s hrs le_rfl

theorem concreteMap_register_zero_at_preparation_start
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (r s : ℕ) (hrs : r + 1 ≤ s) (hreset : t r ∈ Set.Icc 2 5)
    (hbefore : ∀ n, r + 1 ≤ n → n < s → t n ∈ Set.Icc 0 8) :
    ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere) := by
  apply concreteMap_register_zero_after_reset_before_preparation
    L hL x horbit t hlift r s hrs hreset
  · intro n hrn hns
    exact ⟨(hbefore n hrn hns).1, lt_of_le_of_lt (hbefore n hrn hns).2 (by norm_num)⟩
  · intro n hrn hns
    apply preparationCoeff_eq_zero_of_outside
    intro hn
    exact (not_lt_of_ge (hbefore n hrn hns).2) hn.1

theorem exists_concrete_zero_register_preparation_start
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) - t n ≤ 1)
    (r : ℕ) (hreset : t r ∈ Set.Icc 2 5) (hevent : ∃ n, 7 ≤ t n) :
    ∃ s, r + 1 ≤ s ∧ 7 ≤ t s ∧ t s < 8 ∧
      (∀ n, n < s → t n < 7) ∧ ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere) := by
  have hstart : t 0 < 7 := by
    have h := hmono (Nat.zero_le r)
    linarith [hreset.2]
  obtain ⟨s, hs7, hs8, hbefore⟩ :=
    ClockDynamics.exists_first_crossing hstart hstep hevent
  have hrs : r + 1 ≤ s := by
    by_contra h
    have hsr : s ≤ r := by omega
    have h := hmono hsr
    linarith [hreset.2]
  refine ⟨s, hrs, hs7, by norm_num at hs8 ⊢; exact hs8, hbefore, ?_⟩
  apply concreteMap_register_zero_at_preparation_start L hL x horbit t hlift r s hrs hreset
  intro n hrn hns
  have hrn' : r ≤ n := by omega
  have hlow := hmono hrn'
  have hhigh := hbefore n hns
  exact ⟨by linarith [hreset.1], by linarith⟩

end Problem340.Construction

end

end OAI
