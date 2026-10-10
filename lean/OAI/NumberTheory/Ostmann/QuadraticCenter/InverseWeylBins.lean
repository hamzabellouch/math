import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylPhase

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

noncomputable def weylBin (r : ℕ) (x : ℝ) : ℕ := ⌊2*(r:ℝ)*integerDistance x⌋₊
noncomputable def weylKey (r : ℕ) (x : ℝ) : Bool × ℕ :=
  (decide (0 ≤ x-(round x : ℤ)), weylBin r x)

theorem weylBin_le (r : ℕ) (x : ℝ) : weylBin r x ≤ r := by
  apply Nat.floor_le_of_le
  nlinarith [integerDistance_le_half x, (show (0:ℝ) ≤ r by positivity)]

theorem weylKey_injective_on {ι : Type*} (s : Finset ι) (theta : ι → ℝ)
    {r : ℕ} (hr : 0 < r)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ m : ℤ,
      1/(2*(r:ℝ)) ≤ |theta i-theta j-m|) :
    Set.InjOn (fun i => weylKey r (theta i)) s := by
  intro i hi j hj heq
  by_contra hij
  have hkey := congrArg Prod.fst heq
  have hbin := congrArg Prod.snd heq
  change decide (0 ≤ theta i-(round (theta i) : ℤ)) =
    decide (0 ≤ theta j-(round (theta j) : ℤ)) at hkey
  change weylBin r (theta i) = weylBin r (theta j) at hbin
  let yi := theta i-(round (theta i) : ℤ)
  let yj := theta j-(round (theta j) : ℤ)
  have hsign : (0 ≤ yi) ↔ (0 ≤ yj) := by
    simpa only [decide_eq_decide] using hkey
  have hi0 := Nat.floor_le (show 0 ≤ 2*(r:ℝ)*integerDistance (theta i) by
    exact mul_nonneg (by positivity) (integerDistance_nonneg _))
  have hj0 := Nat.floor_le (show 0 ≤ 2*(r:ℝ)*integerDistance (theta j) by
    exact mul_nonneg (by positivity) (integerDistance_nonneg _))
  have hi1 := Nat.lt_floor_add_one (2*(r:ℝ)*integerDistance (theta i))
  have hj1 := Nat.lt_floor_add_one (2*(r:ℝ)*integerDistance (theta j))
  change (weylBin r (theta i) : ℝ) ≤ 2*(r:ℝ)*|yi| at hi0
  change (weylBin r (theta j) : ℝ) ≤ 2*(r:ℝ)*|yj| at hj0
  change 2*(r:ℝ)*|yi| < (weylBin r (theta i) : ℝ)+1 at hi1
  change 2*(r:ℝ)*|yj| < (weylBin r (theta j) : ℝ)+1 at hj1
  rw [hbin] at hi0 hi1
  have hp : 0 < 2*(r:ℝ) := by positivity
  have hh := (div_le_iff₀ hp).mp
    (hsep i hi j hj hij (round (theta i)-round (theta j)))
  have he : theta i-theta j-((round (theta i)-round (theta j):ℤ):ℝ) = yi-yj := by
    dsimp [yi,yj]
    push_cast
    ring
  rw [he] at hh
  by_cases hyi : 0 ≤ yi
  · have hyj : 0 ≤ yj := hsign.mp hyi
    rw [abs_of_nonneg hyi] at hi0 hi1
    rw [abs_of_nonneg hyj] at hj0 hj1
    rcases le_total yi yj with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
      nlinarith
  · have hyj : yj < 0 := lt_of_not_ge (fun h => hyi (hsign.mpr h))
    rw [abs_of_neg (lt_of_not_ge hyi)] at hi0 hi1
    rw [abs_of_neg hyj] at hj0 hj1
    rcases le_total yi yj with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
      nlinarith

noncomputable def weylBinWeight (N : ℝ) (r k : ℕ) : ℝ :=
  if k=0 then N else (r:ℝ)/k

theorem le_weylBinWeight {N u x : ℝ} {r : ℕ} (hu : 0 ≤ u)
    (huN : u ≤ N) (hud : u*integerDistance x ≤ 1/2) :
    u ≤ weylBinWeight N r (weylBin r x) := by
  by_cases hk : weylBin r x = 0
  · simpa [weylBinWeight, hk] using huN
  · rw [weylBinWeight, ite_eq_right hk]
    have hkp : (0:ℝ) < weylBin r x := by exact_mod_cast Nat.pos_of_ne_zero hk
    apply (le_div_iff₀ hkp).mpr
    have hfloor := Nat.floor_le (show 0 ≤ 2*(r:ℝ)*integerDistance x by
      exact mul_nonneg (by positivity) (integerDistance_nonneg _))
    change (weylBin r x : ℝ) ≤ 2*(r:ℝ)*integerDistance x at hfloor
    have hm := mul_le_mul_of_nonneg_left hfloor hu
    have hd := mul_le_mul_of_nonneg_left hud (show 0 ≤ 2*(r:ℝ) by positivity)
    nlinarith only [hm,hd]

theorem weylBinWeight_sum (N : ℝ) (r : ℕ) :
    ∑ k ∈ range (r+1), weylBinWeight N r k = N+(r:ℝ)*(harmonic r:ℝ) := by
  rw [sum_range_succ']
  simp only [weylBinWeight, Nat.succ_ne_zero, ite_false, ite_true]
  rw [add_comm]
  congr 1
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
    mul_sum, div_eq_mul_inv]

theorem separated_linear_sum_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (theta u : ι → ℝ) {r : ℕ} (hr : 0 < r) {N : ℝ} (hN : 0 ≤ N)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ m : ℤ,
      1/(2*(r:ℝ)) ≤ |theta i-theta j-m|)
    (hu : ∀ i ∈ s, 0 ≤ u i)
    (huN : ∀ i ∈ s, u i ≤ N)
    (hud : ∀ i ∈ s, u i*integerDistance (theta i) ≤ 1/2) :
    ∑ i ∈ s, u i ≤ 2*N+2*(r:ℝ)*(harmonic r:ℝ) := by
  classical
  let w : Bool × ℕ → ℝ := fun k => weylBinWeight N r k.2
  have hsub : s.image (fun i => weylKey r (theta i)) ⊆
      (univ : Finset Bool) ×ˢ range (r+1) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_univ _, mem_range.mpr (Nat.lt_succ_of_le (weylBin_le r _))⟩
  calc
    _ ≤ ∑ i ∈ s, w (weylKey r (theta i)) :=
      sum_le_sum (fun i hi => le_weylBinWeight (hu i hi) (huN i hi) (hud i hi))
    _ = ∑ k ∈ s.image (fun i => weylKey r (theta i)), w k :=
      (sum_image (weylKey_injective_on s theta hr hsep)).symm
    _ ≤ ∑ k ∈ (univ : Finset Bool) ×ˢ range (r+1), w k := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro k hk _
      dsimp [w, weylBinWeight]
      split_ifs <;> positivity
    _ = _ := by
      rw [sum_product]
      simp only [w, weylBinWeight_sum]
      simp
      ring

end Ostmann.QuadraticCenter

end OAI
