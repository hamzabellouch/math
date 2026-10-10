import OAI.Probability.InvariantIsing.Cavity.CavityAffineRetained

namespace OAI

/-! Endpoint limits and uniform positive proportions for affine block counts. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityAffineStart_alternative {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    (∀ r, cavityOrderedStart (cavityAffineCount s c q r) a=0) ∨
      Tendsto (fun r => cavityOrderedStart (cavityAffineCount s c q r) a) atTop atTop := by
  by_cases ha : a.val=0
  · left
    intro r
    have hz : IsEmpty (Fin a) := ⟨fun i => by have hi := i.isLt; omega⟩
    simp only [cavityOrderedStart]
    exact Finset.sum_eq_zero (fun i _ => isEmptyElim i)
  · right
    have hp : 0 < cavityOrderedStart s a := by
      let i : Fin a := ⟨0,by omega⟩
      have hh := Finset.single_le_sum (f := fun i : Fin a => s (Fin.castLE a.isLt.le i))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact (hs (Fin.castLE a.isLt.le i)).trans_le hh
    apply tendsto_atTop_mono _ (cavityRationalDimension_tendsto (cavityOrderedStart s a) q hp)
    intro r
    rw [cavityAffineStart]
    exact Nat.le_add_right _ _

lemma cavityAffineEnd_tendsto {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityOrderedStart (cavityAffineCount s c q r) a+
      cavityAffineCount s c q r a) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) (cavityAffineCount_tendsto s c hs q a)

lemma cavityAffineFullStart_ratio {m n q : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityOrderedStart (cavityAffineCount s c q (r+1)) a : ℝ)/
      (cavityAffineSize n q c r+n)) atTop (𝓝 ((cavityOrderedStart s a : ℝ)/n)) := by
  have h := (cavityAffineStart_ratio s c hn hq a).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, cavityAffineSize_succ, Nat.cast_add] using h

lemma cavityAffineFullEnd_ratio {m n q : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => ((cavityOrderedStart (cavityAffineCount s c q (r+1)) a+
      cavityAffineCount s c q (r+1) a : ℕ) : ℝ)/(cavityAffineSize n q c r+n)) atTop
      (𝓝 (((cavityOrderedStart s a+s a : ℕ) : ℝ)/n)) := by
  have h := (cavityAffineEnd_ratio s c hn hq a).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, cavityAffineSize_succ, Nat.cast_add] using h

lemma cavityAffineFullWindow_size {m n q : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hq : n ≤ q) (r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityAffineCount s c q (r+1)) a+n ≤
      cavityOrderedStart (cavityAffineCount s c q (r+1)) a+cavityAffineCount s c q (r+1) a := by
  apply Nat.add_le_add_left
  have hh := Nat.le_mul_of_pos_right (r+1+q) (hs a)
  dsimp only [cavityAffineCount,cavityRationalCount]
  omega

lemma cavityAffineMass_lower {m n q : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hn : 0 < n) (hq : 0 < q) (r : ℕ) (a : Fin m) :
    (1 : ℝ)/(n+∑ a, c a : ℕ) ≤
      (cavityAffineCount s c q r a : ℝ)/cavityAffineSize n q c r := by
  have hr : 0 < r+q := by omega
  have hdim : r+q ≤ cavityAffineCount s c q r a :=
    (Nat.le_mul_of_pos_right _ (hs a)).trans (Nat.le_add_right _ _)
  have hc : (∑ a, c a) ≤ (r+q)*(∑ a, c a) := Nat.le_mul_of_pos_left _ hr
  have hineq : cavityAffineSize n q c r ≤ cavityAffineCount s c q r a*(n+∑ a, c a) := by
    calc
      _ ≤ (r+q)*n+(r+q)*(∑ a, c a) := Nat.add_le_add_left hc _
      _ = (r+q)*(n+∑ a, c a) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hdim
  have hsize : 0 < cavityAffineSize n q c r := by
    dsimp only [cavityAffineSize]
    positivity
  apply (div_le_div_iff₀ (by exact_mod_cast (show 0 < n+∑ a, c a by omega))
    (by exact_mod_cast hsize)).mpr
  simpa only [one_mul, Nat.cast_mul] using (show (cavityAffineSize n q c r : ℝ) ≤
    ((cavityAffineCount s c q r a*(n+∑ a, c a) : ℕ) : ℝ) by exact_mod_cast hineq)

end InvariantIsing

end

end OAI
