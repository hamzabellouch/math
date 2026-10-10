import OAI.Combinatorics.BinaryEdit.FiniteL1Tree
import OAI.Combinatorics.BinaryEdit.FiniteWordDetection
import OAI.Combinatorics.BinaryEdit.FiniteTreeCostTheorem

namespace OAI

/-!
# The actual finite word's averaged ℓ₁ displacement

This specializes the proved finite-group Fourier obstruction to the concrete
cyclic parameter space and recursive word evaluator. The only metric input is
that the chosen map into actual ℓ₁ does not expand ordinary edit distance.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

open Classical
open scoped BigOperators

/-- The leaf cyclic tests have the required pointwise cost for every map
which is nonexpanding on pairs of actual finite words. -/
theorem finiteWord_leaf_l1_cost {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ T k [] x) (finiteWord p i₀ T k [] y) : ℝ))
    (a : Fin k → Fin m) [NeZero (FiniteVectors.leafPeriod p a)]
    (z : ZMod (FiniteVectors.leafPeriod p a)) (x : State (wordPeriods p)) :
    ‖F (x + wordLeafCoordinate p a z) - F x‖ ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  rw [norm_sub_rev]
  apply (hF x (x + wordLeafCoordinate p a z)).trans
  rw [wordLeafCoordinate_eq_val_zsmul p i₀]
  exact finiteWord_leaf_translation_cost p i₀ T
    ⟨List.ofFn a, List.length_ofFn⟩ z.val x

/-- The actual finite word satisfies the full Fourier root estimate. All
leaf costs and sparse-node tests are proved from its concrete construction. -/
theorem finiteWord_root_mean_bound {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (hk : 1 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    (T : ℕ) (hT : 0 < T) (hJT : 4 * k ^ (10 * k) ≤ T)
    [Fintype (State (wordPeriods p))]
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ T k [] x) (finiteWord p i₀ T k [] y) : ℝ)) :
    (𝔼 x : State (wordPeriods p), ‖F (x + wordW p i₀ []) - F x‖) ≤
      4 * ((k : ℝ) * ((2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) *
        ((m * T : ℕ) : ℝ) ^ k) +
        ((m * T : ℕ) : ℝ) ^ k / (2 * (k : ℝ) ^ k)) := by
  let : ∀ f : Fin k → Fin m, NeZero (FiniteVectors.leafPeriod p f) :=
    fun f => ⟨ne_of_gt (FiniteVectors.leafPeriod_pos p hppos f)⟩
  have hJpos : 0 < 4 * k ^ (10 * k) := by positivity
  let : Nonempty (Fin (4 * k ^ (10 * k))) := ⟨⟨0, hJpos⟩⟩
  let shift : FiniteActivity.InternalNode (Fin m) k → Fin (4 * k ^ (10 * k)) →
      State (wordPeriods p) := fun v s => (s.val + 1) • wordU p i₀ (List.ofFn v.2)
  have hm : m ≠ 0 := by have hi := i₀.isLt; omega
  apply FiniteActivity.finite_tree_l1_mean_bound m k k hm (by omega)
    (wordW p i₀) (FiniteVectors.leafPeriod p) (wordLeafCoordinate p)
    (fun f => (wordLeafCoordinate_one p i₀ f).symm) F shift
    (((m * T : ℕ) : ℝ) ^ k)
    ((2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) * ((m * T : ℕ) : ℝ) ^ k)
  · intro f z x
    exact finiteWord_leaf_l1_cost p i₀ T F hF f z x
  · intro v χ hv
    simpa only [Fintype.card_fin] using word_sparse_detection p i₀ hk hppos hp v χ hv
  · intro v s x
    have hs : s.val + 1 ≤ 4 * k ^ (10 * k) := Nat.succ_le_of_lt s.isLt
    have hsR : ((s.val + 1 : ℕ) : ℝ) ≤ ((4 * k ^ (10 * k) : ℕ) : ℝ) :=
      by exact_mod_cast hs
    have hcost := finiteWord_node_translation_cost p i₀ T hT (List.ofFn v.2)
      (by simp) (s.val + 1) (hs.trans hJT) x
    simp only [List.length_ofFn] at hcost
    rw [norm_sub_rev]
    apply (hF x (x + shift v s)).trans
    calc
      _ ≤ (2 * ((s.val + 1 : ℕ) : ℝ) / T) *
          (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ v.1.val) := hcost
      _ ≤ (2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) *
          (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ v.1.val) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsR (by norm_num)) (Nat.cast_nonneg T)
      _ = _ := by ring

/-- The source parameter choice gives the explicit `34 M/k^k` averaged
root bound for every nonexpanding map of the actual constructed word image. -/
theorem finiteWord_root_mean_bound34 {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (hk : 2 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    [Fintype (State (wordPeriods p))]
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ (k ^ (20 * k)) k [] x)
        (finiteWord p i₀ (k ^ (20 * k)) k [] y) : ℝ)) :
    (𝔼 x : State (wordPeriods p), ‖F (x + wordW p i₀ []) - F x‖) ≤
      34 * ((m * k ^ (20 * k) : ℕ) : ℝ) ^ k / (k : ℝ) ^ k := by
  apply FiniteActivity.source_mean_bound34 F (wordW p i₀ []) (by omega) (by positivity)
  have hroot := finiteWord_root_mean_bound p i₀ (by omega) hppos hp
    (k ^ (20 * k)) (by positivity) (FiniteNumeric.averaging_length_le_rows hk) F hF
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hroot

end TreeEdit.BinaryLower.FiniteTree

end

end OAI
