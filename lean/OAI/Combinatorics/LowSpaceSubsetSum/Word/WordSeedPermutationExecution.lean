import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedRangeInitialization

namespace OAI

/-! # Measured permutation seed generation

Each range call computes its modulus, draws and retains the actual candidate
tuple, and caches its accepted digit. Permutation values are composition
closures; their application or array materialization remains a separate
measured operation, as in `PermutationArray`.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

def permutation (w n : ℕ) : (k : ℕ) → (hw : Nat.clog 2 k ≤ w) →
    Execution (WordSeedRealization.permutation w n k hw)
  | 0, _ => by
      exact reprogram (pure (w := w) (Equiv.refl (Fin 0))) (by
        unfold WordSeedRealization.permutation
        exact mpr_program (Nat.zero_mul (n^3)) _)
  | k+1, hw => by
      have hk : Nat.clog 2 k ≤ w :=
        (Nat.clog_mono_right 2 (by omega : k ≤ k+1)).trans hw
      exact reprogram
        (map (prod (fin w n (k+1) hw) (permutation w n k hk))
          Equiv.Perm.decomposeFin.symm
          (fun p => ((Equiv.Perm.decomposeFin.symm p,6),8)) (fun _ => rfl)) (by
            conv_lhs => rw [WordSeedRealization.permutation]
            exact mpr_program (w := w) (α := Equiv.Perm (Fin (k+1)))
              (by simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm] :
                (k+1)*n^3 = n^3+k*n^3) _)

theorem permutation_bounded (w n : ℕ) : ∀ (k : ℕ) (hw : Nat.clog 2 k ≤ w),
    (permutation w n k hw).Bounded
      (k*(13*n^3+5*k+64)+1) ((k+1)*(2*n^3+256)) ((k+1)*(n^3+64)) := by
  intro k
  induction k with
  | zero =>
    intro hw stream cursor
    change 1 ≤ _ ∧ 4 ≤ _ ∧ 4 ≤ _
    constructor
    · omega
    · constructor <;> omega
  | succ k ih =>
    intro hw
    have hk : Nat.clog 2 k ≤ w :=
      (Nat.clog_mono_right 2 (by omega : k ≤ k+1)).trans hw
    have ht := ih hk
    have hf := fin_bounded w n (k+1) hw
    have hp := prod_bounded (fin w n (k+1) hw) (permutation w n k hk)
      _ _ _ _ _ _ hf ht
    have hm := map_bounded _ Equiv.Perm.decomposeFin.symm
      (fun p => ((Equiv.Perm.decomposeFin.symm p,6),8)) (fun _ => rfl)
      _ _ _ 6 8 hp (fun _ => le_rfl) (fun _ => le_rfl)
    have hclog : Nat.clog 2 (k+1) ≤ k+1 :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    intro stream cursor
    have h := hm stream cursor
    change _ ≤ (k+1)*(13*n^3+5*(k+1)+64)+1 ∧
      _ ≤ (k+1+1)*(2*n^3+256) ∧ _ ≤ (k+1+1)*(n^3+64)
    refine ⟨h.1.trans (by nlinarith),h.2.1.trans ?_,h.2.2.trans (by nlinarith)⟩
    apply max_le
    · apply max_le
      · apply max_le <;> nlinarith
      · nlinarith
    · nlinarith

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
