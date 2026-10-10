import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMaskExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.ComputedSeparatorFamilies

namespace OAI

/-! # Measured independent separator-family draws

The inner loop bounds are supplied as explicit integer parameters. The
application wrapper obtains these integers from `SeparatorParameterExecution`.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {g : ℕ}

def families (S : SeparatorExpectation.RoundedParameters g)
    (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.families S w n hw) :=
  pi w (11*2^g*(g*n^3)) 4 _ _ _ (fun i =>
    enlarge (pi w (g*n^3) (S.counts i) _ _ _
      (fun _ => fixedSize w n g (S.e i) (S.size_le i) hw))
      (Nat.mul_le_mul_right _ (S.counts_le i)))

def familyUsing (S : SeparatorExpectation.RoundedParameters g) (i : Fin 4)
    (size count : ℕ) (hs : size = S.e i) (hc : count = S.counts i)
    (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.enlarge
      (WordSeedRealization.pi w (g*n^3) (S.counts i) _ _
        (fun _ => WordSeedRealization.fixedSize w n g (S.e i) (S.size_le i) hw))
      (Nat.mul_le_mul_right _ (S.counts_le i))) := by
  have hsize : size ≤ g := by rw [hs]; exact S.size_le i
  have hcount : count ≤ 11*2^g := by rw [hc]; exact S.counts_le i
  let actual := enlarge (pi w (g*n^3) count _ _ _
    (fun _ => fixedSize w n g size hsize hw)) (Nat.mul_le_mul_right _ hcount)
  cases hs
  cases hc
  exact actual

def familiesUsing (S : SeparatorExpectation.RoundedParameters g)
    (sizes counts : Fin 4 → ℕ) (hs : ∀ i, sizes i = S.e i)
    (hc : ∀ i, counts i = S.counts i) (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.families S w n hw) :=
  pi w (11*2^g*(g*n^3)) 4 _ _ _
    (fun i => familyUsing S i (sizes i) (counts i) (hs i) (hc i) w n hw)

def maskBudget (n g : ℕ) : ℕ :=
  (g*(14*n^3+5*g+68)+10*(g+1)^2+11)+10*(g+1)*(n^3+256)+100

theorem fixedSize_budget (w n g k : ℕ) (hk : k ≤ g) (hw : Nat.clog 2 g ≤ w) :
    (fixedSize w n g k hk hw).Bounded (maskBudget n g) (maskBudget n g) (maskBudget n g) := by
  intro stream cursor
  have h := fixedSize_bounded w n g k hk hw stream cursor
  unfold maskBudget
  exact ⟨h.1.trans (by omega),h.2.1.trans (by omega),h.2.2.trans (by omega)⟩

theorem families_bounded (S : SeparatorExpectation.RoundedParameters g)
    (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    (families S w n hw).Bounded
      (100*(11*2^g+1)*(maskBudget n g+100))
      (100*(11*2^g+1)*(maskBudget n g+100))
      (100*(11*2^g+1)*(maskBudget n g+100)) := by
  let F := 11*2^g
  let B := maskBudget n g
  have hi (i : Fin 4) :
      (enlarge (pi w (g*n^3) (S.counts i) _ _ _
        (fun _ => fixedSize w n g (S.e i) (S.size_le i) hw))
        (Nat.mul_le_mul_right _ (S.counts_le i))).Bounded
        ((F+1)*(2*B+100)) ((F+1)*(2*B+100)) ((F+1)*(2*B+100)) := by
    have h := pi_bounded w (g*n^3) (S.counts i) _ _ _ _ B B B
      (fun _ => fixedSize_budget w n g (S.e i) (S.size_le i) hw)
    intro stream cursor
    have ht := h stream cursor
    have hc := S.counts_le i
    change S.counts i ≤ F at hc
    change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
    refine ⟨ht.1.trans ?_,ht.2.1.trans ?_,ht.2.2.trans ?_⟩ <;> nlinarith
  have h := pi_bounded w (11*2^g*(g*n^3)) 4 _ _ _ _
    ((F+1)*(2*B+100)) ((F+1)*(2*B+100)) ((F+1)*(2*B+100)) hi
  intro stream cursor
  have ht := h stream cursor
  change _ ≤ 100*(F+1)*(B+100) ∧ _ ≤ 100*(F+1)*(B+100) ∧ _ ≤ 100*(F+1)*(B+100)
  refine ⟨ht.1.trans ?_,ht.2.1.trans ?_,ht.2.2.trans ?_⟩ <;> nlinarith

theorem familiesUsing_bounded (S : SeparatorExpectation.RoundedParameters g)
    (sizes counts : Fin 4 → ℕ) (hs : ∀ i, sizes i = S.e i)
    (hc : ∀ i, counts i = S.counts i) (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    (familiesUsing S sizes counts hs hc w n hw).Bounded
      (100*(11*2^g+1)*(maskBudget n g+100))
      (100*(11*2^g+1)*(maskBudget n g+100))
      (100*(11*2^g+1)*(maskBudget n g+100)) := by
  have he : sizes = S.e := funext hs
  have hm : counts = S.counts := funext hc
  subst sizes
  subst counts
  simpa only [familiesUsing,familyUsing,families] using families_bounded S w n hw

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
