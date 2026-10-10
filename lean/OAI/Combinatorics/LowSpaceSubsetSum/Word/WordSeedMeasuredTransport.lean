import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasuredProduct
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimitives

namespace OAI

/-! # Proof-only transport for the conditional seed programs

The source sampler uses dependent decidable recursors. These lemmas expose
which conditional program is selected, preserving its probability law.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

private theorem rec_heq_pos {p : Prop} (h : p) {C : Decidable p → Sort*}
    (f : ∀ h : ¬p,C (.isFalse h)) (g : ∀ h : p,C (.isTrue h)) (d : Decidable p) :
    HEq (@Decidable.rec p C f g d) (g h) := by
  cases d with
  | isFalse hh => exact False.elim (hh h)
  | isTrue hh => rfl

private theorem rec_heq_neg {p : Prop} (h : ¬p) {C : Decidable p → Sort*}
    (f : ∀ h : ¬p,C (.isFalse h)) (g : ∀ h : p,C (.isTrue h)) (d : Decidable p) :
    HEq (@Decidable.rec p C f g d) (f h) := by
  cases d with
  | isFalse hh => rfl
  | isTrue hh => exact False.elim (h hh)

def transportSampler {w N : ℕ} {α : Type} [Fintype α] {S T : SamplerCoupling α}
    {X : Realization w N S} {Y : Realization w N T} (hS : T = S)
    (hX : HEq Y X) (E : Execution X) : Execution Y := by
  subst T
  cases eq_of_heq hX
  exact E

theorem transportSampler_bounded {w N : ℕ} {α : Type} [Fintype α]
    {S T : SamplerCoupling α} {X : Realization w N S} {Y : Realization w N T}
    (hS : T = S) (hX : HEq Y X) (E : Execution X) (W C R : ℕ)
    (hE : E.Bounded W C R) : (transportSampler hS hX E).Bounded W C R := by
  subst T
  cases eq_of_heq hX
  exact hE

theorem bounded_mono {w N : ℕ} {α : Type} [Fintype α] {S : SamplerCoupling α}
    {X : Realization w N S} (E : Execution X) {W C R V D Q : ℕ}
    (h : E.Bounded W C R) (hW : W ≤ V) (hC : C ≤ D) (hR : R ≤ Q) :
    E.Bounded V D Q := fun stream cursor =>
  ⟨(h stream cursor).1.trans hW,(h stream cursor).2.1.trans hC,
    (h stream cursor).2.2.trans hR⟩

theorem source_fin_pos (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) (h : 1 < D) :
    HEq (WordSeedRealization.fin w n D hw) (WordSeedRealization.range w n D h hw) := by
  unfold WordSeedRealization.fin
  dsimp only [id_eq]
  exact (rec_heq_pos h _ _ _).trans (cast_heq _ _)

theorem source_fin_neg (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) (h : ¬1 < D) :
    HEq (WordSeedRealization.fin w n D hw)
      (WordSeedRealization.enlarge (WordSeedRealization.pure (w := w)
        (⟨0,Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D)) (Nat.zero_le (n^3))) := by
  unfold WordSeedRealization.fin
  dsimp only [id_eq]
  exact (rec_heq_neg h _ _ _).trans (cast_heq _ _)

theorem source_factor_small (w n ell : ℕ) (hw : ell ≤ w) (h : ell < 4) :
    HEq (WordSeedRealization.factor w n ell hw)
      (WordSeedRealization.enlarge (WordSeedRealization.map
        (WordSeedRealization.pure (w := w) ()) (factorOneEquiv h)) (Nat.zero_le (n^3))) := by
  unfold WordSeedRealization.factor
  dsimp only [id_eq]
  exact (rec_heq_pos h _ _ _).trans (cast_heq _ _)

theorem source_factor_large (w n ell : ℕ) (hw : ell ≤ w) (h : ¬ell < 4) :
    HEq (WordSeedRealization.factor w n ell hw)
      (WordSeedRealization.map (WordSeedRealization.prime w n ell (by omega) hw)
        (factorPrimeEquiv (by omega))) := by
  unfold WordSeedRealization.factor
  dsimp only [id_eq]
  exact (rec_heq_neg h _ _ _).trans (cast_heq _ _)

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
