import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedBind

namespace OAI

/-! # Adding the seven sequential generation stages without inflating exponents -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

variable {w N M : ℕ} {α : Type} [Fintype α]

/-- Each completed stage releases scratch space and retains its bounded seed. -/
def Budgeted {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (B D k : ℕ) : Prop :=
  E.Bounded (k*(B+2)) (k*(D+8)) (k*(D+8))

theorem budgeted_one {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (B D : ℕ) (h : E.Bounded B D D) : Budgeted E B D 1 := by
  intro stream cursor
  have hh := h stream cursor
  exact ⟨by simpa only [Nat.one_mul] using hh.1.trans (Nat.le_add_right B 2),
    by simpa only [Nat.one_mul] using hh.2.1.trans (Nat.le_add_right D 8),
    by simpa only [Nat.one_mul] using hh.2.2.trans (Nat.le_add_right D 8)⟩

theorem budgeted_bind {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (A : α → Type) [∀ a, Fintype (A a)]
    (T : ∀ a, SamplerCoupling (A a)) (Y : ∀ a, Realization w M (T a))
    (F : ∀ a, Execution (Y a)) (B D k : ℕ) (hE : Budgeted E B D k)
    (hF : ∀ a, (F a).Bounded B D D) :
    Budgeted (bind E A T Y F) B D (k+1) := by
  have h := bind_bounded E A T Y F _ _ _ _ _ _ hE hF
  intro stream cursor
  have hh := h stream cursor
  refine ⟨hh.1.trans (by nlinarith),hh.2.1.trans ?_,hh.2.2.trans (by nlinarith)⟩
  exact max_le (by nlinarith) (by nlinarith)

theorem budgeted_bindSeed {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (A : α → Type) [∀ a, Fintype (A a)]
    (T : ∀ a, SamplerCoupling (A a)) (Y : ∀ a, Realization w M (T a))
    (F : ∀ a : Accepted S, Execution (Y a.value)) (B D k : ℕ) (hE : Budgeted E B D k)
    (hF : ∀ a, (F a).Bounded B D D) :
    Budgeted (bindSeed E A T Y F) B D (k+1) := by
  have h := bindSeed_bounded E A T Y F _ _ _ _ _ _ hE hF
  intro stream cursor
  have hh := h stream cursor
  refine ⟨hh.1.trans (by nlinarith),hh.2.1.trans ?_,hh.2.2.trans (by nlinarith)⟩
  exact max_le (by nlinarith) (by nlinarith)

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
