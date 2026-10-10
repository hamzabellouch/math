import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasured

namespace OAI

/-! # Measured products and finite families of seed generators -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

variable {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]

/-- Changing a certified read bound preserves the executed program. -/
theorem mpr_program {S : SamplerCoupling α} (h : M = N) (X : Realization w N S) :
    (Eq.mpr (congrArg (fun j => Realization w j S) h) X).program = X.program := by
  cases h
  rfl

/-- Transport only the proof-facing program index, leaving the executed result intact. -/
def reprogram {S : SamplerCoupling α} {X : Realization w N S}
    {Y : Realization w M S} (E : Execution X) (h : Y.program = X.program) :
    Execution Y where
  run := E.run
  value stream cursor := by rw [h]; exact E.value stream cursor

def enlarge {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (h : N ≤ M) : Execution (WordSeedRealization.enlarge X h) where
  run := E.run
  value := E.value

theorem enlarge_bounded {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (h : N ≤ M) (W C R : ℕ) (hE : E.Bounded W C R) :
    (enlarge E h).Bounded W C R := hE

def prod {S : SamplerCoupling α} {T : SamplerCoupling β}
    {X : Realization w N S} {Y : Realization w M T}
    (E : Execution X) (F : Execution Y) : Execution (WordSeedRealization.prod X Y) :=
  map (bind E (fun _ => β) (fun _ => T) (fun _ => Y) (fun _ => F))
    (Equiv.sigmaEquivProd α β)
    (fun p => (((Equiv.sigmaEquivProd α β) p,1),2)) (fun _ => rfl)

theorem prod_bounded {S : SamplerCoupling α} {T : SamplerCoupling β}
    {X : Realization w N S} {Y : Realization w M T}
    (E : Execution X) (F : Execution Y) (W C R V D Q : ℕ)
    (hE : E.Bounded W C R) (hF : F.Bounded V D Q) :
    (prod E F).Bounded (W+V+5)
      (max (max C (R+D+8)) (R+Q+18)) (R+Q+18) := by
  have h := map_bounded
    (bind E (fun _ => β) (fun _ => T) (fun _ => Y) (fun _ => F))
    (Equiv.sigmaEquivProd α β)
    (fun p => (((Equiv.sigmaEquivProd α β) p,1),2)) (fun _ => rfl)
    _ _ _ 1 2 (bind_bounded E _ _ _ _ W C R V D Q hE (fun _ => hF))
    (fun _ => le_rfl) (fun _ => le_rfl)
  have hw : W+V+2+1+2 = W+V+5 := by omega
  have hr : R+Q+8+2+8 = R+Q+18 := by omega
  simpa only [prod,Execution.Bounded,SamplerCoupling.prod,WordSeedRealization.prod,hw,hr] using h

def pi (w N : ℕ) : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (S : ∀ i, SamplerCoupling (A i)) → (X : ∀ i, Realization w N (S i)) →
    (∀ i, Execution (X i)) → Execution (WordSeedRealization.pi w N k A S X)
  | 0, A, _, _, _, _ => by
      exact reprogram (pure (w := w) (fun i : Fin 0 => (Fin.elim0 i : A i))) (by
        unfold WordSeedRealization.pi
        exact mpr_program (Nat.zero_mul N) _)
  | k+1, A, _, S, X, E => by
    let tail := pi w N k (fun i => A i.succ) (fun i => S i.succ)
      (fun i => X i.succ) (fun i => E i.succ)
    exact reprogram (map (prod (E 0) tail) (Fin.consEquiv A)
      (fun p => (((Fin.consEquiv A) p,2),4)) (fun _ => rfl)) (by
        conv_lhs => rw [WordSeedRealization.pi]
        exact mpr_program (w := w) (α := ∀ i, A i)
          (by simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm] : (k+1)*N = N+k*N) _)

theorem pi_bounded (w N : ℕ) : ∀ (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    (S : ∀ i, SamplerCoupling (A i)) (X : ∀ i, Realization w N (S i))
    (E : ∀ i, Execution (X i)) (W C R : ℕ),
    (∀ i, (E i).Bounded W C R) →
    (pi w N k A S X E).Bounded (k*(W+10)+1)
      ((k+1)*(C+R+64)) ((k+1)*(R+32)) := by
  intro k
  induction k with
  | zero =>
    intro A _ S X E W C R hE stream cursor
    change 1 ≤ _ ∧ 4 ≤ _ ∧ 4 ≤ _
    constructor
    · omega
    · constructor <;> nlinarith
  | succ k ih =>
    intro A _ S X E W C R hE
    have ht := ih (fun i => A i.succ) (fun i => S i.succ) (fun i => X i.succ)
      (fun i => E i.succ) W C R (fun i => hE i.succ)
    have hp := prod_bounded (E 0)
      (pi w N k (fun i => A i.succ) (fun i => S i.succ)
        (fun i => X i.succ) (fun i => E i.succ))
      W C R _ _ _ (hE 0) ht
    have hm := map_bounded _ (Fin.consEquiv A)
      (fun p => (((Fin.consEquiv A) p,2),4)) (fun _ => rfl)
      _ _ _ 2 4 hp (fun _ => le_rfl) (fun _ => le_rfl)
    intro stream cursor
    have h := hm stream cursor
    change _ ≤ (k+1)*(W+10)+1 ∧
      _ ≤ (k+1+1)*(C+R+64) ∧ _ ≤ (k+1+1)*(R+32)
    refine ⟨h.1.trans (by nlinarith),h.2.1.trans ?_,h.2.2.trans (by nlinarith)⟩
    apply max_le
    · apply max_le
      · apply max_le <;> nlinarith
      · nlinarith
    · nlinarith

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
