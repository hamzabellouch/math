import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Defs.PartialOrder
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

structure FinitePartitionFiltration (Ω : Type*) where
  part : ℕ → Setoid Ω
  refines : ∀ {m n : ℕ}, m ≤ n → ∀ {ω η : Ω},
    (part n).r ω η → (part m).r ω η

namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

def IsStoppingTime (τ : Ω → ℕ) : Prop :=
  ∀ n : ℕ, ∀ {ω η : Ω}, (F.part n).r ω η → (τ ω ≤ n ↔ τ η ≤ n)

def IsPredictableTime (τ : Ω → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ {ω η : Ω},
    (F.part (n - 1)).r ω η → (τ ω = n ↔ τ η = n)

def AdaptedAt {V : Type*} (n : ℕ) (f : Ω → V) : Prop :=
  ∀ {ω η : Ω}, (F.part n).r ω η → f ω = f η

theorem adaptedAt_mono {V : Type*} {m n : ℕ} {f : Ω → V}
    (hmn : m ≤ n) (hf : F.AdaptedAt m f) : F.AdaptedAt n f := by
  intro ω η hωη
  exact hf (F.refines hmn hωη)

theorem isStoppingTime_const (n : ℕ) : F.IsStoppingTime (fun _ => n) := by
  intro m ω η hωη
  rfl

theorem isStoppingTime_of_isPredictableTime {τ : Ω → ℕ}
    (hpos : ∀ ω, 0 < τ ω) (hτ : F.IsPredictableTime τ) :
    F.IsStoppingTime τ := by
  intro n ω η hωη
  constructor
  · intro hle
    have hrel : (F.part (τ ω - 1)).r ω η :=
      F.refines ((Nat.sub_le (τ ω) 1).trans hle) hωη
    have heq : τ η = τ ω := (hτ (τ ω) (hpos ω) hrel).mp rfl
    simpa only [heq] using hle
  · intro hle
    have hrel : (F.part (τ η - 1)).r η ω :=
      F.refines ((Nat.sub_le (τ η) 1).trans hle) ((F.part n).symm' hωη)
    have heq : τ ω = τ η := (hτ (τ η) (hpos η) hrel).mp rfl
    simpa only [heq] using hle

def stoppedSetoid (τ : Ω → ℕ) : Setoid Ω where
  r ω η := τ ω = τ η ∧ (F.part (τ ω)).r ω η
  iseqv := {
    refl := fun ω => ⟨rfl, (F.part (τ ω)).refl' ω⟩
    symm := by
      intro ω η h
      refine ⟨h.1.symm, ?_⟩
      rw [← h.1]
      exact (F.part (τ ω)).symm' h.2
    trans := by
      intro ω η ξ hωη hηξ
      refine ⟨hωη.1.trans hηξ.1, ?_⟩
      have hηξ' : (F.part (τ ω)).r η ξ := by
        rw [hωη.1]
        exact hηξ.2
      exact (F.part (τ ω)).trans' hωη.2 hηξ' }

theorem stopped_rel_of_rel_of_le {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    {n : ℕ} {ω η : Ω} (hωη : (F.part n).r ω η) (hω : τ ω ≤ n) :
    (F.stoppedSetoid τ).r ω η := by
  have hη : τ η ≤ n := (hτ n hωη).mp hω
  have hrelω : (F.part (τ ω)).r ω η := F.refines hω hωη
  have hrelη : (F.part (τ η)).r ω η := F.refines hη hωη
  have hηω : τ η ≤ τ ω := (hτ (τ ω) hrelω).mp le_rfl
  have hωηtime : τ ω ≤ τ η := (hτ (τ η) hrelη).mpr le_rfl
  exact ⟨Nat.le_antisymm hωηtime hηω, hrelω⟩

theorem stoppedSetoid_refines {τ σ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    (hle : ∀ ω, τ ω ≤ σ ω) {ω η : Ω}
    (hωη : (F.stoppedSetoid σ).r ω η) :
    (F.stoppedSetoid τ).r ω η :=
  F.stopped_rel_of_rel_of_le hτ hωη.2 (hle ω)

theorem adapted_stopped {V : Type*} (M : ℕ → Ω → V)
    (hM : ∀ n, F.AdaptedAt n (M n)) (τ : Ω → ℕ) {ω η : Ω}
    (hωη : (F.stoppedSetoid τ).r ω η) :
    M (τ ω) ω = M (τ η) η := by
  rw [← hωη.1]
  exact hM (τ ω) hωη.2

theorem stopped_atom_and_predictable_eq {τ σ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hσ : F.IsPredictableTime σ)
    (a : Ω) {n : ℕ} (hn : 0 < n)
    (hstrict : ∀ ω, σ ω = n → τ ω < n)
    {ω η : Ω} (hωη : (F.part (n - 1)).r ω η) :
    ((F.stoppedSetoid τ).r ω a ∧ σ ω = n) ↔
      ((F.stoppedSetoid τ).r η a ∧ σ η = n) := by
  have hstep (u v : Ω) (huv : (F.part (n - 1)).r u v)
      (hu : (F.stoppedSetoid τ).r u a ∧ σ u = n) :
      (F.stoppedSetoid τ).r v a ∧ σ v = n := by
    have hv : σ v = n := (hσ n hn huv).mp hu.2
    have htime : τ u ≤ n - 1 := by
      have := hstrict u hu.2
      omega
    have hstop : (F.stoppedSetoid τ).r u v :=
      F.stopped_rel_of_rel_of_le hτ huv htime
    exact ⟨(F.stoppedSetoid τ).trans' ((F.stoppedSetoid τ).symm' hstop) hu.1, hv⟩
  exact ⟨hstep ω η hωη, hstep η ω ((F.part (n - 1)).symm' hωη)⟩

end FinitePartitionFiltration

end MarkovSuperreflexivity

end OAI
