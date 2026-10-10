import Mathlib
import OAI.Computability.VertexCover.PCP.ZigzagSpectral
import OAI.Computability.VertexCover.PCP.NameCompaction
import OAI.Computability.VertexCover.Repetition.CompletedSampling

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover

structure LabelCover where
  u : ℕ
  v : ℕ
  qU : ℕ
  qV : ℕ
  M : ℕ
  qU_pos : 0 < qU
  qV_pos : 0 < qV
  M_pos : 0 < M
  left : Fin M → Fin u
  right : Fin M → Fin v
  projection : Fin M → Fin qU → Fin qV

namespace LabelCover

abbrev Labeling (Φ : LabelCover) := (Fin Φ.u → Fin Φ.qU) × (Fin Φ.v → Fin Φ.qV)

def Satisfies (Φ : LabelCover) (A : Φ.Labeling) (c : Fin Φ.M) : Prop :=
  Φ.projection c (A.1 (Φ.left c)) = A.2 (Φ.right c)

instance (Φ : LabelCover) (A : Φ.Labeling) (c : Fin Φ.M) :
    Decidable (Φ.Satisfies A c) := inferInstanceAs (Decidable (_ = _))

def satisfiedCount (Φ : LabelCover) (A : Φ.Labeling) : ℕ :=
  (Finset.univ.filter (Φ.Satisfies A)).card

def maxSatisfied (Φ : LabelCover) : ℕ :=
  Finset.univ.sup Φ.satisfiedCount

noncomputable def value (Φ : LabelCover) : ℝ := (Φ.maxSatisfied : ℝ) / Φ.M

def defaultLabeling (Φ : LabelCover) : Φ.Labeling :=
  (fun _ => ⟨0, Φ.qU_pos⟩, fun _ => ⟨0, Φ.qV_pos⟩)

theorem satisfiedCount_le_max (Φ : LabelCover) (A : Φ.Labeling) :
    Φ.satisfiedCount A ≤ Φ.maxSatisfied := by
  exact Finset.le_sup (f := Φ.satisfiedCount) (Finset.mem_univ A)

theorem count_le_of_value_le (Φ : LabelCover) {σ : ℝ} (h : Φ.value ≤ σ)
    (A : Φ.Labeling) : (Φ.satisfiedCount A : ℝ) ≤ σ * Φ.M := by
  have hM : (0 : ℝ) < Φ.M := Nat.cast_pos.mpr Φ.M_pos
  have hm : (Φ.maxSatisfied : ℝ) ≤ σ * Φ.M := (div_le_iff₀ hM).mp h
  exact le_trans (Nat.cast_le.mpr (Φ.satisfiedCount_le_max A)) hm

abbrev Query (Φ : LabelCover) (d : ℕ) :=
  Σ j : Fin d,
    ({k : Fin d // j < k} → Fin Φ.u) × ({k : Fin d // k < j} → Fin Φ.v)

namespace Query

def scopeU {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : Finset (Fin Φ.u) :=
  Finset.univ.image i.2.1

def scopeV {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : Finset (Fin Φ.v) :=
  Finset.univ.image i.2.2

abbrev Assignment {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :=
  ({x // x ∈ i.scopeU} → Fin Φ.qU) × ({y // y ∈ i.scopeV} → Fin Φ.qV)

def Valid {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (A : i.Assignment) : Prop :=
  ∀ c : Fin Φ.M, ∀ hx : Φ.left c ∈ i.scopeU, ∀ hy : Φ.right c ∈ i.scopeV,
    Φ.projection c (A.1 ⟨Φ.left c, hx⟩) = A.2 ⟨Φ.right c, hy⟩

instance {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (A : i.Assignment) :
    Decidable (i.Valid A) := inferInstanceAs (Decidable (∀ _c _hx _hy, _ = _))

abbrev LocalLabel {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :=
  {A : i.Assignment // i.Valid A}

end Query

abbrev Coordinate (Φ : LabelCover) (d : ℕ) := Σ i : Φ.Query d, i.LocalLabel

def Compatible (Φ : LabelCover) {d : ℕ} (I : Finset (Φ.Coordinate d)) : Prop :=
  (∀ p ∈ I, ∀ q ∈ I, p.1 = q.1 → p = q) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ x (hp : x ∈ p.1.scopeU) (hq : x ∈ q.1.scopeU),
    p.2.1.1 ⟨x, hp⟩ = q.2.1.1 ⟨x, hq⟩) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ y (hp : y ∈ p.1.scopeV) (hq : y ∈ q.1.scopeV),
    p.2.1.2 ⟨y, hp⟩ = q.2.1.2 ⟨y, hq⟩) ∧
  (∀ p ∈ I, ∀ q ∈ I, ∀ c (hp : Φ.left c ∈ p.1.scopeU)
      (hq : Φ.right c ∈ q.1.scopeV),
    Φ.projection c (p.2.1.1 ⟨Φ.left c, hp⟩) = q.2.1.2 ⟨Φ.right c, hq⟩)

theorem compatible_mono (Φ : LabelCover) {d : ℕ} {I J : Finset (Φ.Coordinate d)}
    (h : Φ.Compatible I) (hJI : J ⊆ I) : Φ.Compatible J := by
  rcases h with ⟨hu, hx, hy, hc⟩
  exact ⟨fun p hp q hq => hu p (hJI hp) q (hJI hq),
    fun p hp q hq => hx p (hJI hp) q (hJI hq),
    fun p hp q hq => hy p (hJI hp) q (hJI hq),
    fun p hp q hq => hc p (hJI hp) q (hJI hq)⟩

theorem compatible_singleton (Φ : LabelCover) {d : ℕ} (p : Φ.Coordinate d) :
    Φ.Compatible {p} := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb _
    simp only [Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  · intro a ha b hb x hx hy
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; rfl
  · intro a ha b hb x hx hy
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; rfl
  · intro a ha b hb c hx hy
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact p.2.2 c hx hy

end LabelCover
end VertexCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
