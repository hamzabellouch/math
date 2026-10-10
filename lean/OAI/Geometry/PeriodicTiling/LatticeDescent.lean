import OAI.Geometry.PeriodicTiling.IntegerMatrixIndex
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory
open scoped Classical

def normalizedComplement (m : ℕ) (c₀ : Space 3) (A : Set (Space 3)) :
    Set (Lattice 3) := {z | c₀ + scaledCast m z ∈ A}

theorem period_lattice_le_scaledGrid (m : ℕ) (c₀ : Space 3)
    {A : Set (Space 3)} (hne : A.Nonempty)
    (hgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a)
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period A v) :
    latticeOfBasis b ≤ scaledGrid m := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨z₀, hz₀⟩ := hgrid a ha
  intro v hv
  obtain ⟨z₁, hz₁⟩ := hgrid (a + v) ((hp v hv a).mpr ha)
  refine ⟨z₁ - z₀, ?_⟩
  change scaledCast m (z₁ - z₀) = v
  calc
    scaledCast m (z₁ - z₀) =
        (c₀ + scaledCast m z₁) - (c₀ + scaledCast m z₀) := by
      rw [map_sub]
      abel
    _ = (a + v) - a := by rw [hz₀, hz₁]
    _ = v := by abel

theorem fullyPeriodic_normalizedComplement (m : ℕ) (c₀ : Space 3)
    {A : Set (Space 3)} (hne : A.Nonempty)
    (hgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a)
    (hperiodic : EuclideanFullyPeriodic A) :
    FullyPeriodic (normalizedComplement m c₀ A) := by
  obtain ⟨b, hb⟩ := hperiodic
  have hle := period_lattice_le_scaledGrid m c₀ hne hgrid b hb
  refine ⟨(latticeOfBasis b).comap (scaledCast m),
    lattice_pullback_finiteIndex m b hle, ?_⟩
  intro v hv z
  change c₀ + scaledCast m (z + v) ∈ A ↔ c₀ + scaledCast m z ∈ A
  rw [map_add, ← add_assoc]
  exact hb (scaledCast m v) hv (c₀ + scaledCast m z)

theorem normalized_typedAETiles (m : ℕ) (hm : m ≠ 0) (c₀ : Space 3)
    {Ω₀ Ω₁ C A : Set (Space 3)}
    (hgrid : C = Set.range (fun z : Lattice 3 => c₀ + scaledCast m z))
    (htile : TypedAETiles Ω₀ Ω₁ C A) :
    ∀ᵐ x ∂volume, ∃! z : Lattice 3,
      x - scaledCast m z ∈
        if z ∈ normalizedComplement m c₀ A then Ω₁ else Ω₀ := by
  classical
  have hshift : ∀ᵐ x ∂volume, ∃! c : C,
      (c₀ + x) - (c : Space 3) ∈
        if (c : Space 3) ∈ A then Ω₁ else Ω₀ :=
    (eventually_add_left_iff volume c₀).mpr htile
  filter_upwards [hshift] with x hx
  obtain ⟨c, hc, huniq⟩ := hx
  obtain ⟨z, hz⟩ : ∃ z : Lattice 3, c₀ + scaledCast m z = (c : Space 3) := by
    exact Eq.mp
      (congrArg (fun S : Set (Space 3) => (c : Space 3) ∈ S) hgrid) c.property
  refine ⟨z, ?_, ?_⟩
  · rw [← hz] at hc
    have he : (c₀ + x) - (c₀ + scaledCast m z) = x - scaledCast m z := by abel
    by_cases hzA : c₀ + scaledCast m z ∈ A
    · simpa only [he, normalizedComplement, Set.mem_ofPred_eq, hzA, ite_true] using hc
    · simpa only [he, normalizedComplement, Set.mem_ofPred_eq, hzA, ite_false] using hc
  · intro y hy
    let cy : C := ⟨c₀ + scaledCast m y, by rw [hgrid]; exact ⟨y, rfl⟩⟩
    have hcy : (c₀ + x) - (cy : Space 3) ∈
        if (cy : Space 3) ∈ A then Ω₁ else Ω₀ := by
      change (c₀ + x) - (c₀ + scaledCast m y) ∈
        if c₀ + scaledCast m y ∈ A then Ω₁ else Ω₀
      have he : (c₀ + x) - (c₀ + scaledCast m y) = x - scaledCast m y := by abel
      rw [he]
      exact hy
    have he : c₀ + scaledCast m y = c₀ + scaledCast m z := by
      exact (congrArg Subtype.val (huniq cy hcy)).trans hz.symm
    exact scaledCast_injective hm (add_left_cancel he)

end PeriodicTilingThree

end

end OAI
