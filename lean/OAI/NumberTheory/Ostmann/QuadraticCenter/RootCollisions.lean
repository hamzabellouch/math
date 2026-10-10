import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Preliminaries.Projection

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

/-- Probability that two uniform elements of `s` are congruent modulo `p`. -/
noncomputable def uniformResidueCollision (s : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.range p, (residueMass s (fun _ => 1 / (s.card : ℝ)) p r) ^ 2

theorem uniformResidueCollision_lower (s : Finset ℕ) (hs : s.Nonempty)
    {p : ℕ} (hp : 0 < p) : 1 / (p : ℝ) ≤ uniformResidueCollision s p := by
  have hmass := residueMass_total s (fun _ => 1 / (s.card : ℝ)) hp
  rw [sum_uniform_mass s hs] at hmass
  have hrange : (Finset.range p).Nonempty := ⟨0, Finset.mem_range.mpr hp⟩
  simpa only [Finset.card_range, uniformResidueCollision] using
    inverse_card_le_collision (Finset.range p)
      (residueMass s (fun _ => 1 / (s.card : ℝ)) p) hrange hmass

theorem uniformResidueCollision_upper (P s : Finset ℕ) (hs : s.Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hP : ∀ p ∈ P, p.Prime)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ D) :
    (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision s p) ≤
      Real.log (D : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) := by
  exact residue_collision_bound_of_diameter P s (fun _ => 1 / (s.card : ℝ)) D
    (1 / (s.card : ℝ)) hD hP hdiam (fun _ _ => by positivity)
    (sum_uniform_mass s hs) (fun _ _ => le_rfl)

/-- Disjoint residue images, after an injective relabeling on each side,
force the stronger lower bound at a split prime. -/
theorem uniformResidueCollision_lower_of_disjoint_images (s t : Finset ℕ)
    (hs : s.Nonempty) (ht : t.Nonempty) {p : ℕ} (hp : 0 < p)
    (f g : ℕ → ℕ)
    (hf : ∀ a ∈ s, f a < p) (hg : ∀ b ∈ t, g b < p)
    (hfc : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p])
    (hgc : ∀ a ∈ t, ∀ b ∈ t, g a = g b ↔ a ≡ b [MOD p])
    (hdisjoint : Disjoint (s.image f) (t.image g)) :
    4 / (p : ℝ) ≤ uniformResidueCollision s p + uniformResidueCollision t p := by
  classical
  let S := s.image f
  let T := t.image g
  have hS : S.Nonempty := hs.image f
  have hT : T.Nonempty := ht.image g
  have hmaps : ∀ a ∈ s, f a ∈ S := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmapt : ∀ a ∈ t, g a ∈ T := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hcard : S.card + T.card ≤ p := by
    rw [← Finset.card_union_of_disjoint hdisjoint, ← Finset.card_range p]
    apply Finset.card_le_card
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_range.mpr (hf a ha)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_range.mpr (hg a ha)
  have hmasss : (∑ r ∈ S, fiberMass s (fun _ => 1 / (s.card : ℝ)) f r) = 1 := by
    rw [sum_fiberMass s S _ f hmaps]
    exact sum_uniform_mass s hs
  have hmasst : (∑ r ∈ T, fiberMass t (fun _ => 1 / (t.card : ℝ)) g r) = 1 := by
    rw [sum_fiberMass t T _ g hmapt]
    exact sum_uniform_mass t ht
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hcard' : (S.card : ℝ) + T.card ≤ p := by exact_mod_cast hcard
  calc
    _ ≤ 1 / (S.card : ℝ) + 1 / (T.card : ℝ) :=
      four_div_le_inverse_add_inverse hSpos hTpos hcard'
    _ ≤ (∑ r ∈ S, (fiberMass s (fun _ => 1 / (s.card : ℝ)) f r) ^ 2) +
        (∑ r ∈ T, (fiberMass t (fun _ => 1 / (t.card : ℝ)) g r) ^ 2) :=
      add_le_add (inverse_card_le_collision S _ hS hmasss)
        (inverse_card_le_collision T _ hT hmasst)
    _ = _ := by
      rw [fiberMass_sq_eq_residueMass_sq s S _ f hp hmaps hfc,
        fiberMass_sq_eq_residueMass_sq t T _ g hp hmapt hgc]
      rfl

/-- Multiplying one population by a nonzero field element preserves its
collision probability. Thus disjoint scaled root residues give `4 / p`. -/
theorem uniformResidueCollision_lower_of_scaled_disjoint {p : ℕ} [Fact p.Prime]
    (s t : Finset ℕ) (hs : s.Nonempty) (ht : t.Nonempty) (c : ZMod p) (hc : c ≠ 0)
    (hdisjoint : Disjoint (s.image (fun a : ℕ => (a : ZMod p)))
      (t.image (fun b : ℕ => c * (b : ZMod p)))) :
    4 / (p : ℝ) ≤ uniformResidueCollision s p + uniformResidueCollision t p := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let f : ℕ → ℕ := fun a => (a : ZMod p).val
  let g : ℕ → ℕ := fun b => (c * (b : ZMod p)).val
  apply uniformResidueCollision_lower_of_disjoint_images s t hs ht hp f g
  · intro a _
    exact ZMod.val_lt _
  · intro b _
    exact ZMod.val_lt _
  · intro a _ b _
    exact (ZMod.val_injective p).eq_iff.trans (ZMod.natCast_eq_natCast_iff a b p)
  · intro a _ b _
    constructor
    · intro hab
      exact (ZMod.natCast_eq_natCast_iff a b p).mp
        (mul_left_cancel₀ hc (ZMod.val_injective p hab))
    · intro hab
      apply congrArg ZMod.val
      rw [(ZMod.natCast_eq_natCast_iff a b p).mpr hab]
  · apply Finset.disjoint_left.mpr
    intro r hr hs'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hs'
    apply Finset.disjoint_left.mp hdisjoint
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    exact Finset.mem_image.mpr ⟨b, hb, ZMod.val_injective p heq⟩

end Ostmann

end OAI
