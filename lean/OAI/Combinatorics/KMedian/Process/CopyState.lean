import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalPotential

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

abbrev Copy := F × Fin Δ

def slots (f : F) : Finset (Copy (F := F) Δ) := univ.image (fun i => (f,i))

@[simp] theorem mem_slots (f : F) (i : Copy (F := F) Δ) : i ∈ slots Δ f ↔ i.1=f := by
  rw [slots, mem_image]
  constructor
  · rintro ⟨a,_,he⟩
    exact (congrArg Prod.fst he).symm
  · intro h
    exact ⟨i.2, mem_univ _, Prod.ext h.symm rfl⟩

@[simp] theorem card_slots (f : F) : (slots Δ f).card=Δ := by
  rw [slots, card_image_of_injective _ (fun i j h => (Prod.mk.inj h).2)]
  simp

 theorem slots_disjoint {f h : F} (hfh : f ≠ h) : Disjoint (slots Δ f) (slots Δ h) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact hfh (((mem_slots Δ f i).mp hi).symm.trans ((mem_slots Δ h i).mp hj))

def resets (O : Finset F) : Finset (Copy (F := F) Δ) := O.biUnion (slots Δ)

@[simp] theorem mem_resets (O : Finset F) (i : Copy (F := F) Δ) : i ∈ resets Δ O ↔ i.1 ∈ O := by
  simp [resets]

 theorem card_resets (O : Finset F) : (resets Δ O).card=O.card*Δ := by
  rw [resets, card_biUnion (fun _ _ _ _ hne => slots_disjoint Δ hne)]
  simp

variable [Fintype F]

def integral (A : Finset (Copy (F := F) Δ)) : Finset F := univ.filter (fun f => slots Δ f ⊆ A)

@[simp] theorem mem_integral (A : Finset (Copy (F := F) Δ)) (f : F) :
    f ∈ integral Δ A ↔ slots Δ f ⊆ A := by simp [integral]

def next (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) := (A \ erased) ∪ resets Δ O

 theorem reset_integral (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) :
    O ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  exact mem_union_right _ ((mem_resets _ _ _).mpr ((mem_slots _ _ _).mp hi ▸ hf))

theorem integral_persists (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    (hattribute : ∀ i ∈ A, i ∈ erased → i.1 ∈ integral Δ A → i.1 ∈ O) :
    integral Δ A ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  have hiA := (mem_integral _ _ _).mp hf hi
  have hif := (mem_slots _ _ _).mp hi
  by_cases hie : i ∈ erased
  · apply mem_union_right
    apply (mem_resets _ _ _).mpr
    exact hattribute i hiA hie (hif ▸ hf)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hiA,hie⟩)

omit [Fintype F] in
 theorem reset_mass (O : Finset F) {g : ℝ} (hunit : g*(Δ:ℝ)=1) :
    mass g (resets Δ O)=(O.card:ℝ) := by
  rw [mass, card_resets, Nat.cast_mul]
  nlinarith only [hunit]

 theorem integral_count (A : Finset (Copy (F := F) Δ)) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) : (integral Δ A).card ≤ mass g A := by
  rw [← reset_mass Δ _ hunit]
  apply mass_mono hg
  intro i hi
  exact (mem_integral _ _ _).mp ((mem_resets _ _ _).mp hi) ((mem_slots _ _ _).mpr rfl)

omit [Fintype F] in

theorem next_mass_le (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (he : erased ⊆ A) :
    mass g (next Δ A erased O) ≤ mass g A-mass g erased+O.card := by
  have hc := card_union_le (A \ erased) (resets Δ O)
  have hr : ((next Δ A erased O).card:ℝ) ≤ ((A \ erased).card:ℝ)+(resets Δ O).card := by
    exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hr hg
  change mass g (next Δ A erased O) ≤ _ at hm
  rw [mul_add, ← mass, ← mass, mass_sdiff g he, reset_mass Δ O hunit] at hm
  exact hm

omit [Fintype F] in
 theorem next_mass_at_least_one (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    {g : ℝ} (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hA : 1 ≤ mass g A)
    (ha : erased.Nonempty → O.Nonempty) : 1 ≤ mass g (next Δ A erased O) := by
  by_cases ho : O.Nonempty
  · have hc : (1:ℝ) ≤ O.card := by exact_mod_cast ho.card_pos
    have hs : resets Δ O ⊆ next Δ A erased O := subset_union_right
    exact (hc.trans_eq (reset_mass Δ O hunit).symm).trans (mass_mono hg hs)
  · have he : erased=∅ := not_nonempty_iff_eq_empty.mp (fun h => ho (ha h))
    exact hA.trans (mass_mono hg (by simp [next,he]))

end MetricKMedian.CopyState
end
end

end OAI
