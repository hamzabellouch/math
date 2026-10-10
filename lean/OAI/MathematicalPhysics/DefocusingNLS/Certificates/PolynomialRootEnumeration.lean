import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialDisk
import Mathlib.Algebra.Polynomial.Roots

namespace OAI

/-! # From disjoint disks to an exhaustive polynomial root list

Fifteen disjoint root-containing disks exhaust the roots of a nonzero
polynomial of degree at most fifteen, including multiplicities.
-/

open Polynomial

namespace DefocusingNLS

theorem roots_of_fifteen_disks (p : Polynomial ℂ) (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ 15) (c : Fin 15 → ℂ) (r : ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * r < ‖c i - c j‖)
    (hroot : ∀ i, ∃ z : ℂ, ‖z - c i‖ ≤ r ∧ p.IsRoot z) :
    ∃ z : Fin 15 → ℂ, Function.Injective z ∧
      (∀ i, ‖z i - c i‖ ≤ r ∧ p.IsRoot (z i)) ∧
      p.roots = (Finset.univ.image z).val := by
  classical
  choose z hz using hroot
  have hinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have hle : ‖c i - c j‖ ≤ 2 * r := by
      calc
        ‖c i - c j‖ = ‖(c i - z i) + (z j - c j)‖ := by
          rw [hij]
          congr 1
          abel
        _ ≤ ‖c i - z i‖ + ‖z j - c j‖ := norm_add_le _ _
        _ ≤ r + r := by
          rw [norm_sub_rev (c i)]
          exact add_le_add (hz i).1 (hz j).1
        _ = 2 * r := by ring
    exact (not_le_of_gt (hsep i j hne)) hle
  refine ⟨z, hinj, hz, ?_⟩
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hz i).2
  · simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin] using hdegree
  · exact hp

theorem positive_real_iff_of_disk {z c : ℂ} {r : ℝ}
    (hc : r < |c.re|) (hz : ‖z - c‖ ≤ r) :
    0 < z.re ↔ 0 < c.re := by
  have h := (Complex.abs_re_le_norm (z - c)).trans hz
  rw [Complex.sub_re, abs_le] at h
  by_cases hpos : 0 < c.re
  · rw [abs_of_pos hpos] at hc
    constructor <;> intro
    · exact hpos
    · linarith [h.1]
  · rw [abs_of_nonpos (le_of_not_gt hpos)] at hc
    constructor
    · intro hzpos
      linarith [h.2]
    · exact False.elim ∘ hpos

theorem real_ne_zero_of_disk {z c : ℂ} {r : ℝ}
    (hc : r < |c.re|) (hz : ‖z - c‖ ≤ r) : z.re ≠ 0 := by
  intro hzero
  have h := (Complex.abs_re_le_norm (z - c)).trans hz
  simp only [Complex.sub_re, hzero, zero_sub, abs_neg] at h
  exact (not_le_of_gt hc) h

theorem no_axis_root_of_disks (p : Polynomial ℂ) (hp : p ≠ 0)
    (c z : Fin 15 → ℂ) (r : ℝ)
    (hroots : p.roots = (Finset.univ.image z).val)
    (haxis : ∀ i, r < |(c i).re|)
    (hdist : ∀ i, ‖z i - c i‖ ≤ r) {x : ℂ} (hx : p.IsRoot x) : x.re ≠ 0 := by
  classical
  have hmem : x ∈ p.roots := (p.mem_roots hp).mpr hx
  rw [hroots] at hmem
  have hmem' : x ∈ Finset.univ.image z := hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem'
  rw [← hi]
  exact real_ne_zero_of_disk (haxis i) (hdist i)

theorem positive_real_root_count_of_disks (p : Polynomial ℂ)
    (c z : Fin 15 → ℂ) (r : ℝ) (hinj : Function.Injective z)
    (hroots : p.roots = (Finset.univ.image z).val)
    (haxis : ∀ i, r < |(c i).re|)
    (hdist : ∀ i, ‖z i - c i‖ ≤ r) :
    (p.roots.toFinset.filter (fun x => 0 < x.re)).card =
      (Finset.univ.filter (fun i => 0 < (c i).re)).card := by
  classical
  rw [hroots, Finset.val_toFinset, Finset.filter_image]
  simp_rw [positive_real_iff_of_disk (haxis _) (hdist _)]
  exact Finset.card_image_of_injective _ hinj

end DefocusingNLS

end OAI
