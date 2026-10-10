import Mathlib.Data.Nat.Dist
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootResidueSeparation
import OAI.NumberTheory.Ostmann.Quadratic.RootPopulationGeometry

namespace OAI

/-! # Concrete root populations attached to endpoint subsets -/

namespace Ostmann

open scoped Classical

def kernelRootPopulation (S : Finset ℤ) (root : ℤ → ℕ) : Finset ℕ := S.image root

theorem kernelRootPopulation_card (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (hm : 0 < m) (h u : ℤ)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    (kernelRootPopulation S root).card = S.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  have hx' := hroot x hx
  have hy' := hroot y hy
  rw [heq] at hx'
  have hmul : (m : ℤ) * x = (m : ℤ) * y := by omega
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) hmul

private theorem cast_nat_dist (a b : ℕ) :
    (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast hab)
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hba)

theorem kernelRootPopulation_diameter (S : Finset ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (h u : ℤ) (hu : u ≠ 0) (X : ℝ)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ D) :
    ∀ a ∈ kernelRootPopulation S root, ∀ b ∈ kernelRootPopulation S root,
      Nat.dist a b ≤ D := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hx' : (u : ℝ) * (root x : ℝ) ^ 2 = (m : ℝ) * (x : ℝ) - (h : ℝ) := by
    exact_mod_cast hroot x hx
  have hy' : (u : ℝ) * (root y : ℝ) ^ 2 = (m : ℝ) * (y : ℝ) - (h : ℝ) := by
    exact_mod_cast hroot y hy
  have hd := kernel_root_diameter (u : ℝ) (m : ℝ) (h : ℝ) (x : ℝ) (y : ℝ)
    (root x : ℝ) (root y : ℝ) X (by exact_mod_cast hu) (by positivity)
    (by positivity) (by positivity) hx' hy' (by exact_mod_cast hspan x hx y hy)
  have hd' : (Nat.dist (root x) (root y) : ℝ) ≤ D := by
    rw [cast_nat_dist]
    exact hd.trans hD
  exact_mod_cast hd'

theorem kernelRootPopulation_residues_disjoint {p : ℕ} [Fact p.Prime]
    (S T : Finset ℤ) (rootS rootT : ℤ → ℕ) (m : ℕ) (h u v : ℤ) (c : ZMod p)
    (hpm : ¬p ∣ m)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (hc : (u : ZMod p) * c ^ 2 = (v : ZMod p))
    (hprime : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (hsmall : ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs) :
    Disjoint ((kernelRootPopulation S rootS).image (fun a : ℕ => (a : ZMod p)))
      ((kernelRootPopulation T rootT).image (fun b : ℕ => c * (b : ZMod p))) := by
  have hsep := kernel_root_images_disjoint S T (fun x => (rootS x : ℤ))
    (fun y => (rootT y : ℤ)) m h u v c hpm hS hT hc hprime hsmall
  simpa only [kernelRootPopulation, Finset.image_image, Int.cast_natCast,
    Function.comp_def] using hsep

end Ostmann

end OAI
