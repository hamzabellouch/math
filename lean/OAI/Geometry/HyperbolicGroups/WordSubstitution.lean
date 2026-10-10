import Mathlib
import OAI.Geometry.HyperbolicGroups.WordDisk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
variable {A B : Type*}
variable (c : A × Bool → Word B) (hc : ∀ e, c (e.1,!e.2) = FreeGroup.invRev (c e))

include hc

lemma substitute_reverse (z : Word A) :
    (FreeGroup.invRev z).flatMap c = FreeGroup.invRev (z.flatMap c) := by
  induction z with
  | nil => rfl
  | cons e z ih =>
    rw [FreeGroup.invRev_cons,List.flatMap_append,ih,List.flatMap_cons,FreeGroup.invRev_append]
    congr 1
    change c (e.1,!e.2) ++ [] = FreeGroup.invRev (c e)
    simpa only [List.append_nil] using hc e

lemma substitute_free_step {z t : Word A} (h : FreeGroup.Red.Step z t) :
    FreeGroup.mk (z.flatMap c) = FreeGroup.mk (t.flatMap c) := by
  cases h with
  | @not l r x b =>
    simp only [List.flatMap_append,List.flatMap_cons]
    rw [hc (x,b)]
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]
    group

namespace Move
variable {R : Set (Word A)} {S : Set (Word B)} {C k : ℕ}
variable (hR : ∀ z ∈ R, ∃ a ≤ C, Homotopy S (z.flatMap c) [] a)
include hR

lemma substitute {z t : Word A} (h : Move R z t k) :
    ∃ a ≤ C * k, Homotopy S (z.flatMap c) (t.flatMap c) a := by
  cases h with
  | free h => exact ⟨0,by simp,Homotopy.free (substitute_free_step c hc h)⟩
  | face l r z hz =>
    obtain ⟨a,ha,hh⟩ := hR z hz
    refine ⟨a,by simpa using ha,?_⟩
    simpa only [List.flatMap_append,List.append_nil] using hh.contextual (l.flatMap c) (r.flatMap c)
  | reverseFace l r z hz =>
    obtain ⟨a,ha,hh⟩ := hR z hz
    refine ⟨a,by simpa using ha,?_⟩
    simpa only [List.flatMap_append,substitute_reverse c hc,FreeGroup.invRev_empty,List.append_nil] using
      hh.reverse.contextual (l.flatMap c) (r.flatMap c)
end Move

namespace Homotopy
variable {R : Set (Word A)} {S : Set (Word B)} {C k : ℕ}
variable (hR : ∀ z ∈ R, ∃ a ≤ C, Homotopy S (z.flatMap c) [] a)
include hR

/-- Quantitative substitution of proved literal relator disks. All contexts,
free folds, reverse relators and intermediate words are retained. -/
theorem substitute {z t : Word A} (h : Homotopy R z t k) :
    ∃ a ≤ C * k, Homotopy S (z.flatMap c) (t.flatMap c) a := by
  induction h with
  | refl => exact ⟨0,by simp,Homotopy.refl _⟩
  | move h => exact h.substitute c hc hR
  | symm h ih => obtain ⟨a,ha,hh⟩ := ih; exact ⟨a,ha,hh.symm⟩
  | trans h h' ih ih' =>
    obtain ⟨a,ha,hh⟩ := ih
    obtain ⟨b,hb,hh'⟩ := ih'
    exact ⟨a+b,by rw [Nat.mul_add]; exact Nat.add_le_add ha hb,hh.trans hh'⟩
end Homotopy
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
