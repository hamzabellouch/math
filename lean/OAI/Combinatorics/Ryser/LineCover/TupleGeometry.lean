import OAI.Combinatorics.Ryser.LineCover.Definitions
import OAI.Combinatorics.Ryser.Geometry.AffineJoins

namespace OAI

open scoped Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F] {t : ℕ}

def NoParallel (a : LineTuple F t) : Prop :=
  ∀ i j, i ≠ j → (a i).1 ≠ (a j).1

def NoConcurrentTriple (a : LineTuple F t) : Prop :=
  ∀ p : ProjectivePoint F, ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ProjectiveIncidence p (some (a i)) →
    ProjectiveIncidence p (some (a j)) →
    ProjectiveIncidence p (some (a k)) → False

theorem finiteCrossings_of_no_parallel (a : LineTuple F t) (h : NoParallel a) :
    FiniteCrossings a := let _ := instFintypeF; let _ := instDecidableEqF; by
  intro i j
  exact (existsUnique_incident_of_ne_direction (a (Sum.inl i)) (a (Sum.inr j))
    (h _ _ (by intro he; cases he))).exists

theorem crossPoints_eq_image_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2))) :
    crossPoints a = Finset.univ.image g := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, hi, hj⟩ := (mem_crossPoints a x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    exact eq_of_common_incidence_of_ne_lines (left_ne_right a i j)
      (hg (i, j)).1 (hg (i, j)).2 hi hj
  · intro hx
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_crossPoints a (g ij)).mpr ⟨ij.1, ij.2, (hg ij).1, (hg ij).2⟩

theorem crossPoints_card_of_grid (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (hinj : Function.Injective g) : (crossPoints a).card = t * t := by
  rw [crossPoints_eq_image_grid a g hg, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

theorem grid_injective_of_no_concurrentTriple (a : LineTuple F t)
    (g : Fin t × Fin t → Point F)
    (hg : ∀ ij, Incidence (g ij) (a (Sum.inl ij.1)) ∧
      Incidence (g ij) (a (Sum.inr ij.2)))
    (h : NoConcurrentTriple a) : Function.Injective g := let _ := instFintypeF; let _ := instDecidableEqF; by
  rintro ⟨i, j⟩ ⟨k, l⟩ he
  have hleft : Incidence (g (i, j)) (a (Sum.inl k)) := by
    rw [he]
    exact (hg (k, l)).1
  have hright : Incidence (g (i, j)) (a (Sum.inr l)) := by
    rw [he]
    exact (hg (k, l)).2
  have hik : i = k := by
    by_contra hik
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inl k) (Sum.inr j)
      (fun hi => hik (Sum.inl.inj hi))
      (by intro hi; cases hi) (by intro hi; cases hi)
      (hg (i, j)).1 hleft (hg (i, j)).2
  have hjl : j = l := by
    by_contra hjl
    exact h (Sum.inl (g (i, j))) (Sum.inl i) (Sum.inr j) (Sum.inr l)
      (by intro hi; cases hi) (by intro hi; cases hi)
      (fun hi => hjl (Sum.inr.inj hi))
      (hg (i, j)).1 (hg (i, j)).2 hright
  exact Prod.ext hik hjl

theorem finiteCrossings_card_of_no_parallel_no_concurrentTriple
    (a : LineTuple F t) (hp : NoParallel a) (hc : NoConcurrentTriple a) :
    FiniteCrossings a ∧ (crossPoints a).card = t * t := by
  have hfinite := finiteCrossings_of_no_parallel a hp
  choose g hg using hfinite
  let grid : Fin t × Fin t → Point F := fun ij => g ij.1 ij.2
  have hgrid : ∀ ij, Incidence (grid ij) (a (Sum.inl ij.1)) ∧
      Incidence (grid ij) (a (Sum.inr ij.2)) := fun ij => hg ij.1 ij.2
  exact ⟨finiteCrossings_of_no_parallel a hp, crossPoints_card_of_grid a grid hgrid
    (grid_injective_of_no_concurrentTriple a grid hgrid hc)⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
