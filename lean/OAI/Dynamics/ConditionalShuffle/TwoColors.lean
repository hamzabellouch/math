import OAI.Dynamics.ConditionalShuffle.ColorCylinder

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Revealed.Color
open Thorp Revealed.Disintegration
variable {A C : Type} [Fintype A] [Fintype C] [decidableEq_A : DecidableEq A] [decidableEq_C : DecidableEq C]

abbrev ColorEnvironment (d t : ℕ) := Fin (t+1) → Coloring d

def environmentTransport (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) : State (d+1) :=
  if hz : ∃ c : History (d+1) t, occupancy d (layoutColor d L) t c = z then
    sortedTransport d L (run (d+1) t hz.choose)
  else 1

lemma environmentTransport_at (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (c : History (d+1) t) :
    environmentTransport d L t (occupancy d (layoutColor d L) t c) = sortedTransport d L (run (d+1) t c) := by
  let retained_decidableEq_A := decidableEq_A
  let retained_decidableEq_C := decidableEq_C
  have hh : ∃ a : History (d+1) t, occupancy d (layoutColor d L) t a = occupancy d (layoutColor d L) t c := ⟨c,rfl⟩
  rw [environmentTransport, dite_eq_left hh]
  exact transport_occupancy d L t _ c hh.choose_spec

def lawA (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) : Equiv.Perm A → ℝ :=
  conditional (fairMass (fun c : History (d+1) t =>
    (occupancy d (layoutColor d L) t c, internalA d L (run (d+1) t c)))) z

def lawC (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) : Equiv.Perm C → ℝ :=
  conditional (fairMass (fun c : History (d+1) t =>
    (occupancy d (layoutColor d L) t c, internalC d L (run (d+1) t c)))) z

def internalLaw (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) :
    Equiv.Perm A × Equiv.Perm C → ℝ :=
  conditional (fairMass (fun c : History (d+1) t =>
    (occupancy d (layoutColor d L) t c,
      (internalA d L (run (d+1) t c),internalC d L (run (d+1) t c))))) z

lemma lawA_probability (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) :
    (∀ a, 0 ≤ lawA d L t z a) ∧ (∑ a, lawA d L t z a) = 1 := by
  let retained_decidableEq_C := decidableEq_C
  exact ⟨conditional_nonneg _ (fairMass_nonneg _) _, conditional_sum _ _⟩
lemma lawC_probability (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (z : ColorEnvironment d t) :
    (∀ b, 0 ≤ lawC d L t z b) ∧ (∑ b, lawC d L t z b) = 1 := by
  let retained_decidableEq_A := decidableEq_A
  exact ⟨conditional_nonneg _ (fairMass_nonneg _) _, conditional_sum _ _⟩

theorem color_product (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (c : History (d+1) t)
    (a : Equiv.Perm A) (b : Equiv.Perm C) :
    internalLaw d L t (occupancy d (layoutColor d L) t c) (a,b) =
      lawA d L t (occupancy d (layoutColor d L) t c) a * lawC d L t (occupancy d (layoutColor d L) t c) b := by
  exact conditional_product d (layoutColor d L) t c (fun a => L (.inl a)) (fun b => L (.inr b))
    (layoutColor_A d L) (layoutColor_C d L) (internalA d L) (internalC d L)
    (internalA_depends d L) (internalC_depends d L) a b

theorem two_color_construction (d : ℕ) (L : Sum A C ≃ Position (d+1)) (t : ℕ) (c : History (d+1) t) :
    (run (d+1) t c = environmentTransport d L t (occupancy d (layoutColor d L) t c) *
      (L.symm.trans ((Equiv.sumCongr (internalA d L (run (d+1) t c)) (internalC d L (run (d+1) t c))).trans L))) ∧
    (∀ (a : Equiv.Perm A) (b : Equiv.Perm C),
      internalLaw d L t (occupancy d (layoutColor d L) t c) (a,b) =
        lawA d L t (occupancy d (layoutColor d L) t c) a * lawC d L t (occupancy d (layoutColor d L) t c) b) ∧
    (∀ a : A, environmentTransport d L t (occupancy d (layoutColor d L) t c) (L (.inl a)) =
      ofLex (sortedImage (leftEnds d L (run (d+1) t c)) (leftEnds_injective d L (run (d+1) t c)) (leftRank d L 1 a))) ∧
    (∀ b : C, environmentTransport d L t (occupancy d (layoutColor d L) t c) (L (.inr b)) =
      ofLex (sortedImage (rightEnds d L (run (d+1) t c)) (rightEnds_injective d L (run (d+1) t c)) (rightRank d L 1 b))) := by
  refine ⟨?_, color_product d L t c, ?_, ?_⟩
  · rw [environmentTransport_at]; exact physical_color_factor d L _
  · intro a; rw [environmentTransport_at]; exact transport_A d L _ a
  · intro b; rw [environmentTransport_at]; exact transport_C d L _ b

end Revealed.Color

end

end OAI
