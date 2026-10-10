import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyLongExact

namespace OAI

/-! # Vanishing along a finite exact coefficient resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_vanishing_of_shortExact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (hA : Subsingleton (ShiftedCompletedCohomology (p + 1) S.X₁))
    (hB : Subsingleton (ShiftedCompletedCohomology p S.X₂)) :
    Subsingleton (ShiftedCompletedCohomology p S.X₃) := by
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p S.X₃)
  intro x
  have hx : shiftedCompleteBoundary p S hS x = 0 := hA.elim _ _
  obtain ⟨y, hy⟩ := shiftedCompleteCohomology_map_boundary_exact p S hS x hx
  rw [← hy, hB.elim y 0, map_zero]

theorem shiftedCompleteCohomology_vanishing_of_finite_resolution
    (d : ℕ) (K P : ℕ → Rep.{0} ℤ G)
    (ι : ∀ n, K (n + 1) ⟶ P n) (π : ∀ n, P n ⟶ K n)
    (zero : ∀ n, ι n ≫ π n = 0)
    (hexact : ∀ n, n < d → (ShortComplex.mk (ι n) (π n) (zero n)).ShortExact)
    (hP : ∀ n, n < d → ∀ p, Subsingleton (ShiftedCompletedCohomology p (P n)))
    (hK : ∀ p, Subsingleton (ShiftedCompletedCohomology p (K d))) (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (K 0)) := by
  induction d generalizing K P p with
  | zero => exact hK p
  | succ d ih =>
    have ht : Subsingleton (ShiftedCompletedCohomology (p + 1) (K 1)) := by
      apply ih (fun n => K (n + 1)) (fun n => P (n + 1))
        (fun n => ι (n + 1)) (fun n => π (n + 1)) (fun n => zero (n + 1))
      · intro n hn
        exact hexact (n + 1) (by omega)
      · intro n hn q
        exact hP (n + 1) (by omega) q
      · exact hK
    exact shiftedCompleteCohomology_vanishing_of_shortExact p
      (ShortComplex.mk (ι 0) (π 0) (zero 0)) (hexact 0 (by omega)) ht (hP 0 (by omega) p)

end PolycyclicRecognition

end

end OAI
