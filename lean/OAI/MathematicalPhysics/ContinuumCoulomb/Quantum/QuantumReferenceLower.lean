import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceFamily

namespace OAI

/-! Positive local history terms make a constant-strength reference penalty sufficient. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem qmaQuadratic_sum {κ : Type*} [Fintype κ] (A : κ → Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (∑ i, A i) u = ∑ i, qmaQuadratic (A i) u := by
  have h (s : Finset κ) : qmaQuadratic (∑ i ∈ s, A i) u = ∑ i ∈ s, qmaQuadratic (A i) u := by
    classical
    induction s using Finset.induction with
    | empty => simp [qmaQuadratic]
    | @insert i s hi ih => simp only [Finset.sum_insert hi,qmaQuadratic_add,ih]
  exact h Finset.univ

theorem qmaQuadratic_identity (u : α → ℂ) :
    qmaQuadratic (1 : Matrix α α ℂ) u = ∑ i, Complex.normSq (u i) := by
  simp [qmaQuadratic,dotProduct,Complex.mul_re,Complex.normSq_apply]

omit [DecidableEq α] in
theorem qmaReferenceSector_nonnegative (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (s : SourceSpinBasis (n+1)) (u : α → ℂ) :
    0 ≤ qmaQuadratic (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s) u := by
  rw [qmaQuadratic_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases hs : s i = 0
  · rw [qmaReferenceSectorTerm,ite_eq_left hs,qmaConjugate_quadratic]
    exact hpos i _
  · rw [qmaReferenceSectorTerm,ite_eq_right hs]
    exact hpos i u

theorem qmaReferenceSector_lower (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : a ≤ Δ)
    (hA : ∀ u, a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (∑ i, A i) u)
    (s : SourceSpinBasis (n+1)) (u : α → ℂ) :
    a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ s) u := by
  have hm : 0 ≤ ∑ i, Complex.normSq (u i) := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  by_cases hs : ∀ i, s i = s 0
  · have he : s = fun _ => s 0 := funext hs
    rw [he]
    generalize hb : s 0 = b
    fin_cases b
    · change a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ (fun _ => 0)) u
      rw [qmaReferenceSector_zero,qmaConjugate_quadratic]
      simpa using hA (fun i => star (u i))
    · change a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ (fun _ => 1)) u
      rw [qmaReferenceSector_one]
      exact hA u
  · have hw : (1:ℝ) ≤ qmaReferenceWalls n s := by exact_mod_cast qmaReferenceWalls_pos n s hs
    have hp := qmaReferenceSector_nonnegative n A hpos s u
    have he : qmaQuadratic (qmaReferenceSector n A Δ s) u =
        qmaQuadratic (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s) u+
          Δ*(qmaReferenceWalls n s:ℝ)*(∑ i, Complex.normSq (u i)) := by
      rw [qmaReferenceSector,qmaQuadratic_add]
      have hc : (Δ:ℂ)*(qmaReferenceWalls n s:ℂ) = ((Δ*(qmaReferenceWalls n s:ℝ):ℝ):ℂ) := by simp
      rw [hc,qmaQuadratic_smul,qmaQuadratic_identity]
    rw [he]
    have hΔ0 : 0 ≤ Δ := ha.trans hΔ
    have hg : a ≤ Δ*(qmaReferenceWalls n s:ℝ) := by nlinarith
    exact (mul_le_mul_of_nonneg_right hg hm).trans (le_add_of_nonneg_left hp)

end ContinuumCoulomb

end

end OAI
