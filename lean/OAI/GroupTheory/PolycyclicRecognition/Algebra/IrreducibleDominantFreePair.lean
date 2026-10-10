import OAI.GroupTheory.PolycyclicRecognition.Algebra.IrreducibleGenericConjugator
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugateEigenlineFreePair

namespace OAI

/-! # A free pair from one two-sided dominant element

For an irreducible real representation of an irreducible polynomial group,
generic position supplies the conjugator. The two-sided spectral estimates
then give freely generating powers of the element and that conjugate.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {G : Type} [Group G] [TopologicalSpace G] [PreirreducibleSpace G]
    [ContinuousInv G] {n : ℕ}

def realContinuousRepresentation (ι : G →* PolynomialMatrixGroup ℝ n) :
    G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (Module.End.toContinuousLinearMap (Fin n → ℝ)).toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction.toMonoidHom.comp ι))

omit [TopologicalSpace G] [PreirreducibleSpace G] [ContinuousInv G] in
@[simp] theorem realContinuousRepresentation_apply
    (ι : G →* PolynomialMatrixGroup ℝ n) (g : G) (x : Fin n → ℝ) :
    realContinuousRepresentation ι g x = linearAction (ι g) x := rfl

theorem free_conjugate_powers_of_irreducible_dominant_element
    (ι : G →* PolynomialMatrixGroup ℝ n) (hι : Continuous ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (hn : 2 ≤ n) (a : G)
    (φ : Bool → (Fin n → ℝ) →L[ℝ] ℝ) (v : Bool → Fin n → ℝ) (μ b : Bool → ℝ)
    (hv : ∀ s, linearAction (ι (if s then a⁻¹ else a)) (v s) = μ s • v s)
    (hφv : ∀ s, φ s (v s) = 1)
    (hφ : ∀ s x, φ s (linearAction (ι (if s then a⁻¹ else a)) x) = μ s * φ s x)
    (hb : ∀ s, 0 ≤ b s) (hgap : ∀ s, b s < |μ s|)
    (hker : ∀ s x, φ s x = 0 →
      ‖linearAction (ι (if s then a⁻¹ else a)) x‖ ≤ b s * ‖x‖) :
    ∃ h : G, ∃ N : ℕ, 0 < N ∧ Function.Injective
      (FreeGroup.lift (fun i : Bool => if i then h * a ^ N * h⁻¹ else a ^ N)) := by
  classical
  have hline (s : Bool) : Submodule.span ℝ ({v s} : Set (Fin n → ℝ)) ≠ ⊤ := by
    intro he
    have hd := finrank_span_le_card (R := ℝ) ({v s} : Set (Fin n → ℝ))
    rw [he] at hd
    have hle : n ≤ 1 := by simpa using hd
    omega
  obtain ⟨h, hh⟩ := exists_irreducible_transverse_conjugator ι hι v
    (fun s => (φ s).toLinearMap) hφv hline
  let : MulAction G (Fin n → ℝ) := {
    smul g x := linearAction (ι g) x
    one_smul x := by
      change linearAction (ι 1) x = x
      rw [map_one, map_one]
      rfl
    mul_smul g h x := by
      change linearAction (ι (g * h)) x = linearAction (ι g) (linearAction (ι h) x)
      rw [map_mul, map_mul]
      rfl }
  let ρ := realContinuousRepresentation ι
  have hact (g : G) (x : Fin n → ℝ) : ρ g x = g • x := rfl
  refine ⟨h, free_powers_of_transverse_conjugate ρ hact a h φ v μ b hv hφv hφ hb hgap hker
    (fun s t => ⟨(hh s t).1, (hh s t).2.1⟩)
    (fun s t => ⟨(hh s t).2.2.1, (hh s t).2.2.2⟩)⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
