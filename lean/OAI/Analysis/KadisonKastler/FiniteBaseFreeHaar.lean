import OAI.Analysis.KadisonKastler.IndependenceMoments

namespace OAI

/-! # A free Haar unitary for the finite scalar matrix base

Finite dimensionality supplies the separability premise of the published
independence input. Centering the base is an actual submodule, and testing
against scalar multiples of one is exactly the required orthogonality.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Norm separability implies separability for the weaker trace norm. -/
theorem traceSeparable_of_separable (τ : FaithfulTracialState B)
    (X : Submodule ℂ B) [SeparableSpace X] : TraceSeparable τ (X : Set B) := by
  obtain ⟨S, hS, hSX, hSD⟩ := exists_countable_dense_subset (X : Set B)
  refine ⟨S, hS, hSX, ?_⟩
  intro x hx ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hSD hx) ε hε
  refine ⟨y, hy, (traceTwoNorm_le_norm τ _).trans_lt ?_⟩
  exact (dist_eq_norm x y) ▸ hxy

/-- The centered linear subspace of a base star algebra. -/
def centeredBase (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B) :
    Submodule ℂ B := A.toSubmodule ⊓ LinearMap.ker τ.toLinearMap

@[simp]
theorem mem_centeredBase (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B) (x : B) :
    x ∈ centeredBase τ A ↔ x ∈ A ∧ τ.toLinearMap x = 0 := Iff.rfl

theorem traceOrthogonal_bot (τ : FaithfulTracialState B) {x : B}
    (hx : τ.toLinearMap x = 0) : TraceOrthogonal τ ⊥ x := by
  intro b hb
  obtain ⟨z, rfl⟩ := StarSubalgebra.mem_bot.mp hb
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hx, smul_zero]

/-- Popa's published finite-base independence theorem, applied with scalar
base, produces the precise free-Haar moments for any finite dimensional
subalgebra. -/
theorem FiniteBaseIndependence.exists_freeHaar
    (τ : FaithfulTracialState B) (h : FiniteBaseIndependence τ)
    (A : StarSubalgebra ℂ B) [FiniteDimensional ℂ A] :
    ∃ w : unitary B, FreeHaarMoments τ A w := by
  let X := centeredBase τ A
  let e : X →ₗ[ℂ] A :=
    { toFun := fun x => ⟨x, x.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : A => (z : B)) hxy
  let : FiniteDimensional ℂ X := FiniteDimensional.of_injective e he
  let : FiniteDimensional ℂ (⊥ : StarSubalgebra ℂ B) :=
    FiniteDimensional.of_surjective (Algebra.linearMap ℂ B |>.codRestrict
      (⊥ : StarSubalgebra ℂ B).toSubmodule (fun z => ⟨z, rfl⟩)) (by
        rintro ⟨b, hb⟩
        obtain ⟨z, rfl⟩ := StarSubalgebra.mem_bot.mp hb
        exact ⟨z, rfl⟩)
  obtain ⟨w, _, hhaar, hw⟩ := h ⊥ inferInstance X (traceSeparable_of_separable τ X)
    (fun x hx => traceOrthogonal_bot τ hx.2)
  exact ⟨w, hw.freeHaarMoments hhaar (fun _ hx => hx.2) A
    (fun a ha ht => ⟨ha, ht⟩)⟩

end

end KadisonKastler

end OAI
