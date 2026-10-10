import Mathlib
import OAI.Computability.MaxCut.Encoding.Encoding

namespace OAI

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear

namespace MaxCutGames.Decoder.AdviceFibers

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K]
  [AddCommGroup R] [Module F2 R]

/-- Actual matrices with the specified observed row advice. -/
abbrev RowFiber (A : K →ₗ[F2] R) (S : E →ₗ[F2] R) :=
  {M : E →ₗ[F2] K // A.comp M = S}

/-- Hidden coordinates relative to one base matrix in the same row fiber. -/
def kernelDifference (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    E →ₗ[F2] A.ker :=
  (M.val - M₀).codRestrict A.ker (by
    intro x
    change A (M.val x - M₀ x) = 0
    rw [map_sub]
    have hM := LinearMap.congr_fun M.property x
    have hbase := LinearMap.congr_fun h₀ x
    change A (M.val x) = S x at hM
    change A (M₀ x) = S x at hbase
    rw [hM, hbase, sub_self])

@[simp] theorem kernelDifference_apply (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) (x : E) :
    (kernelDifference A S M₀ h₀ M x : K) = M.val x - M₀ x := rfl

/-- Reassemble an actual matrix from its fixed visible base and private part. -/
def assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : E →ₗ[F2] K :=
  M₀ + A.ker.subtype.comp N

@[simp] theorem assemble_apply (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (x : E) :
    assemble A M₀ N x = M₀ x + (N x : K) := rfl

/-- Observed advice is completely unchanged by the private coordinates. -/
theorem observed_assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : A.comp (assemble A M₀ N) = A.comp M₀ := by
  ext x
  have hN : A (N x : K) = 0 := (N x).property
  simp only [LinearMap.comp_apply, assemble_apply, map_add, hN, add_zero]

/-- The exact row-fiber bijection; no rank or surjectivity premise is needed. -/
def rowFiberEquiv (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) :
    (E →ₗ[F2] A.ker) ≃ RowFiber A S where
  toFun N := ⟨assemble A M₀ N, (observed_assemble A M₀ N).trans h₀⟩
  invFun := kernelDifference A S M₀ h₀
  left_inv N := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M₀ x + (N x : K) - M₀ x = (N x : K)
    exact add_sub_cancel_left _ _
  right_inv M := by
    apply Subtype.ext
    ext x
    change M₀ x + (M.val x - M₀ x) = M.val x
    simpa only [← add_sub_assoc] using add_sub_cancel_left (M₀ x) (M.val x)

@[simp] theorem rowFiberEquiv_coe (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (N : E →ₗ[F2] A.ker) :
    (rowFiberEquiv A S M₀ h₀ N).val = assemble A M₀ N := rfl

@[simp] theorem rowFiberEquiv_symm (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    (rowFiberEquiv A S M₀ h₀).symm M = kernelDifference A S M₀ h₀ M := rfl

/-- Affine target intercepts are retained in the private coordinates. -/
theorem assemble_affine_target (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (z : E) (u : K) :
    assemble A M₀ N z + u = (N z : K) + (M₀ z + u) := by
  rw [assemble_apply]
  ac_rfl

section UniformFiber

variable (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
  [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] A.ker)]

omit [Fintype (E →ₗ[F2] K)] in
theorem rowFiber_card (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) :
    Nat.card (RowFiber A S) = Fintype.card (E →ₗ[F2] A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A S M₀ h₀).symm, Nat.card_eq_fintype_card]

omit [Fintype (E →ₗ[F2] K)] in
/-- Uniform private matrices push forward to uniform matrices in the fiber. -/
theorem rowFiber_expect (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S)
    [Fintype (RowFiber A S)] (f : (E →ₗ[F2] K) → ℝ) :
    (𝔼 M : RowFiber A S, f M.val) =
      𝔼 N : E →ₗ[F2] A.ker, f (assemble A M₀ N) := by
  exact (Fintype.expect_equiv (rowFiberEquiv A S M₀ h₀)
    (fun N => f (assemble A M₀ N)) (fun M => f M.val) (fun _ => rfl)).symm

end UniformFiber

/-- Only attainable rows are observation values. -/
abbrev ObservedRow (A : K →ₗ[F2] R) :=
  {S : E →ₗ[F2] R // ∃ M : E →ₗ[F2] K, A.comp M = S}

def observe (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) : ObservedRow (E := E) A :=
  ⟨A.comp M, M, rfl⟩

/-- A canonical base depends only on observed advice, never on the hidden matrix. -/
def observedBase (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) : E →ₗ[F2] K :=
  Classical.choose S.property

theorem observedBase_property (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) :
    A.comp (observedBase A S) = S.val := Classical.choose_spec S.property

def hiddenCoordinate (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    E →ₗ[F2] A.ker :=
  (rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
    (observedBase_property A (observe A M))).symm ⟨M, rfl⟩

theorem observe_assemble_base (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A)
    (N : E →ₗ[F2] A.ker) : observe A (assemble A (observedBase A S) N) = S := by
  apply Subtype.ext
  exact (observed_assemble A (observedBase A S) N).trans (observedBase_property A S)

/-- Full matrix space is a product of attainable visible rows and private
kernel-valued maps.  A section of `A` is not required. -/
def observationEquiv (A : K →ₗ[F2] R) :
    (E →ₗ[F2] K) ≃ ObservedRow (E := E) A × (E →ₗ[F2] A.ker) where
  toFun M := (observe A M, hiddenCoordinate A M)
  invFun p := assemble A (observedBase A p.1) p.2
  left_inv M := by
    exact congrArg Subtype.val
      ((rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
        (observedBase_property A (observe A M))).apply_symm_apply ⟨M, rfl⟩)
  right_inv p := by
    apply Prod.ext
    · exact observe_assemble_base A p.1 p.2
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      change assemble A (observedBase A p.1) p.2 x -
        observedBase A (observe A (assemble A (observedBase A p.1) p.2)) x =
          (p.2 x : K)
      rw [observe_assemble_base, assemble_apply]
      exact add_sub_cancel_left _ _

@[simp] theorem observationEquiv_apply (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    observationEquiv A M = (observe A M, hiddenCoordinate A M) := rfl

variable (A : K →ₗ[F2] R)
  [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] A.ker)] [Fintype (ObservedRow (E := E) A)]

/-- The joint law is exactly the uniform product law. -/
theorem observation_expect (f : ObservedRow (E := E) A → (E →ₗ[F2] A.ker) → ℝ) :
    (𝔼 M : E →ₗ[F2] K, f (observe A M) (hiddenCoordinate A M)) =
      𝔼 S : ObservedRow (E := E) A, 𝔼 N : E →ₗ[F2] A.ker, f S N := by
  rw [Fintype.expect_equiv (observationEquiv A)
    (fun M => f (observe A M) (hiddenCoordinate A M))
    (fun p => f p.1 p.2) (fun _ => rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Exact factorization of every product of visible and private observables. -/
theorem observed_hidden_independent (f : ObservedRow (E := E) A → ℝ)
    (g : (E →ₗ[F2] A.ker) → ℝ) :
    (𝔼 M : E →ₗ[F2] K, f (observe A M) * g (hiddenCoordinate A M)) =
      (𝔼 S : ObservedRow (E := E) A, f S) * (𝔼 N : E →ₗ[F2] A.ker, g N) := by
  rw [observation_expect A (fun S N => f S * g N)]
  simp_rw [← Finset.mul_expect]
  exact (Finset.expect_mul _ _ _).symm

end MaxCutGames.Decoder.AdviceFibers
end

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace MaxCutGames.Reduction.ActualOrbit

open MaxCutGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

abbrev Ambient (s d : Nat) := Vector s × Vector d

def body (can : Q → Ambient s d × T) (q : Q) : Vector d × T :=
  ((can q).1.2, (can q).2)

def offset (can : Q → Ambient s d × T) (q : Q) : Vector s := (can q).1.1

/-- Only realized bodies are vertices; no extra formal records are added. -/
def Vertex (can : Q → Ambient s d × T) := {o : Vector d × T // ∃ q, body can q = o}

def vertex (can : Q → Ambient s d × T) (q : Q) : Vertex can :=
  ⟨body can q, q, rfl⟩

theorem vertex_surjective (can : Q → Ambient s d × T) :
    Function.Surjective (vertex can) := by
  rintro ⟨o, q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

noncomputable instance vertexFintype [Fintype Q] (can : Q → Ambient s d × T) :
    Fintype (Vertex can) := by
  classical
  exact Fintype.ofSurjective (vertex can) (vertex_surjective can)

instance vertexNonempty [Nonempty Q] (can : Q → Ambient s d × T) :
    Nonempty (Vertex can) := Nonempty.map (vertex can) inferInstance

theorem vertex_eq_iff (can : Q → Ambient s d × T) (q r : Q) :
    vertex can q = vertex can r ↔ body can q = body can r := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

/-- `false` is the left copy and `true` is the right copy. -/
abbrev TwoSidedVertex (can : Q → Ambient s d × T) := Bool × Vertex can

noncomputable def vertexEquiv [Fintype Q] (can : Q → Ambient s d × T) :
    TwoSidedVertex can ≃ Fin (Fintype.card (TwoSidedVertex can)) :=
  Fintype.equivFin _

/-- Executable vertex numbering from an exhaustive list, preserving the same
realizable-body subtype used in the semantic statements. -/
def explicitVertexEquiv [DecidableEq (Vector d × T)]
    (can : Q → Ambient s d × T) (queries : List Q) (full : ∀ q, q ∈ queries) :
    Vertex can ≃ Fin (Encoding.imageVertices queries (body can)).length :=
  let e : Vertex can ≃ Encoding.ImageVertex queries (body can) :=
    { toFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mpr
        v.property⟩
      invFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mp
        v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.trans (Encoding.imageEquiv queries (body can))

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

theorem add_self_vector (c : Vector s) : c + c = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (c i)

theorem add_cancel_vector (a b : Vector s) : (a + b) + b = a := by
  rw [add_assoc, add_self_vector, add_zero]

/-- The precise orientation used by the generated edge. -/
theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  constructor
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'

/-- A common full canonical record has one common unfolded value on each side. -/
theorem unfold_eq_of_canonical_eq (can : Q → Ambient s d × T)
    (label : Vertex can → Vector s) (q r : Q) (h : can q = can r) :
    unfold can label q = unfold can label r := by
  have hv : vertex can q = vertex can r := by
    apply (vertex_eq_iff can q r).2
    exact congrArg (fun z : Ambient s d × T => (z.1.2, z.2)) h
  simp only [unfold, hv, offset, h]

end MaxCutGames.Reduction.ActualOrbit

end OAI
