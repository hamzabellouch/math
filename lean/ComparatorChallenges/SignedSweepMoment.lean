import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct
open Module

namespace SignedSweeps

abbrev Partition (n : ℕ) := {lam : YoungDiagram // lam.card = n}

abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

namespace Partition

def transpose {n : ℕ} (lam : Partition n) : Partition n :=
  ⟨lam.1.transpose, by simpa [YoungDiagram.card, YoungDiagram.transpose] using lam.2⟩

def tableau {n : ℕ} (lam : Partition n) : {c // c ∈ lam.1.cells} ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa using lam.2)

def rowOf {n : ℕ} (lam : Partition n) (x : Fin n) : ℕ :=
  ((tableau lam).symm x).1.1

def colOf {n : ℕ} (lam : Partition n) (x : Fin n) : ℕ :=
  ((tableau lam).symm x).1.2

end Partition

def fiberSubgroup {A C : Type*} (f : A → C) : Subgroup (Equiv.Perm A) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

def rowSubgroup {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  fiberSubgroup lam.rowOf

def colSubgroup {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  fiberSubgroup lam.colOf

abbrev RegularSpace (n : ℕ) := EuclideanSpace ℂ (SymmetricGroup n)

def regularIsometry {n : ℕ} (g : SymmetricGroup n) :
    RegularSpace n ≃ₗᵢ[ℂ] RegularSpace n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)

@[simp]
lemma regularIsometry_apply {n : ℕ} (g : SymmetricGroup n)
    (f : RegularSpace n) (h : SymmetricGroup n) :
    regularIsometry g f h = f (g⁻¹ * h) := rfl

def regularRepresentation (n : ℕ) : Representation ℂ (SymmetricGroup n) (RegularSpace n) where
  toFun g := (regularIsometry g).toLinearEquiv.toLinearMap
  map_one' := by ext f h; simp
  map_mul' := by
    intro g h
    ext f k
    simp [mul_assoc]

@[simp]
lemma regularRepresentation_apply {n : ℕ} (g : SymmetricGroup n)
    (f : RegularSpace n) (h : SymmetricGroup n) :
    regularRepresentation n g f h = f (g⁻¹ * h) := rfl

def polytabloid {n : ℕ} (lam : Partition n) : RegularSpace n := by
  classical
  exact ∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    (((Equiv.Perm.sign (c : SymmetricGroup n) : ℤˣ) : ℤ) : ℂ) •
      EuclideanSpace.single ((c : SymmetricGroup n) * (a : SymmetricGroup n)) 1

def spechtSubrepresentation {n : ℕ} (lam : Partition n) :
    Subrepresentation (regularRepresentation n) where
  toSubmodule := Submodule.span ℂ (Set.range (fun g => regularRepresentation n g (polytabloid lam)))
  apply_mem_toSubmodule := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨h, rfl⟩ := hv
        apply Submodule.subset_span
        refine ⟨g * h, ?_⟩
        simp [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
        simpa only [map_smul] using Submodule.smul_mem _ a ih

def Specht {n : ℕ} (lam : Partition n) : Type := (spechtSubrepresentation lam).toSubmodule

instance spechtNormedAddCommGroup {n : ℕ} (lam : Partition n) : NormedAddCommGroup (Specht lam) :=
  inferInstanceAs (NormedAddCommGroup (spechtSubrepresentation lam).toSubmodule)

instance spechtInnerProductSpace {n : ℕ} (lam : Partition n) : InnerProductSpace ℂ (Specht lam) :=
  inferInstanceAs (InnerProductSpace ℂ (spechtSubrepresentation lam).toSubmodule)

instance spechtFiniteDimensional {n : ℕ} (lam : Partition n) : FiniteDimensional ℂ (Specht lam) :=
  inferInstanceAs (FiniteDimensional ℂ (spechtSubrepresentation lam).toSubmodule)

def spechtRepresentation {n : ℕ} (lam : Partition n) :
    Representation ℂ (SymmetricGroup n) (Specht lam) :=
  (spechtSubrepresentation lam).toRepresentation

def spechtDimension {n : ℕ} (lam : Partition n) : ℕ := finrank ℂ (Specht lam)

def blockEmbedding {u v l n : ℕ} (h : u + v + l = n)
    (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) :
    SymmetricGroup n :=
  let e : (Fin u ⊕ Fin v) ⊕ Fin l ≃ Fin n :=
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin l))).trans finSumFinEquiv).trans
      (finCongr h)
  e.permCongr ((a.sumCongr b).sumCongr c)

def SignedOccurrence {u v l n : ℕ} (h : u + v + l = n)
    (α : Partition u) (β : Partition v) (γ : Partition l) (lam : Partition n) : Prop :=
  ∃ f : ((Specht α ⊗[ℂ] Specht β.transpose) ⊗[ℂ] Specht γ) →ₗ[ℂ] Specht lam,
    Function.Injective f ∧
    ∀ (a : SymmetricGroup u) (b : SymmetricGroup v) (c : SymmetricGroup l) x,
      f (TensorProduct.map
        (TensorProduct.map (spechtRepresentation α a) (spechtRepresentation β.transpose b))
        (spechtRepresentation γ c) x) =
      spechtRepresentation lam (blockEmbedding h a b c) (f x)

abbrev BinaryPositions (d : ℕ) := Fin d → Fin 2

def positionsEquiv (d : ℕ) : BinaryPositions d ≃ Fin (2 ^ d) :=
  Fintype.equivFinOfCardEq (by simp [BinaryPositions])

def coordinateSubgroup (d : ℕ) (i : Fin d) : Subgroup (SymmetricGroup (2 ^ d)) :=
  fiberSubgroup (fun x : Fin (2 ^ d) =>
    fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)

def layerOperator {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) :
    Specht lam →ₗ[ℂ] Specht lam := by
  classical
  exact (Fintype.card (coordinateSubgroup d i) : ℂ)⁻¹ •
    ∑ g : coordinateSubgroup d i, spechtRepresentation lam g.1

def sweepOperator {d : ℕ} (lam : Partition (2 ^ d)) : Specht lam →ₗ[ℂ] Specht lam :=
  ((List.ofFn (layerOperator lam)).reverse).prod

def positiveSquare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := T.adjoint * T

def sweepSquare {d : ℕ} (lam : Partition (2 ^ d)) : Specht lam →ₗ[ℂ] Specht lam :=
  positiveSquare (E := Specht lam) (sweepOperator lam)

def weightedMoment {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) : ℝ :=
  (spechtDimension lam : ℝ) * (LinearMap.trace ℂ (Specht lam) (sweepSquare lam ^ r)).re

def logMoment (x : ℝ) : EReal := if x = 0 then ⊥ else (Real.log x : EReal)

def signedEntropy {u v : ℕ} (α : Partition u) (β : Partition v) : ℝ :=
  ((α.1.rowLens ++ β.1.rowLens).map
    (fun a : ℕ => (a : ℝ) * Real.log (((u : ℝ) + v) / a))).sum

def coefficient (a : ℝ) (d : ℕ) : ℝ := a * (1 - 1 / (2 * Real.sqrt d))

def remainderBudget (κ : ℝ) (d l : ℕ) : ℝ :=
  if l = 0 then 0 else
    max 0 (coefficient κ d * l * Real.log (2 ^ d : ℕ) -
      (l : ℝ) * Real.log ((2 ^ d : ℕ) / (l : ℝ)))

theorem signed_occurrence_moment_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < η / 256 ∧
          ∀ κ : ℝ, 0 < κ → κ < κ₀ →
            ∃ r : ℕ, 1 ≤ r ∧
              ∀ d : ℕ, 1 ≤ d →
                ∀ lam : Partition (2 ^ d),
                  ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
                    (α : Partition u) (β : Partition v) (γ : Partition l),
                    SignedOccurrence h α β γ lam →
                      logMoment (weightedMoment lam r) ≤
                        ((coefficient η d * signedEntropy α β +
                            remainderBudget κ d l : ℝ) : EReal) := by
  sorry

end SignedSweeps

end

end OAI
