import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion

abbrev Mat (n : Type) := Matrix n n ℂ
abbrev Map (n m : Type) := Mat n →ₗ[ℂ] Mat m

variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

def amplify (F : Map n m) {k : Type} (X : Mat (k × n)) : Mat (k × m) :=
  fun a b => F (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

def CP (F : Map n m) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Mat (k × n)), X.PosSemidef → (amplify F X).PosSemidef

def transposeMap : Map n n where
  toFun := Matrix.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def PPT (F : Map n m) : Prop := CP F ∧ CP (transposeMap.comp F)

def TracePreserving (F : Map n m) : Prop := ∀ X, Matrix.trace (F X) = Matrix.trace X

def Separable (Z : Mat (n × m)) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Mat n) (B : Fin r → Mat m),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
    Z = ∑ i, A i ⊗ₖ B i

def EntanglementBreaking (F : Map n m) : Prop :=
  CP F ∧ ∀ (k : Type) [Fintype k] (X : Mat (k × n)),
    X.PosSemidef → Separable (amplify F X)

end ChannelCompletion

namespace DimensionTen

/-- A trace-preserving PPT channel on twenty-one dimensions with a non-entanglement-breaking square. -/
theorem exists_channel_fin21 :
    ∃ Θ : ChannelCompletion.Map (Fin 21) (Fin 21),
      ChannelCompletion.PPT Θ ∧ ChannelCompletion.TracePreserving Θ ∧
        ¬ ChannelCompletion.EntanglementBreaking (Θ.comp Θ) := by
  sorry

end DimensionTen

end

end OAI
