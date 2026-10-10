import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.DominatedFactorization

namespace OAI

/-! Cohomology for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild

variable (M : Type*) [CStarAlgebra M]

def differentialLinearMap (k : ℕ) : Cochain M k →ₗ[ℂ] Cochain M (k+1) where
  toFun := differential
  map_add' f g := by
    ext v
    simp only [differential_apply, differentialValue_add, add_apply]
  map_smul' c f := by
    ext v
    simp only [differential_apply, differentialValue_smul, smul_apply, RingHom.id_apply]

def incomingDifferential : (k : ℕ) → Cochain M (k-1) →ₗ[ℂ] Cochain M k
  | 0 => 0
  | k+1 => differentialLinearMap M k

@[simp] lemma incomingDifferential_succ (k : ℕ) (g : Cochain M k) :
    incomingDifferential M (k+1) g = differential g := rfl

def cocycles (k : ℕ) : Submodule ℂ (Cochain M k) :=
  LinearMap.ker (differentialLinearMap M k)

@[simp] lemma mem_cocycles (k : ℕ) (f : Cochain M k) :
    f ∈ cocycles M k ↔ differential f = 0 := Iff.rfl

def coboundaries (k : ℕ) : Submodule ℂ (Cochain M k) :=
  LinearMap.range (incomingDifferential M k)

lemma coboundaries_le_cocycles (k : ℕ) : coboundaries M k ≤ cocycles M k := by
  rintro f ⟨g, rfl⟩
  change differential (incomingDifferential M k g) = 0
  cases k with
  | zero =>
    change differential (0 : Cochain M 0) = 0
    ext v
    simp [differentialValue]
  | succ k => exact differential_squared g

def incomingToCocycles (k : ℕ) : Cochain M (k-1) →ₗ[ℂ] cocycles M k :=
  (incomingDifferential M k).codRestrict (cocycles M k)
    (fun g => coboundaries_le_cocycles M k ⟨g, rfl⟩)

abbrev Cohomology (k : ℕ) :=
  (cocycles M k) ⧸ LinearMap.range (incomingToCocycles M k)

theorem cohomology_subsingleton_iff (k : ℕ) :
    Subsingleton (Cohomology M k) ↔
      ∀ f : Cochain M k, differential f = 0 →
        ∃ g : Cochain M (k-1), incomingDifferential M k g = f := by
  change Subsingleton ((cocycles M k) ⧸ LinearMap.range (incomingToCocycles M k)) ↔ _
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h f hf
    have hm : (⟨f, hf⟩ : cocycles M k) ∈ LinearMap.range (incomingToCocycles M k) := by
      rw [h]
      trivial
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, congrArg Subtype.val hg⟩
  · intro h
    apply (Submodule.eq_top_iff').mpr
    intro f
    obtain ⟨g, hg⟩ := h f f.property
    exact ⟨g, Subtype.ext hg⟩

end BoundedHochschild

end

end OAI
