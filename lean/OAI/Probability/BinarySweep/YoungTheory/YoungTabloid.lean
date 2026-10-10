import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungFactor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
abbrev G := Equiv.Perm (Cell μ)

def labels (π : G μ) : Cell μ → ℕ := fun x => row (π⁻¹ x)

def Tabloid := Set.range (labels μ)

def tabloidOfPerm (π : G μ) : Tabloid μ := ⟨labels μ π, π, rfl⟩

lemma tabloidOfPerm_surjective : Function.Surjective (tabloidOfPerm μ) := by
  rintro ⟨f, π, rfl⟩
  exact ⟨π, rfl⟩

instance : Fintype (Tabloid μ) := Fintype.ofSurjective _ (tabloidOfPerm_surjective μ)
instance : DecidableEq (Tabloid μ) := Classical.decEq _

noncomputable def actTabloid (π : G μ) (t : Tabloid μ) : Tabloid μ := by
  refine ⟨fun x => t.val (π⁻¹ x), ?_⟩
  obtain ⟨g, hg⟩ := t.property
  refine ⟨π * g, ?_⟩
  ext x
  simp [labels, ← hg]

instance : MulAction (G μ) (Tabloid μ) where
  smul := actTabloid μ
  one_smul t := by
    change actTabloid μ 1 t = t
    apply Subtype.ext
    funext x
    simp [actTabloid]
  mul_smul π σ t := by
    change actTabloid μ (π * σ) t = actTabloid μ π (actTabloid μ σ t)
    apply Subtype.ext
    funext x
    simp [actTabloid]

lemma smul_tabloid_apply (π : G μ) (t : Tabloid μ) (x : Cell μ) :
    (π • t).val x = t.val (π⁻¹ x) := rfl

@[simp] lemma smul_tabloidOfPerm (π σ : G μ) :
    π • tabloidOfPerm μ σ = tabloidOfPerm μ (π * σ) := by
  apply Subtype.ext
  funext x
  simp [smul_tabloid_apply, tabloidOfPerm, labels]

lemma tabloidOfPerm_eq_iff (π σ : G μ) :
    tabloidOfPerm μ π = tabloidOfPerm μ σ ↔ π⁻¹ * σ ∈ rowStabilizer μ := by
  constructor
  · intro h x
    have he := congrArg (fun t : Tabloid μ => t.val (σ x)) h
    simpa [tabloidOfPerm, labels] using he
  · intro h
    apply Subtype.ext
    funext x
    have he := h (σ⁻¹ x)
    simpa [tabloidOfPerm, labels] using he

lemma tabloidOfPerm_row_mul (π : G μ) (r : rowStabilizer μ) :
    tabloidOfPerm μ (π * r.val) = tabloidOfPerm μ π := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  simp

def tabloidRepresentation : Representation ℂ (G μ) (Tabloid μ → ℂ) where
  toFun π :=
    { toFun := fun v t => v (π⁻¹ • t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v t; simp
  map_mul' π σ := by ext v t; simp [mul_smul]

lemma tabloidRepresentation_apply (π : G μ) (v : Tabloid μ → ℂ) (t : Tabloid μ) :
    tabloidRepresentation μ π v t = v (π⁻¹ • t) := rfl

def tabloidBasis (t : Tabloid μ) : Tabloid μ → ℂ := Pi.single t 1

lemma rep_basis (π : G μ) (t : Tabloid μ) :
    tabloidRepresentation μ π (tabloidBasis μ t) = tabloidBasis μ (π • t) := by
  ext u
  simp only [tabloidRepresentation_apply, tabloidBasis, Pi.single_apply]
  simp only [inv_smul_eq_iff]

end BinaryCoordinateSweeps.Young

end

end OAI
