import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugateCharacterLog
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace OAI

/-! # The finitely generated group of nonzero spectral values

We include the conjugate eigenvalues so the resulting group has its actual
conjugation involution, independently of a later choice of logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def spectralUnits (S : Module.End ℂ V) : Set ℂˣ :=
  {z | S.HasEigenvalue (z : ℂ)}

theorem spectralUnits_finite (S : Module.End ℂ V) : (spectralUnits S).Finite :=
  S.finite_hasEigenvalue.preimage Units.val_injective.injOn

def spectralUnitGroup (S : Module.End ℂ V) : Subgroup ℂˣ :=
  Subgroup.closure (spectralUnits S ∪ star '' spectralUnits S)

instance spectralUnitGroup_fg (S : Module.End ℂ V) : Group.FG (spectralUnitGroup S) := by
  let : Finite ↥(spectralUnits S ∪ star '' spectralUnits S : Set ℂˣ) :=
    ((spectralUnits_finite S).union ((spectralUnits_finite S).image star)).to_subtype
  exact Group.closure_finite_fg _

omit [FiniteDimensional ℂ V] in
theorem spectralUnitGroup_star (S : Module.End ℂ V) {z : ℂˣ}
    (hz : z ∈ spectralUnitGroup S) : star z ∈ spectralUnitGroup S := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩)
    · have hw' : w ∈ spectralUnitGroup S := Subgroup.subset_closure (Or.inl hw)
      simpa only [star_star] using hw'
  | one => simp
  | mul x y _ _ hx hy =>
    simpa only [star_mul] using (spectralUnitGroup S).mul_mem hy hx
  | inv x _ hx => simpa only [star_inv] using (spectralUnitGroup S).inv_mem hx

def spectralUnitConjugation (S : Module.End ℂ V) : spectralUnitGroup S →* spectralUnitGroup S where
  toFun z := ⟨star z.val, spectralUnitGroup_star S z.property⟩
  map_one' := by apply Subtype.ext; exact star_one _
  map_mul' x y := by apply Subtype.ext; simp [star_mul, mul_comm]

omit [FiniteDimensional ℂ V] in
theorem spectralUnitConjugation_involutive (S : Module.End ℂ V)
    (z : spectralUnitGroup S) :
    spectralUnitConjugation S (spectralUnitConjugation S z) = z := by
  apply Subtype.ext
  exact star_star z.val

theorem spectralUnitGroup_logarithm (S : Module.End ℂ V) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : spectralUnitGroup S →* Multiplicative ℂ,
      (∀ z, complexUnitExp (L z) = z.val ^ m) ∧
      (∀ z, (L (spectralUnitConjugation S z)).toAdd = star (L z).toAdd) := by
  exact finitelyGenerated_real_character_power_log (spectralUnitGroup S).subtype
    (spectralUnitConjugation S) (spectralUnitConjugation_involutive S) (fun _ => rfl)

end PolycyclicRecognition

end

end OAI
