import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticeGenerators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicPowerIndex

namespace OAI

/-! # Finite-index powers in an integral vector lattice -/

noncomputable section
namespace PolycyclicRecognition

def latticePowerHom (n m : ℕ) : IntegralLatticeGroup n →* IntegralLatticeGroup n where
  toFun z := z ^ m
  map_one' := one_pow m
  map_mul' z w := (Commute.all z w).mul_pow m

def latticeCoordinateHom (n : ℕ) (i : Fin n) : IntegralLatticeGroup n →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem latticePowerHom_injective (n : ℕ) {m : ℕ} (hm : 0 < m) :
    Function.Injective (latticePowerHom n m) := by
  intro z w h
  apply Multiplicative.ext
  funext i
  have hi := congrArg (fun a : IntegralLatticeGroup n => a.toAdd i) h
  change (m : ℤ) * z.toAdd i = (m : ℤ) * w.toAdd i at hi
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hm) hi

theorem latticePowerHom_range (n m : ℕ) :
    (latticePowerHom n m).range =
      ⨅ i, (integerScaleHom m).range.comap (latticeCoordinateHom n i) := by
  ext z
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨Multiplicative.ofAdd (w.toAdd i), rfl⟩
  · intro h
    choose w hw using h
    refine ⟨Multiplicative.ofAdd (fun i => (w i).toAdd), ?_⟩
    apply Multiplicative.ext
    funext i
    exact congrArg Multiplicative.toAdd (hw i)

theorem latticePowerHom_finiteIndex (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (latticePowerHom n m).range.FiniteIndex := by
  let := integerScaleHom_range_finiteIndex hm
  rw [latticePowerHom_range]
  apply Subgroup.finiteIndex_iInf
  intro i
  infer_instance

variable {H : Type} [Group H]

def integralSemidirectPowerMap {n : ℕ} (ρ : IntegralLatticeGroup n →* MulAut H) (m : ℕ) :
    (H ⋊[ρ.comp (latticePowerHom n m)] IntegralLatticeGroup n) →*
      (H ⋊[ρ] IntegralLatticeGroup n) :=
  SemidirectProduct.map (MonoidHom.id H) (latticePowerHom n m) (by intros; rfl)

theorem integralSemidirectPowerMap_injective {n m : ℕ} (ρ : IntegralLatticeGroup n →* MulAut H)
    (hm : 0 < m) : Function.Injective (integralSemidirectPowerMap ρ m) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun z : H ⋊[ρ] IntegralLatticeGroup n => z.left) h
  · exact latticePowerHom_injective n hm
      (congrArg (fun z : H ⋊[ρ] IntegralLatticeGroup n => z.right) h)

theorem integralSemidirectPowerMap_range {n : ℕ} (ρ : IntegralLatticeGroup n →* MulAut H) (m : ℕ) :
    (integralSemidirectPowerMap ρ m).range =
      (latticePowerHom n m).range.comap SemidirectProduct.rightHom := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.right, rfl⟩
  · rintro ⟨v, hv⟩
    refine ⟨⟨g.left, v⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hv

theorem integralSemidirectPowerMap_finiteIndex {n m : ℕ} (ρ : IntegralLatticeGroup n →* MulAut H)
    (hm : 0 < m) : (integralSemidirectPowerMap ρ m).range.FiniteIndex := by
  let := latticePowerHom_finiteIndex n hm
  rw [integralSemidirectPowerMap_range]
  infer_instance

end PolycyclicRecognition

end

end OAI
