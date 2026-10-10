import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MaximalNilpotentCentralAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentUpperCentralRoots

namespace OAI

/-! # Rational actions on the upper central layers

Ambient conjugation preserves the characteristic upper central series.
On each central layer it therefore gives a rational linear action. Trivial
rational action implies trivial action on the layer itself, since the
successive quotients are torsion-free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

abbrev CentralLayer (i : ℕ) := Subgroup.center (F ⧸ Subgroup.upperCentralSeries F i)

def upperCentralLayerAut (i : ℕ) : G →* MulAut (CentralLayer F i) :=
  (MulAut.characteristic (Subgroup.center (F ⧸ Subgroup.upperCentralSeries F i))).comp
    ((characteristicQuotientAut (Subgroup.upperCentralSeries F i)).comp
      (MulAut.conjNormal (H := F)))

def rationalUpperCentralAction (i : ℕ) :
    G →* (RationalAbelianSpace (CentralLayer F i) ≃ₗ[ℚ]
      RationalAbelianSpace (CentralLayer F i)) :=
  rationalAbelianAut.comp (upperCentralLayerAut F i)

theorem upperCentralLayerAut_eq_one_of_rational [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) (g : G)
    (hg : rationalUpperCentralAction F i g = 1) : upperCentralLayerAut F i g = 1 := by
  have hQ := nilpotent_upperCentralQuotient_torsionFree hF i
  have hZ : HasNoNontrivialTorsion (CentralLayer F i) :=
    hQ.of_injective (Subgroup.center _).subtype Subtype.val_injective
  apply rationalAbelianAut_injective hZ
  simpa only [rationalUpperCentralAction, MonoidHom.comp_apply, map_one] using hg

theorem commutator_centralLayer_le_of_rational_kernel [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) (K : Subgroup G)
    (hK : K ≤ (rationalUpperCentralAction F i).ker) :
    ⁅K, ambientUpperCentralSeries F (i + 1)⁆ ≤ ambientUpperCentralSeries F i := by
  apply Subgroup.commutator_le.mpr
  intro g hg a ha
  obtain ⟨b, hb, rfl⟩ := ha
  let U := Subgroup.upperCentralSeries F i
  let q := QuotientGroup.mk' U
  have hbZ : q b ∈ Subgroup.center (F ⧸ U) := by
    change b ∈ (Subgroup.center (F ⧸ U)).comap q
    rw [← Subgroup.upperCentralSeriesStep_eq_comap_center]
    exact hb
  have hfix := upperCentralLayerAut_eq_one_of_rational F hF i g (hK hg)
  have hqb : q ((MulAut.conjNormal (H := F) g) b) = q b := by
    have hh := congrArg
      (fun e : MulAut (CentralLayer F i) => ((e ⟨q b, hbZ⟩ : CentralLayer F i) : F ⧸ U)) hfix
    exact hh
  have hdiff : (MulAut.conjNormal (H := F) g) b * b⁻¹ ∈ U := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((MulAut.conjNormal (H := F) g) b * b⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]
  refine ⟨(MulAut.conjNormal (H := F) g) b * b⁻¹, hdiff, ?_⟩
  rfl

theorem subgroup_le_rationalUpperCentralAction_ker (i : ℕ) :
    F ≤ (rationalUpperCentralAction F i).ker := by
  intro g hg
  let a : F := ⟨g, hg⟩
  let U := Subgroup.upperCentralSeries F i
  let q := QuotientGroup.mk' U
  have he : upperCentralLayerAut F i g = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective U (z : F ⧸ U)
    change characteristicQuotientAut U (MulAut.conjNormal (H := F) g) (z : F ⧸ U) = z
    rw [← hb, characteristicQuotientAut_mk]
    change q (a * b * a⁻¹) = q b
    rw [map_mul, map_mul, map_inv]
    have hcomm : q a * q b = q b * q a := by
      rw [hb]
      exact Subgroup.mem_center_iff.mp z.property (q a)
    rw [hcomm, mul_inv_cancel_right]
  change rationalAbelianAut (upperCentralLayerAut F i g) = 1
  rw [he, map_one]

end PolycyclicRecognition

end

end OAI
