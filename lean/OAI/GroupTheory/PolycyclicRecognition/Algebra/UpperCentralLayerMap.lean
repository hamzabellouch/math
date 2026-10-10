import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCentralLayers
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EquivariantCommutatorFiltration

namespace OAI

/-! # Equivariant rational maps from the actual upper central series -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

omit [F.Normal] in
theorem mem_ambientUpperCentralSeries_iff (i : ℕ) (a : F) :
    (a : G) ∈ ambientUpperCentralSeries F i ↔ a ∈ Subgroup.upperCentralSeries F i := by
  constructor
  · rintro ⟨b, hb, he⟩
    have he' : b = a := Subtype.val_injective he
    cases he'
    exact hb
  · exact fun ha => ⟨a, ha, rfl⟩

def ambientUpperCentralToF (i : ℕ) : ambientUpperCentralSeries F i →* F :=
  Subgroup.inclusion (Subgroup.map_subtype_le (Subgroup.upperCentralSeries F i))

def upperCentralLayerMap (i : ℕ) : ambientUpperCentralSeries F (i + 1) →* CentralLayer F i where
  toFun a := ⟨QuotientGroup.mk' (Subgroup.upperCentralSeries F i)
    (ambientUpperCentralToF F (i + 1) a), by
      change ambientUpperCentralToF F (i + 1) a ∈
        (Subgroup.center _).comap (QuotientGroup.mk' (Subgroup.upperCentralSeries F i))
      rw [← Subgroup.upperCentralSeriesStep_eq_comap_center]
      exact (mem_ambientUpperCentralSeries_iff F (i + 1) _).mp a.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

theorem upperCentralLayerMap_equivariant (i : ℕ) (g : G)
    (a : ambientUpperCentralSeries F (i + 1)) :
    upperCentralLayerMap F i (MulAut.conjNormal g a) =
      upperCentralLayerAut F i g (upperCentralLayerMap F i a) := by
  apply Subtype.ext
  change QuotientGroup.mk' (Subgroup.upperCentralSeries F i) _ =
    characteristicQuotientAut (Subgroup.upperCentralSeries F i)
      (MulAut.conjNormal (H := F) g)
      (QuotientGroup.mk' (Subgroup.upperCentralSeries F i) _)
  rw [characteristicQuotientAut_mk]
  rfl

def rationalUpperCentralMap (i : ℕ) :
    ambientUpperCentralSeries F (i + 1) →* Multiplicative (RationalAbelianSpace (CentralLayer F i)) where
  toFun a := Multiplicative.ofAdd (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a)))
  map_one' := by simp
  map_mul' a b := by simp

theorem rationalUpperCentralMap_equivariant (i : ℕ) (g : G)
    (a : ambientUpperCentralSeries F (i + 1)) :
    (rationalUpperCentralMap F i (MulAut.conjNormal g a)).toAdd =
      rationalUpperCentralAction F i g (rationalUpperCentralMap F i a).toAdd := by
  change rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i (MulAut.conjNormal g a))) =
    rationalAbelianAut (upperCentralLayerAut F i g)
      (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a)))
  change rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i (MulAut.conjNormal g a))) =
    rationalAbelianMap (Additive.ofMul (upperCentralLayerAut F i g (upperCentralLayerMap F i a)))
  rw [upperCentralLayerMap_equivariant]

omit [F.Normal] in
theorem rationalUpperCentralMap_kernel [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F) (i : ℕ) :
    (rationalUpperCentralMap F i).ker.map (ambientUpperCentralSeries F (i + 1)).subtype =
      ambientUpperCentralSeries F i := by
  have hQ := nilpotent_upperCentralQuotient_torsionFree hF i
  have hZ : HasNoNontrivialTorsion (CentralLayer F i) :=
    hQ.of_injective (Subgroup.center _).subtype Subtype.val_injective
  have hker (a : ambientUpperCentralSeries F (i + 1)) :
      a ∈ (rationalUpperCentralMap F i).ker ↔ (a : G) ∈ ambientUpperCentralSeries F i := by
    change Multiplicative.ofAdd (rationalAbelianMap (Additive.ofMul (upperCentralLayerMap F i a))) = 1 ↔ _
    change _ ↔ (ambientUpperCentralToF F (i + 1) a : G) ∈ ambientUpperCentralSeries F i
    rw [mem_ambientUpperCentralSeries_iff]
    constructor
    · intro ha
      have hz : upperCentralLayerMap F i a = 1 := by
        apply Additive.ofMul.injective
        apply rationalAbelianMap_injective hZ
        simpa only [ofMul_one, map_zero, toAdd_ofAdd, toAdd_one] using
          congrArg Multiplicative.toAdd ha
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hz)
    · intro ha
      have hz : upperCentralLayerMap F i a = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff _).mpr ha)
      simp only [hz, ofMul_one, map_zero, ofAdd_zero]
  apply le_antisymm
  · rintro g ⟨a, ha, rfl⟩
    exact (hker a).mp ha
  · intro g hg
    have hg' : g ∈ ambientUpperCentralSeries F (i + 1) :=
      ambientUpperCentralSeries_mono F (Nat.le_succ i) hg
    exact ⟨⟨g, hg'⟩, (hker _).mpr hg, rfl⟩

end PolycyclicRecognition

end

end OAI
