import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.AtomicPhysicalKinetic
import OAI.Analysis.CoulombRadii.FieldAnalysis.FermionicNear

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def atomicNearConstant : ℝ := fermionicNearConstant*(atomicKineticConstant+1)
lemma atomicNearConstant_nonneg : 0≤atomicNearConstant := by
  have hT := thinReserveFactor_nonneg
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hC : 0≤atomicCountConstant := by linarith [atomicCountConstant_ge_two]
  unfold atomicNearConstant atomicKineticConstant
  exact mul_nonneg fermionicNearConstant_nonneg (by positivity)

theorem exists_atomic_near_scale : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
    ∀ (u : H1Vector n), Antisymmetric u → mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
    ∀ (y : Space), y≠0 → atomicCellScale y<s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∀ {R : ℝ}, 0≤R → R≤4*atomicCellScale y →
      potentialForm (nearPotential y R) u≤atomicNearConstant*(atomicCellScale y)^(-21/5:ℝ)*R^(1/5:ℝ) := by
  obtain ⟨s,hs,hs1,Hs⟩ := exists_atomic_small_kinetic
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom u hu hm E δ hE hstate hδ y hy hys hd R hR hRa
  obtain ⟨t,ht,T,ho,hcore,hout,hK⟩ := Hs S hatom u hu hm hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have H := T.ensemble.nearPotential_le u T.law ho y hR
    (hRa.trans (by linarith [ht.1] : 4*atomicCellScale y≤t))
    (Real.rpow_pos_of_pos ha (-7:ℝ)) hcore
  rw [T.mass_eq,hm,mul_one] at H
  calc
    _≤_ := H
    _≤fermionicNearConstant*R^(1/5:ℝ)*
        ((a^(-7:ℝ))^(-2/5:ℝ)*(atomicKineticConstant*a^(-7:ℝ))+(a^(-7:ℝ))^(3/5:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg hR _))
      have hh := mul_le_mul_of_nonneg_left hK
        (Real.rpow_nonneg (Real.rpow_nonneg ha.le (-7)) (-2/5))
      simpa only [add_comm] using add_le_add_right hh ((a^(-7:ℝ))^(3/5:ℝ))
    _=_ := by
      rw [←Real.rpow_mul ha.le,←Real.rpow_mul ha.le]
      have he : a^((-7)*(-2/5):ℝ)*(atomicKineticConstant*a^(-7:ℝ))=
          atomicKineticConstant*a^(-21/5:ℝ) := by
        rw [mul_left_comm,←Real.rpow_add ha]
        norm_num
      rw [he]
      norm_num only at *
      unfold atomicNearConstant
      ring
end Coulomb
end

end
end

end OAI
