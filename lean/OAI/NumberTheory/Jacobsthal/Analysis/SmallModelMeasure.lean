import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def modelUnitIntegers (R xi : ℝ) (H : ℕ) (C0 : ℤ) : Finset ℤ :=
  (modelIntegers R xi (H : ℝ) (C0 : ℝ)).filter (fun m => m.natAbs.Coprime H)

noncomputable def modelUniverse (R xi w : ℝ) (H : ℕ) (C0 : ℤ) : Finset (ModelPoint w H) :=
  (modelUnitIntegers R xi H C0).product Finset.univ

noncomputable def atomWeight (R xi w : ℝ) (H : ℕ) (C0 : ℤ) : ℝ :=
  (H : ℝ)/((H.totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)*
    (divisorModulus w H : ℝ)*((coprimeModulus w H).totient : ℝ))

noncomputable def modelMass (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (E : ModelPoint w H → Prop) : ℝ :=
  ∑ _v ∈ (modelUniverse R xi w H C0).filter E,atomWeight R xi w H C0

theorem mem_modelUniverse (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (v : ModelPoint w H) :
    v ∈ modelUniverse R xi w H C0 ↔
      modelLeft R xi (C0 : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < modelRight R xi (H : ℝ) (C0 : ℝ) ∧
        v.1.natAbs.Coprime H := by
  simp only [modelUniverse,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,and_true,
    modelUnitIntegers,Finset.mem_filter,mem_modelIntegers,and_assoc]

theorem atomWeight_pos (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    0 < atomWeight R xi w H C0 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hphi : (0 : ℝ) < H.totient := by exact_mod_cast Nat.totient_pos.mpr hH
  have hT0 : (0 : ℝ) < divisorModulus w H := by exact_mod_cast divisorModulus_pos w H
  have hT1 : (0 : ℝ) < (coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr (coprimeModulus_pos w H)
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    dsimp [modelLength,interceptScale]
    positivity
  unfold atomWeight
  positivity

theorem modelMass_card (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (E : ModelPoint w H → Prop) :
    modelMass R xi w H C0 E =
      (((modelUniverse R xi w H C0).filter E).card : ℝ)*atomWeight R xi w H C0 := by
  simp only [modelMass,Finset.sum_const,nsmul_eq_mul]

theorem modelUniverse_card (R xi w : ℝ) (H : ℕ) (C0 : ℤ) :
    (modelUniverse R xi w H C0).card =
      (modelUnitIntegers R xi H C0).card*(divisorModulus w H*(coprimeModulus w H).totient) := by
  simp only [modelUniverse,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,pattern_card]

theorem model_total_mass (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) :
    modelMass R xi w H C0 (fun _ => True) =
      ((modelUnitIntegers R xi H C0).card : ℝ)*(H : ℝ)/
        ((H.totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)) := by
  have hphi : (0 : ℝ) < H.totient := by exact_mod_cast Nat.totient_pos.mpr hH
  have hT0 : (0 : ℝ) < divisorModulus w H := by exact_mod_cast divisorModulus_pos w H
  have hT1 : (0 : ℝ) < (coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr (coprimeModulus_pos w H)
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    have hHR : (0 : ℝ) < H := by exact_mod_cast hH
    dsimp [modelLength,interceptScale]
    positivity
  rw [modelMass_card,Finset.filter_true,modelUniverse_card]
  simp only [Nat.cast_mul,atomWeight]
  field_simp

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
