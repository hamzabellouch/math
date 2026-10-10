import OAI.NumberTheory.Ostmann.QuadraticCenter.NormalizedQuadraticGrid

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

structure AdaptiveArrayParameters where
  modulusResidue : ℕ
  phaseResidue : ℕ
  multiple : ℕ
  theta : ℝ
  radius : ℝ

def adaptiveArrayParameters (L Z : ℕ) : Finset AdaptiveArrayParameters := by
  classical
  exact (((Finset.range (4*L)).product (Finset.range L)).product
    ((Finset.Icc 1 (Z^7)).product
      ((parameterGrid 0 1 (Z^200)).product (parameterGrid 1 (2*Z^13) (Z^200))))).image
    (fun x => ⟨x.1.1,x.1.2,x.2.1,x.2.2.1,x.2.2.2⟩)

theorem adaptiveArrayParameters_card_raw (L Z : ℕ) :
    (adaptiveArrayParameters L Z).card ≤
      (4*L)*L*(Z^7*((Z^200+1)*(2*Z^13*Z^200+1))) := by
  classical
  unfold adaptiveArrayParameters
  apply Finset.card_image_le.trans
  simp only [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,Nat.card_Icc,Nat.add_sub_cancel]
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  simpa only [Finset.product_eq_sprod,Finset.card_product] using
    parameter_pair_card_le (2*Z^13) (Z^200)

private theorem add_one_pow_le {Z : ℕ} (hZ : 2 ≤ Z) (k : ℕ) :
    Z^k+1 ≤ Z^(k+1) := by
  have hp : 1 ≤ Z^k := Nat.one_le_pow k Z (by omega)
  rw [pow_succ]
  nlinarith

theorem adaptiveArrayParameters_card {L Z : ℕ} (hZ : 2 ≤ Z) (hL : L ≤ Z) :
    (adaptiveArrayParameters L Z).card ≤ Z^430 := by
  have hfirst : 4*L ≤ Z^3 := by
    have hsq : 4 ≤ Z^2 := by nlinarith
    calc
      _ ≤ 4*Z := Nat.mul_le_mul_left _ hL
      _ ≤ Z^2*Z := Nat.mul_le_mul_right _ hsq
      _ = Z^3 := by ring
  have htheta : Z^200+1 ≤ Z^201 := add_one_pow_le hZ 200
  have hrad : 2*Z^13*Z^200+1 ≤ Z^215 := by
    have hp : 1 ≤ Z^213 := Nat.one_le_pow _ _ (by omega)
    have hsq : 4 ≤ Z^2 := by nlinarith
    have hid : 2*Z^13*Z^200=2*Z^213 := by ring
    rw [hid]
    calc
      _ ≤ Z^213*Z^2 := by nlinarith
      _ = Z^215 := by ring
  calc
    _ ≤ (4*L)*L*(Z^7*((Z^200+1)*(2*Z^13*Z^200+1))) := adaptiveArrayParameters_card_raw L Z
    _ ≤ Z^3*Z*(Z^7*(Z^201*Z^215)) := by gcongr
    _ = Z^427 := by ring
    _ ≤ Z^430 := pow_le_pow_right' (a := Z)
      (le_trans (by decide : 1 ≤ 2) hZ) (by decide : 427 ≤ 430)

theorem mem_adaptiveArrayParameters {L Z : ℕ} {a : AdaptiveArrayParameters}
    (ha : a ∈ adaptiveArrayParameters L Z) (hZ : 0 < Z) :
    a.modulusResidue < 4*L ∧ a.phaseResidue < L ∧
      1 ≤ a.multiple ∧ a.multiple ≤ Z^7 ∧
      0 ≤ a.theta ∧ a.theta ≤ 1 ∧ 1 ≤ a.radius ∧ a.radius ≤ (2*Z^13:ℕ) := by
  classical
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hmh,hrest⟩ := Finset.mem_product.mp hx
  obtain ⟨hM,hh⟩ := Finset.mem_product.mp hmh
  obtain ⟨hP,hgr⟩ := Finset.mem_product.mp hrest
  obtain ⟨ht,hR⟩ := Finset.mem_product.mp hgr
  have ht := mem_parameterGrid_bounds (pow_pos hZ 200) ht
  have hR := mem_parameterGrid_bounds (pow_pos hZ 200) hR
  exact ⟨Finset.mem_range.mp hM,Finset.mem_range.mp hh,(Finset.mem_Icc.mp hP).1,
    (Finset.mem_Icc.mp hP).2,by simpa using ht.1,by simpa using ht.2,
    by simpa using hR.1,hR.2⟩

theorem exists_near_adaptiveArrayParameters {L Z M h P : ℕ} (hZ : 0 < Z)
    (hM : M < 4*L) (hh : h < L) (hP : 1 ≤ P) (hPZ : P ≤ Z^7)
    {θ R : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hR1 : 1 ≤ R)
    (hRB : R ≤ (2*Z^13:ℕ)) :
    ∃ a ∈ adaptiveArrayParameters L Z,
      a.modulusResidue=M ∧ a.phaseResidue=h ∧ a.multiple=P ∧
      |θ-a.theta| ≤ 1/(Z^200:ℕ) ∧ |R-a.radius| ≤ 1/(Z^200:ℕ) := by
  classical
  obtain ⟨z,hz,ht,hR,hzR⟩ := exists_near_parameter_pair (pow_pos hZ 200) ht0 ht1 hR1 hRB
  refine ⟨⟨M,h,P,z.1,z.2⟩,?_,rfl,rfl,rfl,ht,hR⟩
  exact Finset.mem_image.mpr ⟨((M,h),(P,z)),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hM,
      Finset.mem_range.mpr hh⟩,Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hP,hPZ⟩,hz⟩⟩,rfl⟩

end Ostmann.QuadraticCenter

end

end OAI
