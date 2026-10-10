import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CountUnits
import OAI.Analysis.CoulombRadii.Packets.ScreenBox

namespace OAI

noncomputable section

namespace Coulomb

lemma screening_ims_units {P a m : ℝ} (hP : 1 ≤ P) (ha : 0<a) (hm : 0 ≤ m)
    (hscale : 1 ≤ a*m) : Real.sqrt P*m/a^2 ≤ P*m^2/a := by
  have hp0 : 0 ≤ P := by linarith
  have hs : Real.sqrt P ≤ P := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hp0,by nlinarith⟩
  have hmass : m ≤ a*m^2 := by nlinarith [mul_le_mul_of_nonneg_left hscale hm]
  calc
    _ ≤ P*m/a^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hm) (sq_nonneg _)
    _ ≤ P*(a*m^2)/a^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hp0) (sq_nonneg _)
    _ = _ := by field_simp

lemma screening_gain_normalized {a b q K P e w r B : ℝ}
    (ha : 0<a) (hb : 0<b) (hq : 0<q) (hK : 0<K) (hw : 0<w)
    (hr : 0 ≤ r) (hscale : a ≤ q*b) (hunit : a*w^2=P*e)
    (hgain : b/(16*K)*r ≤ P*q^7*e*B) :
    (Real.sqrt r/w)^2 ≤ 16*K*q^8*B := by
  rw [div_pow,Real.sq_sqrt hr,div_le_iff₀ (sq_pos_of_pos hw)]
  have hg : b*r ≤ 16*K*(P*q^7*e*B) := by
    have H := (div_le_iff₀ (show 0<16*K by positivity)).mp
      (show b*r/(16*K) ≤ P*q^7*e*B by simpa only [div_mul_eq_mul_div] using hgain)
    simpa only [mul_comm (16*K)] using H
  have H := mul_le_mul_of_nonneg_left hg hq.le
  have hl := mul_le_mul hscale (le_refl r) hr (mul_nonneg hq.le hb.le)
  have HH : a*r ≤ a*(16*K*q^8*B*w^2) := by
    calc
      _ ≤ q*(b*r) := by nlinarith
      _ ≤ q*(16*K*(P*q^7*e*B)) := H
      _ = (P*e)*(16*K*q^8*B) := by ring
      _ = _ := by rw [←hunit]; ring
  exact (mul_le_mul_iff_right₀ ha).mp HH

lemma screening_polynomial_bound {I K M G t L J : ℝ}
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (_ht : 0 ≤ t) (hL : 0 ≤ L) (hJ : 1 ≤ J) (htJ : t ≤ J) (hLM : L ≤ J*M) :
    1+t*I+4*K+3*L*G+L^3 ≤ (1+I+4*K+3*M+M^3)*J^3*(1+G) := by
  have hj0 : 0 ≤ J := by linarith
  have hj3 : 1 ≤ J^3 := one_le_pow₀ hJ
  have hj : J ≤ J^3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (show 1 ≤ 3 by omega)
  have htI : t*I ≤ J^3*I := mul_le_mul_of_nonneg_right (htJ.trans hj) hI
  have h4 : 4*K ≤ J^3*(4*K) := le_mul_of_one_le_left (by positivity) hj3
  have hLG : 3*L*G ≤ J^3*(3*M*G) := by
    have hL' := hLM.trans (mul_le_mul_of_nonneg_right hj hM)
    nlinarith [mul_le_mul_of_nonneg_right hL' hG]
  have hLc : L^3 ≤ J^3*M^3 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL hLM 3
  have hp : 1+I+4*K+M^3 ≥ 0 := by positivity
  calc
    _ ≤ J^3*(1+I+4*K+3*M*G+M^3) := by nlinarith
    _ ≤ J^3*((1+I+4*K+3*M+M^3)*(1+G)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hj0 _)
      nlinarith [mul_nonneg hG hp]
    _ = _ := by ring

lemma screening_exponential_majorant {A : ℝ} (hA : 1 ≤ A) (j : ℕ) :
    A*((4:ℝ)^(j+1))^8*((j+1:ℕ):ℝ)^3 ≤ (A*524288)^(j+1) := by
  have hj : ((j+1:ℕ):ℝ) ≤ 2^(j+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=j+1)).le
  have hj3 : ((j+1:ℕ):ℝ)^3 ≤ (8:ℝ)^(j+1) := by
    calc
      _ ≤ (2^(j+1):ℝ)^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hj _
      _ = _ := by rw [←pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have ha : A ≤ A^(j+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ j+1 by omega)
  have hae : 0 ≤ A := by linarith
  calc
    _ ≤ A*((4:ℝ)^(j+1))^8*(8:ℝ)^(j+1) :=
      mul_le_mul_of_nonneg_left hj3 (mul_nonneg hae (by positivity))
    _ = A*(524288:ℝ)^(j+1) := by
      rw [←pow_mul (4:ℝ), Nat.mul_comm (j+1) 8, pow_mul]
      rw [mul_assoc,←mul_pow]
      norm_num
    _ ≤ A^(j+1)*(524288:ℝ)^(j+1) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := (mul_pow _ _ _).symm

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def screenFieldUnit (δ P a : ℝ) : ℝ := Real.sqrt P*screenMass δ a/a
lemma screenFieldUnit_pos {δ P a : ℝ} (hP : 1 ≤ P) (ha : 0<a) : 0<screenFieldUnit δ P a :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (by linarith)) (screenMass_pos δ a)) ha
lemma screenFieldUnit_square {δ P a : ℝ} (hP : 0 ≤ P) (ha : 0<a) :
    a*(screenFieldUnit δ P a)^2=P*screenEnergy δ a := by
  unfold screenFieldUnit screenEnergy
  rw [div_pow,mul_pow,Real.sq_sqrt hP]
  field_simp
lemma screenFieldUnit_product {δ P a : ℝ} (hP : 0 ≤ P) :
    Real.sqrt P*screenMass δ a*screenFieldUnit δ P a=P*screenEnergy δ a := by
  unfold screenFieldUnit screenEnergy
  have hs := Real.sq_sqrt hP
  calc
    _ = (Real.sqrt P)^2*(screenMass δ a)^2/a := by ring
    _ = _ := by rw [hs]; ring

def atomicIMSConstant : ℝ := 24*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*(radialCutCoefficient/40)^2
lemma atomicIMSConstant_nonneg : 0 ≤ atomicIMSConstant := by unfold atomicIMSConstant; positivity

lemma atomicIMS_le_units {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0 ≤ δ) (hP : 1 ≤ P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    atomicIMS ψ y ≤ atomicIMSConstant*P*screenEnergy δ (atomicCellScale y) := by
  have ha := atomicCellScale_pos hy
  have HB := atomicPatch_population ψ hm hδ (by linarith) hc hy
  change 3*(radialCutCoefficient/(40*atomicCellScale y))^2*expectedPopulation ψ _ ≤ _
  calc
    _ ≤ 3*(radialCutCoefficient/(40*atomicCellScale y))^2*
        ((Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y)) :=
      mul_le_mul_of_nonneg_left HB (by positivity)
    _ = atomicIMSConstant*(Real.sqrt P*screenMass δ (atomicCellScale y)/(atomicCellScale y)^2) := by
      unfold atomicIMSConstant
      field_simp
      ring
    _ ≤ atomicIMSConstant*(P*(screenMass δ (atomicCellScale y))^2/atomicCellScale y) :=
      mul_le_mul_of_nonneg_left (screening_ims_units hP ha (screenMass_pos _ _).le (screenMass_scale δ ha)) atomicIMSConstant_nonneg
    _ = _ := by unfold screenEnergy; ring

lemma sqrt_count_raw_product {X P m w G : ℝ} (hP : 0 ≤ P) (hm : 0 ≤ m)
    (hw : 0 ≤ w) (hG : 0 ≤ G) (hX : X ≤ P*m^2) :
    Real.sqrt (X*(8*(w*G)^2)) ≤ 3*Real.sqrt P*m*w*G := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ P*m^2*(8*(w*G)^2) := mul_le_mul_of_nonneg_right hX (by positivity)
    _ ≤ (3*Real.sqrt P*m*w*G)^2 := by
      simp only [mul_pow,Real.sq_sqrt hP]
      nlinarith [mul_nonneg (mul_nonneg hP (sq_nonneg m)) (sq_nonneg (w*G))]

lemma atomic_cell_cost_units {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {δ P a q G : ℝ} (hδ : 0 ≤ δ) (hP : 1 ≤ P) (ha : 0<a) (hq : 1 ≤ q) (hG : 0 ≤ G)
    (z : C → Space) (hz : ∀ c, AtomicScaleWindow a q (z c))
    (hc : ∀ v : Space, v≠0 → localCountSecondMoment ψ (Metric.closedBall v (atomicCellScale v)) ≤
      P*(screenMass δ (atomicCellScale v))^2) :
    (∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*
        (8*(screenFieldUnit δ P a*G)^2))+
        ((Fintype.card C:ℝ)*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
          (3*atomicCellScale (z c)))) ≤
      P*q^7*screenEnergy δ a*(3*(Fintype.card C:ℝ)*G+(Fintype.card C:ℝ)^3) := by
  have hp0 : 0 ≤ P := by linarith
  have hq0 : 0<q := by linarith
  have he : 0<screenEnergy δ a := screenEnergy_pos δ ha
  have hw : 0<screenFieldUnit δ P a := screenFieldUnit_pos hP ha
  have hm0 : 0<screenMass δ a := screenMass_pos δ a
  have hq37 : q^3 ≤ q^7 := pow_le_pow_right₀ hq (by omega)
  let L : ℝ := Fintype.card C
  let M : ℝ := screenMass δ a
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hM : 0<M := hm0
  have hmom (c) : localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c))) ≤ P*q^6*M^2 := by
    have H := (hz c).mass ha hq hδ
    have HH := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos _ _).le H 2) hp0
    calc
      _ ≤ P*(screenMass δ (atomicCellScale (z c)))^2 := hc _ ((hz c).nonzero ha)
      _ ≤ P*(q^3*M)^2 := HH
      _ = _ := by ring
  have hsum : (∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))) ≤ L*(P*q^6*M^2) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,L] using Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => hmom c)
  have hsqrt (c) : Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*
      (8*(screenFieldUnit δ P a*G)^2)) ≤ 3*P*q^7*screenEnergy δ a*G := by
    have H := sqrt_count_raw_product hp0 (screenMass_pos δ (atomicCellScale (z c))).le hw.le hG
      (hc _ ((hz c).nonzero ha))
    calc
      _ ≤ 3*Real.sqrt P*screenMass δ (atomicCellScale (z c))*screenFieldUnit δ P a*G := H
      _ ≤ 3*Real.sqrt P*(q^3*M)*screenFieldUnit δ P a*G := by
        gcongr
        exact (hz c).mass ha hq hδ
      _ = 3*q^3*(P*screenEnergy δ a)*G := by
        have hu := screenFieldUnit_product (δ:=δ) (a:=a) hp0
        dsimp [M]
        calc
          _ = 3*q^3*(Real.sqrt P*screenMass δ a*screenFieldUnit δ P a)*G := by ring
          _ = _ := by rw [hu]
      _ ≤ _ := by
        have HH := mul_le_mul_of_nonneg_right hq37 (show 0 ≤ 3*P*screenEnergy δ a*G by positivity)
        nlinarith
  have hother (c) : (L*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
      (3*atomicCellScale (z c)) ≤ L^2*P*q^7*screenEnergy δ a := by
    calc
      _ ≤ (L*(L*(P*q^6*M^2)))/(a/q) := by
        apply div_le_div₀
        · positivity
        · exact mul_le_mul_of_nonneg_left hsum hL
        · exact div_pos ha hq0
        · have H := (hz c).div_lower hq0
          linarith [atomicCellScale_nonneg (z c)]
      _ = _ := by unfold screenEnergy; dsimp [M]; field_simp
  calc
    _ ≤ ∑ _c : C, (3*P*q^7*screenEnergy δ a*G+L^2*P*q^7*screenEnergy δ a) :=
      Finset.sum_le_sum (fun c _ => add_le_add (hsqrt c) (hother c))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [L]; ring

end Coulomb

end

end OAI
