import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import OAI.NumberTheory.DirichletL.Detector.CentralExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyadic_weighted_rows_card (α r C U B : ℝ) (hC : 0≤C) (hU : 0<U)
    (R : Finset FreeRow) (hcard : (R.card:ℝ)≤B)
    (hR : ∀u∈R,U≤rowNorm u ∧ rowNorm u≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*rowNorm u^α)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      B*C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (α-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<rowNorm u := hU.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      change rowNorm u^(-r)*F u≤_
      calc
        _ ≤ rowNorm u^(-r)*(C*rowNorm u^α) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*rowNorm u^(α-r) := by
          rw [show α-r=(-r)+α by ring,Real.rpow_add hN]; ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U (rowNorm u) (α-r)
            (by norm_num) (by norm_num) hU (by simpa using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) := by simp
    _ ≤ B*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma annular_power_uniform (p pmax : ℝ) (hp : p≤pmax) :
    ProbeSelectedPrimeSums.annularPower 1 2 p≤max 1 ((2:ℝ)^pmax) := by
  unfold ProbeSelectedPrimeSums.annularPower
  rw [Real.one_rpow]
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)

def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

lemma mixed_physical_exponent (Z a v d R q e eps loss mesh : ℝ) (N : ℕ)
    (hZ : 0<Z) :
    ((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*Z^(-2/75+q/6+mesh/6+loss))=
    Z^(mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤ProbeCentralExponent.sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0<Z) (hmargin : 2≤Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end SevenEighths.ProbeHighRowFamily

end

end OAI
