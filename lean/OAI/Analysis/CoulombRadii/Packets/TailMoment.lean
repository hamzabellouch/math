import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RestrictedField
import OAI.Analysis.CoulombRadii.Localization.RadialCut
import OAI.Analysis.CoulombRadii.Screening.ScreenUnits

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma screenBaseMass_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    screenBaseMass b ≤ screenBaseMass a := by
  have hb : 0 < b := ha.trans_le hab
  unfold screenBaseMass
  exact max_le_max ((inv_le_inv₀ (by positivity) (by positivity)).mpr (pow_le_pow_left₀ ha.le hab 3)) le_rfl

lemma screenMass_dyadic_bound {δ h : ℝ} (hδ : 0 ≤ δ) (hh : 0 < h) (j : ℕ) :
    screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) ≤ screenMass δ h/h*(3/4:ℝ)^j := by
  have h2 : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have h3 : (1:ℝ) ≤ (3/2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hb := screenBaseMass_antitone hh (show h ≤ (2:ℝ)^j*h by nlinarith)
  have hb' : screenBaseMass ((2:ℝ)^j*h) ≤ (3/2:ℝ)^j*screenBaseMass h :=
    hb.trans (le_mul_of_one_le_left (screenBaseMass_nonneg h) h3)
  have hp : (2:ℝ)^j ≤ ((3/2:ℝ)^j)^2 := by
    have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ (3/2:ℝ)^2) j
    simpa only [←pow_mul,Nat.mul_comm] using H
  have hr : Real.sqrt (δ*((2:ℝ)^j*h)) ≤ (3/2:ℝ)^j*Real.sqrt (δ*h) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hδ hh.le)]
    nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hδ hh.le)]
  have hm : screenMass δ ((2:ℝ)^j*h) ≤ (3/2:ℝ)^j*screenMass δ h := by
    unfold screenMass
    nlinarith
  refine (div_le_div_of_nonneg_right hm (by positivity)).trans_eq ?_
  have he : (3/2:ℝ)^j=(3/4:ℝ)^j*(2:ℝ)^j := by rw [←mul_pow]; congr 1; norm_num
  rw [he]
  field_simp

def radialTailKernel (r : ℝ) (x : Space) : ℝ := if r ≤ ‖x‖ then ‖x‖⁻¹ else 0

def radialTailPotential {n : ℕ} (ψ : H1Vector n) (r : ℝ) : ℝ :=
  restrictedCorePotential ψ {x | r ≤ ‖x‖} 0

lemma radialTailPotential_eq {n : ℕ} (ψ : H1Vector n) (r : ℝ) :
    radialTailPotential ψ r=∑ s, ∑ i : Fin n, ∫ x, radialTailKernel r (position x i)*‖ψ.value s x‖^2 := by
  unfold radialTailPotential restrictedCorePotential radialTailKernel coulombKernel
  simp only [sub_zero,Set.mem_ofPred_eq,ite_mul,zero_mul]

lemma radialTailKernel_nonneg (r : ℝ) (x : Space) : 0 ≤ radialTailKernel r x := by
  unfold radialTailKernel
  split_ifs <;> positivity

lemma radialTailKernel_le {r : ℝ} (hr : 0 < r) (x : Space) : radialTailKernel r x ≤ r⁻¹ := by
  unfold radialTailKernel
  split_ifs with hx
  · exact (inv_le_inv₀ (hr.trans_le hx) hr).mpr hx
  · positivity

lemma radialTailKernel_integrable {n : ℕ} (ψ : H1Vector n) (r : ℝ) (s : Spins n) (i : Fin n) :
    Integrable (fun x => radialTailKernel r (position x i)*‖ψ.value s x‖^2) := by
  simpa only [radialTailKernel,coulombKernel,sub_zero,Set.mem_ofPred_eq,ite_mul,zero_mul] using
    restrictedCore_integrable ψ (isClosed_le continuous_const continuous_norm).measurableSet s i 0

lemma radialTailPotential_cap {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0 < r) :
    radialTailPotential ψ r ≤ (n:ℝ)/r*mass ψ := by
  rw [radialTailPotential_eq]
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x, r⁻¹*‖ψ.value s x‖^2 := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      exact integral_mono (radialTailKernel_integrable ψ r s i)
        (((ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
        (fun x => mul_le_mul_of_nonneg_right (radialTailKernel_le hr _) (sq_nonneg _))
    _ = _ := by simp only [integral_const_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mass,div_eq_mul_inv,←Finset.mul_sum,mul_assoc]

lemma radialTailKernel_step {r : ℝ} (hr : 0 < r) (x : Space) :
    radialTailKernel r x ≤ r⁻¹*({z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}.indicator (fun _ => (1:ℝ)) x)+
      radialTailKernel (2*r) x := by
  by_cases h0 : r ≤ ‖x‖
  · by_cases h1 : 2*r ≤ ‖x‖
    · simp only [radialTailKernel,ite_eq_left h0,ite_eq_left h1]
      have H : 0 ≤ ({z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}.indicator (fun _ => (1:ℝ)) x) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) H]
    · have hA : x∈{z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} := by constructor <;> linarith
      simp only [indicator_of_mem hA,mul_one,radialTailKernel,ite_eq_left h0,ite_eq_right h1,add_zero]
      exact (inv_le_inv₀ (hr.trans_le h0) hr).mpr h0
  · rw [radialTailKernel,ite_eq_right h0]
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (radialTailKernel_nonneg _ _)

lemma radialTailPotential_step {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0 < r) :
    radialTailPotential ψ r ≤ expectedPopulation ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}/r+
      radialTailPotential ψ (2*r) := by
  let A : Set Space := {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [radialTailPotential_eq,radialTailPotential_eq]
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x, (r⁻¹*A.indicator (fun _ => (1:ℝ)) (position x i)+radialTailKernel (2*r) (position x i))*‖ψ.value s x‖^2 := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      apply integral_mono (radialTailKernel_integrable ψ r s i) _
        (fun x => mul_le_mul_of_nonneg_right (radialTailKernel_step hr _) (sq_nonneg _))
      convert ((population_integrable ψ A hA s i).const_mul r⁻¹).add
        (radialTailKernel_integrable ψ (2*r) s i) using 1
      first | rfl | (ext x; simp only [Pi.add_apply]; ring)
    _ = _ := by
      simp_rw [add_mul,mul_assoc]
      simp_rw [integral_add ((population_integrable ψ A hA _ _).const_mul _) (radialTailKernel_integrable ψ (2*r) _ _),integral_const_mul]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,expectedPopulation,A,div_eq_mul_inv]
      ring

end Coulomb
end

end
end

end OAI
