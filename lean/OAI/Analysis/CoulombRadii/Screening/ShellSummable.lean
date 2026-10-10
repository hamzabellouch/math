import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UniformCountConsequences
import OAI.Analysis.CoulombRadii.Localization.ShellIMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma screenMass_dilate {δ t q : ℝ} (hδ : 0≤δ) (ht : 0<t) (hq : 1≤q) :
    screenMass δ (q*t) ≤ q*screenMass δ t := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hbt : screenBaseMass (q*t) ≤ screenBaseMass t := by
    simpa only [div_one,one_pow,one_mul] using
      (screenBaseMass_comparable ht (q:=1) (b:=q*t) le_rfl (by nlinarith))
  have hsq : Real.sqrt (δ*(q*t)) ≤ q*Real.sqrt (δ*t) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hq0.le (Real.sqrt_nonneg _),?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hδ ht.le)]
    have hqq : q ≤ q^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hqq) (mul_nonneg hδ ht.le)]
  have hb0 : 0≤ screenBaseMass t := zero_le_one.trans (screenBaseMass_ge_one t)
  dsimp only [screenMass]
  nlinarith

theorem exists_atomic_imsShell_population_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → expectedPopulation ψ (imsShell 0 u) ≤ C*screenMass δ u := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=1/2) (β:=3) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu
  have hb := H S hatom ψ hψ hm hE hstate hδ hu
  have hA : MeasurableSet {x : Space | (1/2:ℝ)*u<‖x‖ ∧ ‖x‖<3*u} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hsub : imsShell 0 u ⊆ {x : Space | (1/2:ℝ)*u<‖x‖ ∧ ‖x‖<3*u} := by
    intro x hx
    simp only [imsShell,mem_ofPred_eq,sub_zero] at hx ⊢
    constructor <;> linarith [hx.1,hx.2]
  have hp := expectedPopulation_sq_le ψ (measurableSet_imsShell 0 u) hm
  have hmom := localCountSecondMoment_mono ψ hA hsub
  have hw : 0≤ screenMass δ u := by
    dsimp only [screenMass]
    linarith [screenBaseMass_ge_one u, Real.sqrt_nonneg (δ*u)]
  have hs := Real.sq_sqrt hC
  have hprod := mul_nonneg (Real.sqrt_nonneg C) hw
  nlinarith [sq_nonneg (Real.sqrt C*screenMass δ u-expectedPopulation ψ (imsShell 0 u))]

lemma dyadic_inverse_square_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((1/4:ℝ)^j)) ≤ 4/3 := by
  have he : (∑ j ∈ Finset.range k, ((1/4:ℝ)^j)) = 4/3*(1-(1/4:ℝ)^k) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [he]
  have hp := pow_nonneg (by norm_num : (0:ℝ)≤1/4) k
  linarith

lemma dyadic_inverse_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((1/2:ℝ)^j)) ≤ 2 := by
  have he : (∑ j ∈ Finset.range k, ((1/2:ℝ)^j)) = 2*(1-(1/2:ℝ)^k) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [he]
  have hp := pow_nonneg (by norm_num : (0:ℝ)≤1/2) k
  linarith

theorem exists_atomic_dyadic_IMS_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {t : ℝ}, 0<t → ∀ k : ℕ,
      (∑ j ∈ Finset.range k, 3*(radialCutCoefficient/((2:ℝ)^j*t))^2*
        expectedPopulation ψ (imsShell 0 ((2:ℝ)^j*t))) ≤ C*screenMass δ t/t^2 := by
  obtain ⟨C,hC,H⟩ := exists_atomic_imsShell_population_bound
  refine ⟨6*radialCutCoefficient^2*C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ t ht k
  have ht0 : t≠0 := ne_of_gt ht
  have hmass : 0≤ screenMass δ t := by
    dsimp only [screenMass]
    linarith [screenBaseMass_ge_one t,Real.sqrt_nonneg (δ*t)]
  have hterm (j : ℕ) :
      3*(radialCutCoefficient/((2:ℝ)^j*t))^2 * expectedPopulation ψ (imsShell 0 ((2:ℝ)^j*t)) ≤
        (3*radialCutCoefficient^2*C*screenMass δ t/t^2)*(1/2:ℝ)^j := by
    have hq : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hqp : 0<(2:ℝ)^j := pow_pos (by norm_num) _
    have hb := H S hatom ψ hψ hm hE hstate hδ (mul_pos hqp ht)
    have hd := mul_le_mul_of_nonneg_left (screenMass_dilate hδ ht hq) hC
    calc
      _ ≤ 3*(radialCutCoefficient/((2:ℝ)^j*t))^2 * (C*((2:ℝ)^j*screenMass δ t)) :=
        mul_le_mul_of_nonneg_left (hb.trans hd) (by positivity)
      _ = _ := by
        simp only [div_pow,one_pow]
        field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range k, (3*radialCutCoefficient^2*C*screenMass δ t/t^2)*(1/2:ℝ)^j :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = (3*radialCutCoefficient^2*C*screenMass δ t/t^2)*∑ j ∈ Finset.range k, (1/2:ℝ)^j := by
      rw [Finset.mul_sum]
    _ ≤ (3*radialCutCoefficient^2*C*screenMass δ t/t^2)*2 :=
      mul_le_mul_of_nonneg_left (dyadic_inverse_sum k) (by positivity)
    _ = _ := by ring

end Coulomb
end

end

end OAI
