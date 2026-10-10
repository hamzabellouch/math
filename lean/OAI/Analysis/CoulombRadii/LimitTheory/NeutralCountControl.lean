import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.NeutralBaseline

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace NeutralAtom
lemma raw_second_expectation_asH1 {n:ℕ} {ψ:Wavefunction n} {g:Gradient n}
    (hd:FormDomain ψ g) {S:Set Position} (hS:MeasurableSet S) :
    rawExpectation ψ (fun x => (rawCount S x)^2)=
      Coulomb.localCountSecondMoment (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [rawExpectation_eq_stateWeightedIntegral hd.2.2.1 ((measurable_rawCount hS).pow_const 2)
    (C:=(n:ℝ)^2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2)]
  change stateWeightedIntegral ψ (fun x => (rawCount S x)^2)=
    Coulomb.potentialForm (fun x => (Coulomb.localCount S x)^2) _
  simpa only [Coulomb.potentialForm,Coulomb.localCount,position_flattenConfiguration,rawCount] using
    (asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1 (fun x => (Coulomb.localCount S x)^2)).symm

lemma physical_exterior_deficit {N:ℕ} {ψ:Wavefunction (N+1)} {g:Gradient (N+1)}
    (hd:FormDomain ψ g) (hn:normSquared ψ=1) (r:ℝ) :
    exteriorMass ψ r=(N+1:ℝ)-Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball 0 r) := by
  rw [←raw_population_asH1 hd measurableSet_ball,integral_rawLaw hd.2.2.1,
    rawExpectation_count_eq_density hd.1 hd.2.2.1 measurableSet_ball]
  have hb : ∫ x in Metric.closedBall (0:Position) r,density ψ x = ∫ x in Metric.ball (0:Position) r,density ψ x := by
    apply setIntegral_congr_set
    have hsphere : ∀ᵐ x : Position,x∉Metric.sphere (0:Position) r := by
      rw [ae_iff]
      convert Measure.addHaar_sphere volume (0:Position) r using 1
      congr 1
      ext x
      simp
    filter_upwards [hsphere] with x hx
    simp only [Metric.mem_sphere,dist_zero_right] at hx
    apply propext
    constructor
    · intro h
      exact Metric.mem_ball.mpr (lt_of_le_of_ne (Metric.mem_closedBall.mp h) (by simpa using hx))
    · intro h
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp h).le
  have H:=integral_add_compl measurableSet_closedBall (integrable_density hd.2.2.1)
    (s:=Metric.closedBall (0:Position) r)
  rw [integral_density hd.2.2.1,hn,mul_one,hb] at H
  have he : (Metric.closedBall (0:Position) r)ᶜ={x:Position | r<‖x‖} := by ext x; simp
  rw [he] at H
  exact eq_sub_of_add_eq' H

 theorem physical_uniform_count_control : UniformGroundStateCountControl := by
  obtain ⟨D,hD,Zmin,H⟩:=physical_neutral_energy_offset
  refine ⟨D,Zmin,hD,?_,?_⟩
  · intro α β hα hαβ
    obtain ⟨C,hC,HC⟩:=Coulomb.atomic_annular_second_moment hα hαβ
    refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
    intro N ψ hNZ hψ u hu
    obtain ⟨g,hd,hn,hmin⟩:=hψ
    let v:=asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have hm:Coulomb.mass v=1 := (asH1_mass ..).trans hn
    have hz:1≤N+1:=by omega
    have he:Coulomb.form (Coulomb.atom (N+1) hz) v≤
        (Coulomb.unrestrictedFormBottom (Coulomb.atom (N+1) hz)).toReal+D := by
      rw [asH1_energy]; exact H (N+1) hNZ hz hd hn hmin
    have hE:=Coulomb.atom_unrestricted_bottom_real (N+1) hz v (asH1_antisymmetric hd) hm
    have HH:=HC (Coulomb.atom (N+1) hz) (fun _ => rfl) v (asH1_antisymmetric hd) hm hE.le he hD hu
    rw [raw_second_expectation_asH1 hd (S:={y:Position | α*u<‖y‖ ∧ ‖y‖<β*u}) (measurableSet_lt measurable_const continuous_norm.measurable |>.inter
      (measurableSet_lt continuous_norm.measurable measurable_const))]
    apply (Real.sqrt_le_sqrt HH).trans_eq
    rw [Real.sqrt_mul hC,Real.sqrt_sq (Coulomb.screenMass_pos D u).le]
    rfl
  · refine ⟨2*Coulomb.atomicInnerFieldConstant,mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg,?_⟩
    intro N ψ hNZ hψ
    obtain ⟨g,hd,hn,hmin⟩:=hψ
    let v:=asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have hm:Coulomb.mass v=1 := (asH1_mass ..).trans hn
    have hz:1≤N+1:=by omega
    have he:Coulomb.form (Coulomb.atom (N+1) hz) v≤
        (Coulomb.unrestrictedFormBottom (Coulomb.atom (N+1) hz)).toReal+D := by
      rw [asH1_energy]; exact H (N+1) hNZ hz hd hn hmin
    have hE:=Coulomb.atom_unrestricted_bottom_real (N+1) hz v (asH1_antisymmetric hd) hm
    have HH:=Coulomb.atomic_inner_deficit_upper (Coulomb.atom (N+1) hz) (fun _ => rfl)
      v (asH1_antisymmetric hd) hm hE.le he hD (by norm_num : (0:ℝ)<1)
    rw [physical_exterior_deficit hd hn]
    simpa [Coulomb.totalCharge,Coulomb.atom,Coulomb.screenMass,Coulomb.screenBaseMass] using HH
end NeutralAtom
end

end
section
noncomputable section
open Filter
open scoped Topology
namespace NeutralAtom

theorem slow_stages {P : ℕ → ℕ → Prop}
    (hP : ∀ q : ℕ, ∀ᶠ n : ℕ in atTop, P q n) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ᶠ n in atTop, P (q n) n := by
  classical
  let q : ℕ → ℕ := fun n => Nat.findGreatest (fun k => P k n) n
  refine ⟨q, tendsto_atTop.mpr ?_, ?_⟩
  · intro Q
    filter_upwards [eventually_ge_atTop Q, hP Q] with n hn hpn
    exact Nat.le_findGreatest hn hpn
  · filter_upwards [hP 0] with n hn
    exact Nat.findGreatest_spec (P := fun k => P k n) (Nat.zero_le n) hn

theorem staged_error_tendsto_zero {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun n => ((q n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hq)

end NeutralAtom
end

end
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma dyadic_radius_choice {r₀ s q : ℝ} (hr : 0 < r₀) (hs : 0 < s) (hq : 0 < q)
    (hsmall : r₀/s ≤ q⁻¹) :
    ∃ j : ℕ, s/(2*q) ≤ r₀*2^j ∧ r₀*2^j ≤ s/q := by
  have hrq : r₀*q ≤ s := by
    have H := (div_le_iff₀ hs).mp hsmall
    have H' := mul_le_mul_of_nonneg_right H hq.le
    calc
      r₀*q ≤ q⁻¹*s*q := H'
      _ = s := by field_simp
  have hx : 1 ≤ s/(q*r₀) := (one_le_div (mul_pos hq hr)).mpr (by simpa [mul_comm] using hrq)
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  refine ⟨j,?_,?_⟩
  · have H' := (div_lt_iff₀ (mul_pos hq hr)).mp hj'
    rw [pow_succ] at H'
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*q)).mpr
    nlinarith only [H',pow_pos (by norm_num : (0:ℝ)<2) j]
  · have H := (le_div_iff₀ (mul_pos hq hr)).mp hj
    apply (le_div_iff₀ hq).mpr
    nlinarith only [H]
end NeutralAtom
end

end

end OAI
