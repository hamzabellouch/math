import Mathlib
import OAI.Analysis.CoulombRadii.Variational.WedgeInsert
import OAI.Analysis.CoulombRadii.Propagation.PropagationMassTest
import OAI.Analysis.CoulombRadii.Propagation.PosteriorPropagationData

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom
section Expectation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {B C r Z L : ℝ} {μ H : Ω → Position → ℝ}
lemma NuclearRandomDatum.ball_product_integrable (q : NuclearRandomDatum Z μ H) (R : ℝ) :
    Integrable (fun z : Ω×Position => (Metric.ball (0:Position) R).indicator (μ z.1) z.2) (P.prod volume) := by
  apply compact_random_field_integrable (P:=P) (R:=R) (f:=fun o x => (Metric.ball (0:Position) R).indicator (μ o) x)
  · exact q.mu_measurable.indicator (measurableSet_ball.preimage measurable_snd)
  · intro D
    obtain ⟨M,hM⟩ := q.mu_bounds D
    refine ⟨max M 0,?_⟩
    intro o x hx
    by_cases h : x∈Metric.ball (0:Position) R
    · simpa only [Set.indicator_of_mem h] using (hM o x hx).trans (le_max_left M 0)
    · simp only [Set.indicator_of_notMem h,abs_zero]; exact le_max_right M 0
  · exact Eventually.of_forall (fun o x hx => Set.indicator_of_notMem (by simpa using not_lt.mpr hx) _)

theorem PropagationDatum.expected_charge_deficit (d : PropagationDatum P B C r Z L μ)
    (q : NuclearRandomDatum Z μ H) (hr : 0<r) (hB : 0≤B) (hC : 0≤C) :
    (∫ o,(∫ x in Metric.ball 0 r,μ o x) ∂P)≤
      Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+
        (∫ o,(∫ x,d.error o x) ∂P) := by
  have hpi := d.error_product_integrable
  have hmi := q.ball_product_integrable (P:=P) r
  have hip : Integrable (fun o => ∫ x,d.error o x) P := hpi.integral_prod_left
  have him : Integrable (fun o => ∫ x in Metric.ball 0 r,μ o x) P := by
    simpa only [integral_indicator measurableSet_ball] using hmi.integral_prod_left
  have H : ∀ᵐ o ∂P,(∫ x in Metric.ball 0 r,μ o x)≤
      Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+(∫ x,d.error o x) := by
    filter_upwards [d.invariant,hpi.prod_right_ae] with o hi hp
    have HD := hi.charge_deficit hr hB hC (q.integrable_mu o) hp
    linarith only [HD]
  have HH := integral_mono_ae him ((integrable_const _).add hip) H
  change (∫ o,(∫ x in Metric.ball 0 r,μ o x) ∂P)≤
    ∫ o,(Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+(∫ x,d.error o x)) ∂P at HH
  rw [integral_add (integrable_const _) hip,integral_const,probReal_univ,one_smul] at HH
  exact HH
end Expectation
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom
section Init
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Z r n ε : ℝ} {μ H : Ω → Position → ℝ} {bad : Ω → Prop}
lemma NuclearRandomDatum.initial_error_bound (q : NuclearRandomDatum Z μ H)
    (hb : MeasurableSet {o | bad o}) (hn : ∀ o,(∫ x,μ o x) ≤ n)
    (hr : 0<r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hnr : n*r^3 ≤ 3*ε^3)
    (hp : P.real {o | bad o} ≤ 343*r^35) :
    (∫ o,(∫ x,initialPropagationError (bad o) r (μ o) x) ∂P) ≤ 1029*ε^3*r^9 := by
  rw [initialPropagationError_total q.mu_measurable hb]
  have hi : Integrable (fun o => ∫ x in Metric.ball 0 r,μ o x) P := by
    simpa only [integral_indicator measurableSet_ball] using (q.ball_product_integrable (P:=P) r).integral_prod_left
  have hno : 0 ≤ n := by
    obtain ⟨o⟩ := nonempty_of_isProbabilityMeasure P
    exact (integral_nonneg (q.nonnegative_mu o)).trans (hn o)
  have H : (∫ o in {o | bad o},∫ x in Metric.ball 0 r,μ o x ∂volume ∂P) ≤ P.real {o | bad o}*n := by
    have HH := integral_mono (hi.integrableOn (s:={o | bad o})) (integrable_const n (μ:=P.restrict {o | bad o}))
      (fun o => (setIntegral_le_integral (q.integrable_mu o)
        (Eventually.of_forall (q.nonnegative_mu o))).trans (hn o))
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] using HH
  calc
    _ ≤ P.real {o | bad o}*n := H
    _ ≤ (343*r^35)*n := mul_le_mul_of_nonneg_right hp hno
    _ = 343*(n*r^3)*r^32 := by ring
    _ ≤ 343*(3*ε^3)*r^32 := by gcongr
    _ = 1029*ε^3*r^32 := by ring
    _ ≤ 1029*ε^3*r^9 := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr.le hr1 (by decide)) (by positivity)
end Init
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma atomic_nuclear_nonsingular_bound {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : H1Vector n) {R : ℝ} (hR : 0<R) :
    nuclearEnergy (atom Z hZ) u ≤ (Z:ℝ)*potentialForm (nearPotential 0 R) u+
      ((Z:ℝ)*(n:ℝ)/R)*mass u := by
  have point (x : Configuration n) :
      (∑ i,attraction (atom Z hZ) (position x i)) ≤
      (Z:ℝ)*nearPotential 0 R x+(Z:ℝ)*(n:ℝ)/R := by
    have H (i : Fin n) : attraction (atom Z hZ) (position x i) ≤
        (Z:ℝ)*nearWeight 0 R (position x i)+(Z:ℝ)/R := by
      have hat : attraction (atom Z hZ) (position x i)=(Z:ℝ)*coulombKernel (0-position x i) := by
        simp [attraction,atom,coulombKernel,norm_neg]
      rw [hat]
      by_cases hx : position x i∈Metric.ball 0 R
      · rw [nearWeight,Set.indicator_of_mem hx]
        exact le_add_of_nonneg_right (by positivity)
      · have hz : R≤‖position x i‖ := by
          simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx
        have H := one_div_le_one_div_of_le hR hz
        rw [nearWeight,Set.indicator_of_notMem hx,mul_zero,zero_add]
        simpa only [coulombKernel,zero_sub,norm_neg,one_div,div_eq_mul_inv,mul_one,one_mul] using
          mul_le_mul_of_nonneg_left H (Nat.cast_nonneg Z)
    have Hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i∈Finset.univ) => H i)
    simpa only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,nearPotential,div_eq_mul_inv,mul_assoc,mul_left_comm] using Hsum
  have hV (s : Spins n) : Integrable (fun x =>
      (∑ i,attraction (atom Z hZ) (position x i))*‖u.value s x‖^2) := by
    simpa only [attraction,atom,Fin.sum_univ_one,sub_zero,Finset.sum_mul,mul_assoc] using
      integrable_finsetSum Finset.univ (fun i _ =>
        ((u.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0:ℝ)<1)).1).const_mul (Z:ℝ))
  have hW (s : Spins n) : Integrable (fun x =>
      ((Z:ℝ)*nearPotential 0 R x)*‖u.value s x‖^2) := by
    simpa only [mul_assoc] using (nearPotential_integrable u 0 R s).const_mul (Z:ℝ)
  have H := potentialForm_le_add_const u hV hW (Eventually.of_forall point)
  change _ ≤ _ at H
  have he : potentialForm (fun x => (Z:ℝ)*nearPotential 0 R x) u =
      (Z:ℝ)*potentialForm (nearPotential 0 R) u := by
    simp only [potentialForm,mul_assoc,integral_const_mul,Finset.mul_sum]
  rw [he] at H
  exact H

lemma atomic_kinetic_le_near {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : H1Vector n) (hu : Antisymmetric u) (hm : mass u=1)
    {R D : ℝ} (hR : 0<R) (hform : form (atom Z hZ) u≤D) :
    kinetic u ≤ (Z:ℝ)*fermionicNearConstant*kinetic u^(3/5:ℝ)*R^(1/5:ℝ)+
      (Z:ℝ)*(n:ℝ)/R+D := by
  have Hn := atomic_nuclear_nonsingular_bound Z hZ u hR
  have Hl := nearPotential_normalized u hu hm.le (0:Space) hR.le
  have Hp := pairEnergy_nonneg u
  have Hl' := mul_le_mul_of_nonneg_left Hl (Nat.cast_nonneg Z)
  rw [hm,mul_one] at Hn
  dsimp only [form] at hform
  nlinarith only [hform,Hn,Hp,Hl']
end Coulomb
end

end

end OAI
