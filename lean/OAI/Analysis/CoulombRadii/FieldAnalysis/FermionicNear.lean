import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.PhysicalEnsemble
import OAI.Analysis.CoulombRadii.Packets.NearLpCoulomb
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshPotentialTower
import OAI.Analysis.CoulombRadii.Variational.PhysicalDensityWeighted
import OAI.Analysis.CoulombRadii.Screening.PhysicalLTBridge

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

def nearWeight (y : Space) (R : ℝ) : Space → ℝ :=
  (Metric.ball y R).indicator (fun z => coulombKernel (y-z))
def nearPotential {n : ℕ} (y : Space) (R : ℝ) (x : Configuration n) : ℝ :=
  ∑ i,nearWeight y R (position x i)
lemma nearWeight_nonneg (y : Space) (R : ℝ) (z : Space) : 0≤nearWeight y R z := by
  unfold nearWeight
  exact Set.indicator_nonneg (fun z _ => coulombKernel_nonneg _) z
lemma nearWeight_measurable (y : Space) (R : ℝ) : Measurable (nearWeight y R) :=
  (coulombKernel_measurable.comp (measurable_const.sub measurable_id)).indicator measurableSet_ball
lemma nearWeight_le (y : Space) (R : ℝ) (z : Space) : nearWeight y R z≤coulombKernel (y-z) := by
  unfold nearWeight
  exact Set.indicator_le_self' (fun z _ => coulombKernel_nonneg _) z
lemma nearPotential_nonneg {n : ℕ} (y : Space) (R : ℝ) (x : Configuration n) : 0≤nearPotential y R x :=
  Finset.sum_nonneg (fun index _ => nearWeight_nonneg y R (position x index))
lemma nearPotential_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ) (s : Spins n) :
    Integrable (fun x => nearPotential y R x*‖u.value s x‖^2) := by
  have hi (i : Fin n) : Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
    have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
    have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
      simpa only [coulombKernel,norm_sub_rev] using H
    have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
      (continuous_position i).measurable)
    apply hh.congr
    filter_upwards [] with x
    by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]
  simpa only [nearPotential,Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi i)

lemma nearPotential_physical {N : ℕ} (u : H1Vector (N+1)) (hu : Antisymmetric u)
    (y : Space) (R : ℝ) : potentialForm (nearPotential y R) u=
      ∫ z in Metric.ball y R,NeutralAtom.density (NeutralAtom.fromH1Wave u) z*coulombKernel (y-z) := by
  have hd := NeutralAtom.fromH1_domain u hu
  have hi (s : NeutralAtom.Spins (N+1)) (i : Fin (N+1)) :
      Integrable (fun x : NeutralAtom.Configuration (N+1) => nearWeight y R (x i)*‖NeutralAtom.fromH1Wave u s x‖^2) := by
    have H := (NeutralAtom.fromH1_coulomb_weight_integrable u y s i).indicator
      ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage (measurable_pi_apply i))
    apply H.congr
    filter_upwards [] with x
    by_cases hx : x i∈Metric.ball y R <;> simp [nearWeight,hx,NeutralAtom.coulombKernel,coulombKernel]
  have he : potentialForm (nearPotential y R) u=
      NeutralAtom.rawExpectation (NeutralAtom.fromH1Wave u) (fun x => ∑ i,nearWeight y R (x i)) := by
    unfold NeutralAtom.rawExpectation NeutralAtom.configurationDensity potentialForm
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun s _ => by
      simpa only [Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi s i))]
    apply Finset.sum_congr rfl
    intro s _
    exact ((NeutralAtom.flattenConfiguration_measurePreserving (N+1)).integral_comp'
      (fun x => nearPotential y R x*‖u.value s x‖^2)).symm
  rw [he,NeutralAtom.rawExpectation_oneBody_eq_density hd.1 _ hi,←integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z∈Metric.ball y R <;> simp [nearWeight,hz,mul_comm]

def fermionicNearConstant : ℝ := (32768/(3*Real.pi^2))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)
lemma fermionicNearConstant_nonneg : 0≤fermionicNearConstant := by unfold fermionicNearConstant; positivity

lemma nearPotential_normalized {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u)
    (hm : mass u≤1) (y : Space) {R : ℝ} (hR : 0≤R) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*kinetic u^(3/5:ℝ)*R^(1/5:ℝ) := by
  cases n with
  | zero =>
    simp only [potentialForm,nearPotential,Finset.univ_eq_empty,Finset.sum_empty,zero_mul,integral_zero,Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg (kinetic_nonneg u) _)) (Real.rpow_nonneg hR _)
  | succ N =>
    let ρ := NeutralAtom.density (NeutralAtom.fromH1Wave u)
    have hρ0 (z) : 0≤ρ z := by
      unfold ρ NeutralAtom.density
      positivity
    obtain ⟨hp,hb⟩ := NeutralAtom.physical_density_power_bound u hu hm
    have hint : Integrable ρ := (oneBodyDensity_integrable u).congr
      (NeutralAtom.density_fromH1_eq_oneBodyDensity u).symm
    have hLp : MemLp ρ (ENNReal.ofReal (5/3:ℝ)) volume := by
      apply (integrable_norm_rpow_iff hint.aestronglyMeasurable (by norm_num) (by simp)).mp
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/3),Real.norm_of_nonneg (hρ0 _)] using hp
    have hlocal := near_coulomb_holder y hR (hLp.restrict _) (Eventually.of_forall hρ0)
    have hmass : (∫ z in Metric.ball y R,ρ z^(5/3:ℝ))≤∫ z,ρ z^(5/3:ℝ) :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun z => Real.rpow_nonneg (hρ0 z) _)) hp
    rw [nearPotential_physical u hu y R]
    calc
      _≤_ := hlocal
      _≤((32768/(3*Real.pi^2))*kinetic u)^(3/5:ℝ)*((8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (hρ0 z) _))
          (hmass.trans hb) (by norm_num)
      _=_ := by
        rw [Real.mul_rpow (by positivity : (0:ℝ)≤32768/(3*Real.pi^2)) (kinetic_nonneg u)]
        unfold fermionicNearConstant
        ring

lemma rpow_three_fifths_linear {x B : ℝ} (hx : 0≤x) (hB : 0<B) :
    x^(3/5:ℝ)≤B^(-2/5:ℝ)*x+B^(3/5:ℝ) := by
  rcases le_total x B with h|h
  · exact (Real.rpow_le_rpow hx h (by norm_num)).trans (le_add_of_nonneg_left (by positivity))
  · have hx' : 0<x := hB.trans_le h
    have he : x^(3/5:ℝ)=x^(-2/5:ℝ)*x := by
      calc
        _=x^((-2/5)+1:ℝ) := by norm_num
        _=x^(-2/5:ℝ)*x^(1:ℝ) := Real.rpow_add hx' _ _
        _=_ := by rw [Real.rpow_one]
    rw [he]
    have hp : x^(-2/5:ℝ)≤B^(-2/5:ℝ) := Real.rpow_le_rpow_of_nonpos hB h (by norm_num)
    exact (mul_le_mul_of_nonneg_right hp hx).trans (le_add_of_nonneg_right (by positivity))

theorem nearPotential_linear {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u)
    (y : Space) {R B : ℝ} (hR : 0≤R) (hB : 0<B) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*kinetic u+B^(3/5:ℝ)*mass u) := by
  by_cases hz : mass u=0
  · rw [potentialForm_eq_zero_of_mass_zero _ u hz,kinetic_eq_zero_of_mass_zero u hz,hz]
    simp
  have hm : 0 < mass u := lt_of_le_of_ne (mass_nonneg u) (Ne.symm hz)
  have hn := nearPotential_normalized u.normalized hu.normalized (mass_normalized u hm).le y hR
  have hr := rpow_three_fifths_linear (kinetic_nonneg u.normalized) hB
  have hc : 0≤fermionicNearConstant*R^(1/5:ℝ) := mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg hR _)
  have hn' : potentialForm (nearPotential y R) u.normalized≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*kinetic u.normalized+B^(3/5:ℝ)) := by
    calc
      _≤(fermionicNearConstant*R^(1/5:ℝ))*kinetic u.normalized^(3/5:ℝ) := by nlinarith [hn]
      _≤_ := mul_le_mul_of_nonneg_left hr hc
  have H := mul_le_mul_of_nonneg_left hn' hm.le
  rw [potentialForm_normalized_weight] at H
  calc
    _≤_ := H
    _=_ := by
      rw [mul_left_comm (mass u),mul_add,mul_left_comm (mass u) (B^(-2/5:ℝ)),kinetic_normalized_weight]
      ring
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb
lemma nearWeight_site_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
  have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
    simpa only [coulombKernel,norm_sub_rev] using H
  have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
    (continuous_position i).measurable)
  apply hh.congr
  filter_upwards [] with x
  by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]

lemma nearPotential_outer_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (R : ℝ)
    (s : Spins (m+k)) :
    Integrable (fun x => nearPotential y R ((joinConfiguration m k).symm x).1*‖u.value s x‖^2) := by
  simp only [nearPotential,position_split_left,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => nearWeight_site_integrable u y R s (Fin.castAdd k i))

theorem outer_nearPotential_linear {m k : ℕ} (u : H1Vector (m+k))
    (hu : PartlyAntisymmetric u (outIndexSet m k))
    (y : Space) {R B : ℝ} (hR : 0≤R) (hB : 0<B) :
    potentialForm (fun x => nearPotential y R ((joinConfiguration m k).symm x).1) u≤
      fermionicNearConstant*R^(1/5:ℝ)*(B^(-2/5:ℝ)*outerKinetic u+B^(3/5:ℝ)*mass u) := by
  let C := fermionicNearConstant*R^(1/5:ℝ)
  have hi (s : Spins (m+k)) : Integrable (fun x =>
      nearPotential y R ((outerJoinConfiguration k m).symm x).2*‖u.value s x‖^2) :=
    nearPotential_outer_integrable u y R s
  have H (s : Spins k) :
      (∫ x,potentialForm (nearPotential y R) (u.outerSlice s x))≤
        C*(B^(-2/5:ℝ)*(∫ x,kinetic (u.outerSlice s x))+B^(3/5:ℝ)*(∫ x,mass (u.outerSlice s x))) := by
    have hk := (kinetic_outerSlice_integrable u s).const_mul (B^(-2/5:ℝ))
    have hm := (mass_outerSlice_integrable u s).const_mul (B^(3/5:ℝ))
    have HA := u.outerSlice_antisymmetric s (hu.outer_symmetry s)
    have HH := integral_mono_ae (potentialForm_outerSlice_integrable u s _ (fun t => hi (outerAppend s t)))
      ((hk.add hm).const_mul C) (HA.mono (fun x hx => nearPotential_linear (u.outerSlice s x) hx y hR hB))
    simpa only [Pi.add_apply,integral_const_mul,integral_add hk hm] using HH
  have HH := Finset.sum_le_sum (fun (s : Spins k) (_ : s∈Finset.univ) => H s)
  rw [integral_potentialForm_outerSlice u _ hi] at HH
  simp only [←Finset.mul_sum,Finset.sum_add_distrib] at HH
  rw [integral_mass_outerSlice,integral_kinetic_outerSlice] at HH
  exact HH

lemma supported_core_nearPotential {m k : ℕ} (u : H1Vector (m+k)) (y : Space) {R t : ℝ}
    (hRt : R≤t) (hs : PartlySupported u (coreIndexSet m k) {z | t≤‖z-y‖}) :
    potentialForm (nearPotential y R) u=
      potentialForm (fun x => nearPotential y R ((joinConfiguration m k).symm x).1) u := by
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [hs s] with x hx
  by_cases hz : u.value s x=0
  · simp [hz]
  have hcore (i : Fin k) : nearWeight y R (position x (Fin.natAdd m i))=0 := by
    have hout : position x (Fin.natAdd m i)∉Metric.ball y R := by
      intro hi
      have hi' : ‖position x (Fin.natAdd m i)-y‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hi
      exact hz (hx _ ⟨i,rfl⟩ (not_le.mpr (hi'.trans_le hRt)))
    exact Set.indicator_of_notMem hout _
  simp only [nearPotential,Fin.sum_univ_add,position_split_left,hcore,Finset.sum_const_zero,add_zero]

lemma nearPotential_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (y : Space) (R : ℝ)
    (x : Configuration m) : nearPotential y R (reindexConfiguration e x)=nearPotential y R x := by
  unfold nearPotential
  exact (Equiv.sum_comp e (fun i => nearWeight y R (position (reindexConfiguration e x) i))).symm.trans
    (Finset.sum_congr rfl (fun i _ => by rw [position_reindex]))
lemma nearPotential_measurable {n : ℕ} (y : Space) (R : ℝ) : Measurable (nearPotential (n := n) y R) :=
  Finset.measurable_sum _ (fun i _ => (nearWeight_measurable y R).comp (continuous_position i).measurable)

lemma RecordedEnsemble.Conserves.nearPotential {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) (R : ℝ) :
    (∑ p,potentialForm (Coulomb.nearPotential y R) (T.vector p))=potentialForm (Coulomb.nearPotential y R) u := by
  have H := hT.nonnegative_observable (Coulomb.nearPotential y R) (nearPotential_measurable y R)
    (nearPotential_nonneg y R) (nearPotential_integrable u y R)
    (fun p s => by simpa only [nearPotential_reindex] using nearPotential_integrable (T.vector p) y R s)
  simpa only [Function.comp_def,nearPotential_reindex] using H

theorem RecordedEnsemble.nearPotential_le {n : ℕ} (T : RecordedEnsemble n) (u : H1Vector n)
    (hc : T.Conserves u) (ho : T.OutFermionic) (y : Space) {R t B : ℝ}
    (hR : 0≤R) (hRt : R≤t) (hB : 0<B)
    (hs : T.CoreSupported {z | t≤‖z-y‖}) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*(∑ p,outerKinetic (T.vector p))+B^(3/5:ℝ)*T.totalMass) := by
  rw [←hc.nearPotential y R]
  have H := Finset.sum_le_sum (fun (p : T.index) (_ : p∈Finset.univ) =>
    (supported_core_nearPotential (T.vector p) y hRt (hs p)).le.trans
      (outer_nearPotential_linear (T.vector p) (ho p) y hR hB))
  simpa only [←Finset.mul_sum,Finset.sum_add_distrib,RecordedEnsemble.totalMass] using H
end Coulomb

end

end OAI
