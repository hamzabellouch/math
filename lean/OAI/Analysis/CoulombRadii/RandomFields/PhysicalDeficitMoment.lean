import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservedUnordered
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalDeficitTail
import OAI.Analysis.CoulombRadii.Screening.DeficitMoment

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_observed_positive_deficit_second_moment {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a : ℝ}
    (hr : 0<r) (hre : r+Real.sqrt 3*ℓ h≤a) :
    (∫ sample, (max ((Z:ℝ)-rawCount (Metric.ball 0 a)
      (observationArrayPositions h (observationCoordinateData ℓ sample))) 0)^2
      ∂observationLaw J (rawLaw ψ))≤
      (observedDeficitCoefficient ℓ D₀ r)^2+
        ∑' k : ℕ, (observedDeficitCoefficient ℓ D₀ r*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
  have := rawLaw_isProbability hd.2.2.1 hn
  let C := observedDeficitCoefficient ℓ D₀ r
  let f : ObservationSample n J → ℝ := fun sample =>
    max ((Z:ℝ)-rawCount (Metric.ball 0 a)
      (observationArrayPositions h (observationCoordinateData ℓ sample))) 0
  let t : ℕ → ℝ := fun k => C*(1+(k:ℝ))^3
  have hC : 1≤C := by
    dsimp [C,observedDeficitCoefficient]
    have : 0≤2*Coulomb.atomicInnerFieldConstant*(Coulomb.screenBaseMass r+
      Real.sqrt ((D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ)*r)) :=
      mul_nonneg (mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg)
        (add_nonneg (Coulomb.screenBaseMass_nonneg r) (Real.sqrt_nonneg _))
    linarith
  have ht : ∀ k, 0≤t k := fun k => mul_nonneg (by linarith) (by positivity)
  have hf : Measurable f :=
    (measurable_const.sub ((measurable_rawCount measurableSet_ball).comp
      ((measurable_observationArrayPositions h).comp (measurable_observationCoordinateData ℓ)))).max measurable_const
  have hz : 0≤(Z:ℝ) := Nat.cast_nonneg _
  have hb : ∀ sample, f sample≤t Z := by
    intro sample
    have hfZ : f sample≤(Z:ℝ) := max_le
      (sub_le_self _ (rawCount_nonneg _ _)) hz
    have hp : (Z:ℝ)≤(1+(Z:ℝ))^3 := by nlinarith [sq_nonneg (Z:ℝ),pow_nonneg hz 3]
    exact hfZ.trans (hp.trans (le_mul_of_one_le_left (by positivity) hC))
  have htail : ∀ k, (observationLaw J (rawLaw ψ)).real {sample | t k<f sample}≤Real.exp (-(k:ℝ)) := by
    intro k
    have he : {sample | t k<f sample}=observationCoordinateData ℓ ⁻¹'
        {y | C*(1+(k:ℝ))^3<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} := by
      ext sample
      simp only [f,t,mem_preimage,mem_ofPred_eq,lt_max_iff,not_lt.mpr (ht k),or_false]
    rw [he]
    exact physical_observed_deficit_exponential_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr
      (Nat.cast_nonneg k) hre
  have H := secondMoment_le_discrete_tails (observationLaw J (rawLaw ψ)) hf
    (fun sample => le_max_right _ _) t (fun k => Real.exp (-(k:ℝ))) ht Z hb htail
    (summable_cubic_exponential_tail C)
  simpa only [f,t,Nat.cast_zero,add_zero,one_pow,mul_one] using H
end NeutralAtom
end

end
end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma observationCoordinateData_positions_linear {n J : ℕ} (ℓ : Fin J → ℝ)
    (sample : ObservationSample n J) (j : Fin J) (i : Fin n) :
    observationArrayPositions j (observationCoordinateData ℓ sample) i =
      sample.1 i+ℓ j • observationNoiseVector (sample.2 j i) := by
  ext a
  simp [observationArrayPositions,observationCoordinateData,observationNoiseVector_coordinate]

lemma observationLaw_ae_linear_displacement {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (ℓ : Fin J → ℝ) (hℓ : ∀ j, 0≤ℓ j) :
    ∀ᵐ sample ∂observationLaw J ν, ∀ j i,
      ‖observationArrayPositions j (observationCoordinateData ℓ sample) i-sample.1 i‖≤
        Real.sqrt 3*ℓ j := by
  have hh : ∀ᵐ z ∂observationLaw J ν, ∀ j i a, |z.2 j i a|<1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (allObservationNoiseLaw_ae_support n J)
  filter_upwards [hh] with z hz j i
  rw [observationCoordinateData_positions_linear,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (hℓ j)]
  exact (mul_le_mul_of_nonneg_left (observationNoiseVector_norm_le (fun a => (hz j i a).le))
    (hℓ j)).trans_eq (mul_comm _ _)

lemma rawCount_flatten {n : ℕ} (A : Set Position) (x : Configuration n) :
    Coulomb.localCount A (flattenConfiguration n x)=rawCount A x := by
  simp only [Coulomb.localCount,rawCount,position_flattenConfiguration]

lemma raw_positive_deficit_moment_le_observed {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    {Z : ℝ} (hZ : 0≤Z) (ℓ : Fin J → ℝ) (hℓ : ∀ j, 0≤ℓ j)
    (j : Fin J) {a t : ℝ} (hat : a+Real.sqrt 3*ℓ j≤t) :
    stateWeightedIntegral ψ (fun x => (max (Z-rawCount (Metric.ball 0 t) x) 0)^2) ≤
      ∫ sample, (max (Z-rawCount (Metric.ball 0 a)
        (observationArrayPositions j (observationCoordinateData ℓ sample))) 0)^2
        ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  let f : Configuration n → ℝ := fun x => (max (Z-rawCount (Metric.ball 0 t) x) 0)^2
  let g : ObservationSample n J → ℝ := fun sample =>
    (max (Z-rawCount (Metric.ball 0 a)
      (observationArrayPositions j (observationCoordinateData ℓ sample))) 0)^2
  have hb (A : Set Position) (x : Configuration n) : ‖(max (Z-rawCount A x) 0)^2‖≤Z^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (sub_le_self _ (rawCount_nonneg _ _)) hZ) 2
  have hf : Measurable f := ((measurable_const.sub (measurable_rawCount measurableSet_ball)).max measurable_const).pow_const 2
  have hg : Measurable g := ((measurable_const.sub ((measurable_rawCount measurableSet_ball).comp
    ((measurable_observationArrayPositions j).comp (measurable_observationCoordinateData ℓ)))).max measurable_const).pow_const 2
  have hi : Integrable (fun z : ObservationSample n J => f z.1) (observationLaw J (rawLaw ψ)) :=
    (integrable_const (Z^2)).mono' (hf.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hb _ z.1))
  have hgi : Integrable g (observationLaw J (rawLaw ψ)) :=
    (integrable_const (Z^2)).mono' hg.aestronglyMeasurable
      (Eventually.of_forall (fun z => hb _ _))
  have he : (∫ z : ObservationSample n J, f z.1 ∂observationLaw J (rawLaw ψ))=
      stateWeightedIntegral ψ f := by
    rw [observationLaw,integral_prod _ hi]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_rawLaw hψ,rawExpectation_eq_stateWeightedIntegral hψ hf (fun x => hb _ x)]
  rw [←he]
  apply integral_mono_ae hi hgi
  filter_upwards [observationLaw_ae_linear_displacement (rawLaw ψ) ℓ hℓ] with sample hs
  dsimp [f,g]
  apply pow_le_pow_left₀ (le_max_right _ _)
  apply max_le_max_right
  apply sub_le_sub_left
  have H := raw_inner_observed_count_le
    (observationArrayPositions j (observationCoordinateData ℓ sample)) sample.1 hat
    (fun i => by simpa only [norm_sub_rev] using hs j i)
  simpa only [rawCount_flatten] using H

theorem physical_raw_positive_deficit_second_moment {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (j : Fin J) {r a t : ℝ}
    (hr : 0<r) (hre : r+Real.sqrt 3*ℓ j≤a) (hat : a+Real.sqrt 3*ℓ j≤t) :
    Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2)
      (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) ≤
      (observedDeficitCoefficient ℓ D₀ r)^2+
        ∑' k : ℕ, (observedDeficitCoefficient ℓ D₀ r*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
  rw [asH1_potentialForm]
  simp only [Coulomb.positiveInnerDeficit,rawCount_flatten]
  exact (raw_positive_deficit_moment_le_observed hd.2.2.1 hn (Nat.cast_nonneg Z) ℓ
    (fun j => (hℓ j).le) j hat).trans
    (physical_observed_positive_deficit_second_moment Z hZ hd hn hmin hE hbase hD ℓ hℓ j hr hre)

end NeutralAtom
end

end

end OAI
