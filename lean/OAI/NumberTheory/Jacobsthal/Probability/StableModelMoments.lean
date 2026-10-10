import OAI.NumberTheory.Jacobsthal.Estimates.UniformJointModel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem variancePrimes_eq_cutoff (w : ℝ) :
    variancePrimes w = LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ :=
  (cutoffPrimes_eq_filtered_Ioc _).symm

theorem model_moment_bounds (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (zeta : ℝ)
    (hrel : ∀ S : Finset ℕ,S.card ≤ 2 →
      |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
        jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
          zeta*jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S) :
    (∑ _v ∈ modelUniverse R xi w H C0,atomWeight R xi w H C0) ≤ 1+zeta ∧
    (∀ j : ℕ,(1-zeta)*sieveProduct (variancePrimes w) ≤
      weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (modelIndicator w H C0 qA beta delta j)) ∧
    (∀ j : ℕ,weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (modelIndicator w H C0 qA beta delta j) ≤ (1+zeta)*sieveProduct (variancePrimes w)) ∧
    (∀ i j : ℕ,weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
        (fun v => modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v) ≤
          (1+zeta)*pairKernel (variancePrimes w) i j) := by
  have hmass := hrel ∅ (by simp)
  have he : jointCondition w H C0 qA beta delta ∅ = (fun _ => True) := by
    funext v
    exact propext (by simp [jointCondition])
  rw [he] at hmass
  have hkempty : jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) ∅ = 1 := by
    simp [jointDensity,positionDensity,positionResidues]
  simp only [hkempty,mul_one,modelMass,Finset.filter_true] at hmass
  have hsingle (j : ℕ) := hrel {j} (by simp)
  have hsingle' (j : ℕ) :
      |weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
          (modelIndicator w H C0 qA beta delta j)-sieveProduct (variancePrimes w)| ≤
        zeta*sieveProduct (variancePrimes w) := by
    simpa only [weighted_single_eq_mass,variancePrimes_eq_cutoff,jointDensity_singleton] using hsingle j
  refine ⟨by linarith [(abs_le.mp hmass).2],?_,?_,?_⟩
  · intro j
    nlinarith [(abs_le.mp (hsingle' j)).1]
  · intro j
    nlinarith [(abs_le.mp (hsingle' j)).2]
  · intro i j
    have hcard : ({i,j} : Finset ℕ).card ≤ 2 := by
      calc
        _ ≤ ({j} : Finset ℕ).card+1 := Finset.card_insert_le i _
        _ = 2 := by simp
    have hh := hrel {i,j} hcard
    rw [jointDensity_pair,← weighted_pair_eq_mass] at hh
    rw [variancePrimes_eq_cutoff]
    nlinarith [(abs_le.mp hh).2]

end ErdosVarianceUniformMoments

end

end Erdos970

end OAI
