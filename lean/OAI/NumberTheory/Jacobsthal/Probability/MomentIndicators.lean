import OAI.NumberTheory.Jacobsthal.Analysis.JointModelDensity
import OAI.NumberTheory.Jacobsthal.Primes.StableSourceChebyshev

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceMoments
open NumberTheoryLean ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem finite_joint_moment_estimate (R xi w : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) (hw : 2 ≤ w)
    (s : ℝ) (hs : 480024 ≤ s) (H qA : ℕ) (hH : 0 < H) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (beta delta : ∀ t : ℕ,ZMod t)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) (S : Finset ℕ) (hS : S.card ≤ 2) :
    |modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S)-
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S| ≤
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S*Real.exp (-s/96)+
        4*(H.divisors.card : ℝ)*(H : ℝ)/
          (modelLength R xi (H : ℝ) (C0 : ℝ)*(H.totient : ℝ))*(w^s)^2 := by
  let b := modelLeft R xi (C0 : ℝ)
  let c := modelRight R xi (H : ℝ) (C0 : ℝ)
  let Y := modelLength R xi (H : ℝ) (C0 : ℝ)
  let X := Y*((H.totient : ℝ)/(H : ℝ))
  let K0 := jointDensity (divisorPrimes w H) S
  let K1 := jointDensity (coprimePrimes w H) S
  let a0 := atomWeight R xi w H C0*(divisorModulus w H : ℝ)
  let N : ℝ := (coprimeModulus w H).totient
  let err := 4*(H.divisors.card : ℝ)*(w^s)^2
  let B := X*K1*Real.exp (-s/96)+err
  let f (p : (ZMod (coprimeModulus w H))ˣ) : ℝ :=
    (coprimePositionSurvivors w H qA delta S p b c).card
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hY : 0 < Y := by dsimp [Y,modelLength,interceptScale];positivity
  have hX : 0 < X := mul_pos hY (div_pos (by exact_mod_cast Nat.totient_pos.mpr hH) hHR)
  have hbc : c-b = Y := by dsimp [c,b,modelRight,Y];ring
  have hK0 := jointDensity_nonneg (divisorPrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have hK01 := jointDensity_le_one (divisorPrimes w H) S
    (fun t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1)
  have ha0 : 0 < a0 := mul_pos (atomWeight_pos R xi w H C0 hR hxi hH)
    (by exact_mod_cast divisorModulus_pos w H)
  have hnorm : a0*N*X = 1 := model_normalization_identity R xi w H C0 hR hxi hH
  have hpoint (p : (ZMod (coprimeModulus w H))ˣ) : |f p-X*K1| ≤ B := by
    by_cases hz : K1 = 0
    · have he := zero_coprimePositionSurvivors w H qA delta S p hqA hz b c
      simp only [f,he,Finset.card_empty,Nat.cast_zero,hz,mul_zero,sub_zero,abs_zero,B,zero_mul,zero_add]
      dsimp [err]
      positivity
    · have hh := coprimePositionSurvivors_estimate w hw s hs H qA hH delta S hS p hqA b c
        (by linarith) hz
      rw [hbc] at hh
      exact hh
  have hsum : |(∑ p,f p)-N*(X*K1)| ≤ N*B := by
    have hconst : (∑ _p : (ZMod (coprimeModulus w H))ˣ,X*K1) = N*(X*K1) := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul,N]
    rw [← hconst,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p,|f p-X*K1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : (ZMod (coprimeModulus w H))ˣ,B := Finset.sum_le_sum (fun p _ => hpoint p)
      _ = N*B := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul,N]
  have hmass : modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) = a0*K0*(∑ p,f p) := by
    rw [joint_model_mass R xi w H qA C0 beta delta S hC0]
    dsimp [a0,K0,f,b,c]
    ring
  have hbase : a0*K0*(N*(X*K1)) = K0*K1 := by
    calc
      _ = (a0*N*X)*(K0*K1) := by ring
      _ = _ := by rw [hnorm,one_mul]
  have htotal := jointDensity_split w H S
  change K0*K1 = _ at htotal
  rw [← htotal,hmass,← hbase,← mul_sub,abs_mul,abs_of_nonneg (mul_nonneg ha0.le hK0)]
  have hm := mul_le_mul_of_nonneg_left hsum (mul_nonneg ha0.le hK0)
  have hscalar : a0*N = 1/X := (eq_div_iff hX.ne').mpr hnorm
  have he : a0*K0*(N*B) = K0*K1*Real.exp (-s/96)+K0*err/X := by
    dsimp [B]
    calc
      _ = (a0*N*X)*(K0*K1*Real.exp (-s/96))+(a0*N)*(K0*err) := by ring
      _ = _ := by rw [hnorm,hscalar];ring
  have her : 0 ≤ err := by dsimp [err];positivity
  have hlast : K0*err/X ≤ err/X := div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK01 her) hX.le
  have hright : err/X = 4*(H.divisors.card : ℝ)*(H : ℝ)/
      (modelLength R xi (H : ℝ) (C0 : ℝ)*(H.totient : ℝ))*(w^s)^2 := by
    dsimp [err,X,Y]
    field_simp
  rw [hbase]
  exact hm.trans (he ▸ add_le_add le_rfl (hlast.trans_eq hright))

end ErdosVarianceMoments



namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem weighted_joint_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (jointIndicator w H C0 qA beta delta S) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta S) := by
  unfold weightedMoment modelMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _hv
  unfold jointIndicator
  split_ifs <;> simp

theorem weighted_single_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (modelIndicator w H C0 qA beta delta j) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta {j}) := by
  rw [← weighted_joint_eq_mass]
  congr 1
  funext v
  exact (jointIndicator_singleton w H C0 qA beta delta j v).symm

theorem weighted_pair_eq_mass (R xi w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ) :
    weightedMoment (modelUniverse R xi w H C0) (fun _ => atomWeight R xi w H C0)
      (fun v => modelIndicator w H C0 qA beta delta i v*modelIndicator w H C0 qA beta delta j v) =
      modelMass R xi w H C0 (jointCondition w H C0 qA beta delta {i,j}) := by
  rw [← weighted_joint_eq_mass]
  congr 1
  funext v
  exact (jointIndicator_pair w H C0 qA beta delta i j v).symm

end ErdosVarianceUniformMoments


end Erdos970

end OAI
