import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimarySupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedMissingCoefficient

namespace OAI

/-! The signed-primary selection rule holds for the actual residue and
matches the prescribed coefficient on the same arithmetic frequency. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_primary_support_germ
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h))
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hh0 hz)
    (fun _ _ => analyticAt_const.meromorphicAt)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_primary_support (by linarith) hh hpos hneg

theorem cubicThetaArithmeticFourierResidue_primary_support
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaArithmeticFourierResidue h (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have ht := cubicThetaFrequencyContinuation_residue hh0
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at ht
  have he : (fun z : ℂ => (z-4/3)*cubicThetaFrequencyContinuation h z)=ᶠ[𝓝[≠] (4/3:ℂ)]
      (fun _ => 0) := by
    filter_upwards [cubicThetaFrequencyContinuation_primary_support_germ hh hpos hneg
      (s:=(4/3:ℂ)) (by norm_num)] with z hz
    rw [hz,mul_zero]
  exact tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds

theorem cubicThetaArithmeticCoefficient_signed_primary_support
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaArithmeticCoefficient (-lambdaE*h)=0 := by
  by_cases hc : Nonempty (CubicThetaCoordinates (-lambdaE*h))
  · let R := Classical.choice hc
    have hp : primary (R.cubePart^3) := by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
    have hcprim := primary_mul R.squarefree_primary hp
    have hn : ¬lambdaE ∣ -h := fun hd => hh (dvd_neg.mp hd)
    have hi : -lambdaE*h=lambdaE*(-h) := by ring
    have he := (congrArg (emultiplicity lambdaE) hi).symm.trans
      (congrArg (emultiplicity lambdaE) R.numerator_eq)
    have hl : emultiplicity lambdaE lambdaE=1 := by
      simpa only [pow_one,Nat.cast_one] using emultiplicity_pow_self_of_prime lambdaE_prime 1
    simp only [emultiplicity_mul lambdaE_prime,hl,
      emultiplicity_pow_self_of_prime lambdaE_prime,emultiplicity_eq_zero.mpr hn,
      unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
      primary_lambda_emultiplicity hp,zero_add,add_zero] at he
    have hR : R.order=1 := by exact_mod_cast he.symm
    have hunit : ¬((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1) := by
      intro hu
      have heq : -h=(R.unit:Eisenstein)*(R.squarefreePart*R.cubePart^3) := by
        apply mul_left_cancel₀ lambdaE_prime.ne_zero
        calc
          _ = -lambdaE*h := by ring
          _ = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) :=
            R.numerator_eq
          _ = _ := by rw [hR,pow_one]; ring
      rcases hu with hu | hu
      · apply hneg
        rw [hu,one_mul] at heq
        rw [heq]
        exact hcprim
      · apply hpos
        rw [hu,neg_one_mul] at heq
        rw [neg_inj.mp heq]
        exact hcprim
    rw [cubicThetaArithmeticCoefficient_formula R]
    simp only [CubicThetaCoordinates.coefficient,hR]
    norm_num only [Nat.reduceMod,one_ne_zero,false_and,ite_false]
    simp only [true_and,ite_eq_right hunit]
  · simp only [cubicThetaArithmeticCoefficient,dite_eq_right hc]

theorem cubicThetaNormalizedObservedCoefficient_primary_support_eq
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaNormalizedObservedCoefficient h=cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [cubicThetaArithmeticCoefficient_signed_primary_support hh hpos hneg]
  simp only [cubicThetaNormalizedObservedCoefficient,cubicThetaObservedWhittakerCoefficient,
    cubicThetaArithmeticFourierResidue_primary_support hh hpos hneg,
    mul_zero,zero_mul,zero_div]

end CubicFirstMoment

end

end OAI
