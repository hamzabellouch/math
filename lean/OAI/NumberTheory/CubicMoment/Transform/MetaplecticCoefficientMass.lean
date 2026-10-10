import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientSeries

namespace OAI

/-! Injective coding of the actual published theta coefficients gives
the absolute dual coefficient mass with a subpower level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDecode (r : Eisenstein) (z : MetaplecticCoefficientCode r) : Eisenstein :=
  lambdaE^z.1*z.2.1.val*z.2.2.1.val*z.2.2.2.2.val*z.2.2.2.1.val^3

def metaplecticCoefficientMassTerm
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (σ : ℝ)
    (n : MetaplecticDualArgument) : ℝ :=
  ‖a r n*metaplecticLocalCoefficient r n‖/(Complex.normSq (metaplecticFrequency n))^(1+σ)

lemma metaplecticCoefficientMassTerm_nonneg
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (σ : ℝ)
    (n : MetaplecticDualArgument) : 0 ≤ metaplecticCoefficientMassTerm a r σ n := by
  exact div_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (Complex.normSq_nonneg _) _)

lemma metaplectic_coefficient_codes
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    (σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ n : MetaplecticDualArgument, a r n*metaplecticLocalCoefficient r n ≠ 0 →
        ∃ z : MetaplecticCoefficientCode r,
          n.val = metaplecticDecode r z ∧
          metaplecticCoefficientMassTerm a r σ n ≤ K*metaplecticCodeWeight r σ z := by
  obtain ⟨C,hC,hbound⟩ := ha
  refine ⟨C*(3:ℝ)^(1+σ),mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro r hr hsr n hn
  obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,_h'div,hwr,hs,he,hcoef⟩ := hbound r hr hsr n hn
  let z : MetaplecticCoefficientCode r :=
    ((j+1).toNat,ζ,⟨h,metaplectic_supported_divisor_mem hr hh hs hdiv⟩,⟨h',hh'⟩,⟨w,hw⟩)
  refine ⟨z,metaplectic_numerator_of_frequency n hj ζ h h' w he,?_⟩
  have hb := metaplectic_coefficient_decay hC.le hr n hj ζ hh hh' hw hwr he hcoef σ
  apply hb.trans_eq
  dsimp [metaplecticCodeWeight,z]
  ring

/-- The absolute dual coefficient sum is derived from the literal
published support formula, not postulated as a Voronoi estimate. -/
theorem metaplectic_coefficient_mass_small_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      Summable (metaplecticCoefficientMassTerm a r σ) ∧
      (∑' n : MetaplecticDualArgument, metaplecticCoefficientMassTerm a r σ n) ≤ C*norm r^ε := by
  obtain ⟨K,hK,hcodes⟩ := metaplectic_coefficient_codes ha σ
  obtain ⟨D,hD,hcodeBound⟩ := metaplecticCodeWeight_small_power hε hσ
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro r hr hsr
  let I := {n : MetaplecticDualArgument // a r n*metaplecticLocalCoefficient r n ≠ 0}
  choose f he hb using fun n : I => hcodes r hr hsr n.val n.property
  have hf : Function.Injective f := by
    intro n m hfm
    apply Subtype.ext
    apply Subtype.ext
    exact (he n).trans ((congrArg (metaplecticDecode r) hfm).trans (he m).symm)
  have hfullCode : Summable (fun z : MetaplecticCoefficientCode r => K*metaplecticCodeWeight r σ z) :=
    (metaplecticCodeWeight_summable r hσ).mul_left K
  have hI : Summable (fun n : I => metaplecticCoefficientMassTerm a r σ n) :=
    (hfullCode.comp_injective hf).of_nonneg_of_le
      (fun n => metaplecticCoefficientMassTerm_nonneg a r σ n) hb
  have hsupp : Function.support (metaplecticCoefficientMassTerm a r σ) ⊆
      {n | a r n*metaplecticLocalCoefficient r n ≠ 0} := by
    intro n hn hezero
    exact hn (by simp [metaplecticCoefficientMassTerm,hezero])
  have hsum : HasSum (metaplecticCoefficientMassTerm a r σ)
      (∑' n : I, metaplecticCoefficientMassTerm a r σ n) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mp hI.hasSum
  refine ⟨hsum.summable,?_⟩
  rw [hsum.tsum_eq]
  calc
    _ ≤ ∑' z : MetaplecticCoefficientCode r, K*metaplecticCodeWeight r σ z :=
      hI.tsum_le_tsum_of_inj f hf
        (fun z _ => mul_nonneg hK.le (metaplecticCodeWeight_nonneg r σ z)) hb hfullCode
    _ = K*(∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) :=
      (metaplecticCodeWeight_summable r hσ).tsum_mul_left K
    _ ≤ K*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hcodeBound r hr) hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
