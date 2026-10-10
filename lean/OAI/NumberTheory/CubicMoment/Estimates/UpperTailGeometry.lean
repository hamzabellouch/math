import OAI.NumberTheory.CubicMoment.Estimates.UpperTailStopping
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionGeometry

namespace OAI

/-! The actual upper stopped dyads have a short side just below X^(1/3).
All size bounds follow from a nonzero coefficient and the product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperStoppedBeta (i : ℕ) (κ ρ ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1
      0 (X^(1/3-κ)) (X^(1/3-κ)) true)

def upperTailStoppedDyad (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*upperStoppedBeta i κ ρ ξ X d q b*
        (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

theorem eventually_upper_stopped_dyad_range {κ ξ ε C : ℝ}
    (_hκ : 0 < κ) (hC : 0 < C) (hgap : ξ+ε < κ/2) :
    ∀ᶠ X : ℝ in atTop, ∀ (b N : ℝ),
      X^(1/3-κ) ≤ N → N ≤ 2*(C*X)^ε*X^ξ*X^(1/3-κ) →
      b/2 ≤ N → N ≤ b →
      X^(1/3-κ) ≤ b ∧ b ≤ X^(1/3-κ/2) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_const_mul_rpow_le
      (show ε+ξ+(1/3-κ) < 1/3-κ/2 by linarith) (4*C^ε)] with X hX hlarge
  intro b N hNlo hNhi hbN hNb
  refine ⟨hNlo.trans hNb,?_⟩
  have hh : 2*N ≤ X^(1/3-κ/2) := by
    calc
      2*N ≤ 4*(C*X)^ε*X^ξ*X^(1/3-κ) := by linarith
      _ = (4*C^ε)*X^(ε+ξ+(1/3-κ)) := by
        rw [Real.mul_rpow hC.le hX.le,Real.rpow_add hX,Real.rpow_add hX]
        ring
      _ ≤ _ := hlarge
  linarith

theorem eventually_upperTailStoppedDyad_geometry {κ ρ ξ ε : ℝ}
    (hκ : 0 < κ) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < κ/2) :
    ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (ℓ : ℤ) (H U : ℝ)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      upperTailStoppedDyad i ℓ κ ρ ξ H U X d q j k ≠ 0 →
      X^(1/3-κ) ≤ stoppedNormDyadLength k ∧
      stoppedNormDyadLength k ≤ X^(1/3-κ/2) ∧
      X/16 ≤ (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ∧
      (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ≤ 16*X := by
  filter_upwards [eventually_upper_stopped_dyad_range hκ
    (Real.exp_pos primeProductWeights.radius) hgap,eventually_ge_atTop (1:ℝ)] with X hr hX
  intro i ℓ H U d q j k hk hne
  obtain ⟨a,ha,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨b,hb,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hβ := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).1).2
  have hK : scaleFirstTailKernel ℓ H U X (a*b) ≠ 0 := by
    intro hz
    apply ht
    simp only [hz,ite_self,mul_zero]
  have has := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
  have hbs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
  have hab := stoppedNormDyad_outer_bounds ha has.1
  have hbb := stoppedNormDyad_outer_bounds hb hbs.1
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hsize := stoppedBeta_norm_bounds (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) (fun x hx => primeDetectorCutoff_zero hx)
    hρ hρ₂ hε hsmall (Real.rpow_pos_of_pos hXp (1/3-κ))
    (Real.rpow_pos_of_pos hXp ξ) (fun n hn => mem_primaryElementBall.mp hn)
    hk true hbs.2.1 hβ
  have hBr := hr (stoppedNormDyadLength k) (norm b) hsize.1 hsize.2 hbb.1 hbb.2
  have hKR := scaleFirstTailKernel_norm_range ℓ H U hXp hK
  have hprod := stopped_dyad_product_range
    (div_nonneg (stoppedNormDyadLength_pos j).le (by norm_num))
    (stoppedNormDyadLength_pos k).le
    (show stoppedNormDyadLength j/2 ≤ norm a ∧ norm a ≤ 2*(stoppedNormDyadLength j/2) by
      constructor
      · exact hab.1
      · nlinarith [hab.2]) hbb ⟨hKR.1.le,hKR.2.le⟩
  exact ⟨hBr.1,hBr.2,by linarith [hprod.1],by linarith [hprod.2]⟩

end CubicFirstMoment

end

end OAI
