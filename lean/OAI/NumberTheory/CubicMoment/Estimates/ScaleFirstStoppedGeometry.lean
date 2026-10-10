import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedDyads
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingCoefficientShift
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedStoppingWeights

namespace OAI

/-! Geometry derived from a surviving term of the original stopped dyad. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedStoppedSide_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ distinguishedStoppedSide X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hp,hs,hnorm⟩ := Finset.mem_filter.mp hn
  exact ⟨primaryPairSupport_primary _ _
    (fun _ hh => (mem_primaryElementBall.mp hh).1)
    (fun _ hh => (mem_primaryElementBall.mp hh).1) hp,hs,hnorm⟩

lemma distinguishedStoppedBeta_as_weights (i : ℕ) (ρ ξ X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) :
    distinguishedStoppedBeta i ρ ξ X h early d q =
      stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
        (distinguishedTupleCoefficient
          (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
          (fun a p => distinguishedStoppingWeights d a (norm p))
          primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
          q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early) := by
  unfold distinguishedStoppedBeta distinguishedScaleCoefficient
  have he : (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(d a).val)) =
      (fun a p => distinguishedStoppingWeights d a (norm p)) := by
    funext a p
    exact (distinguishedStoppingWeights_at d a p).symm
  rw [he]

lemma distinguishedStoppedDyad_witness (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ)
    (hne : distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k ≠ 0) :
    ∃ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
      ∃ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
        distinguishedStoppedBeta i ρ ξ X h early d q b ≠ 0 ∧
        centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) ≠ 0 := by
  obtain ⟨a,ha,hsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨b,hb,ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨a,ha,b,hb,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).1).2,?_⟩
  intro hz
  apply ht
  simp only [hz,ite_self,mul_zero]

theorem eventually_distinguishedStoppedDyad_geometry {ρ ξ ε : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) :
    ∀ᶠ X : ℝ in atTop, ∀ (i Ct : ℕ) (H : ℝ) (h : ℕ) (early : Bool)
      (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      distinguishedStoppedDyad i ρ ξ Ct H X h early d q j k ≠ 0 →
      X^(7/20:ℝ) ≤ stoppedNormDyadLength k ∧
      stoppedNormDyadLength k ≤ X^(39/100:ℝ) ∧
      stoppedNormDyadLength k ≤ X ∧
      X/16 ≤ (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ∧
      (stoppedNormDyadLength j/2)*stoppedNormDyadLength k ≤ 16*X ∧
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ q.1 := by
  filter_upwards [eventually_two_stage_stopped_dyad_range_dilation
    (Real.exp_pos primeProductWeights.radius) hgap,eventually_ge_atTop (1:ℝ)] with X hr hX
  intro i Ct H h early d q j k hk hne
  obtain ⟨a,ha,b,hb,hβ,hK⟩ := distinguishedStoppedDyad_witness i ρ ξ Ct H X h early d q j k hne
  have has := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
  have hbs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
  have hab := stoppedNormDyad_outer_bounds ha has.1
  have hbb := stoppedNormDyad_outer_bounds hb hbs.1
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have hsize := stoppedBeta_norm_bounds (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) (fun x hx => primeDetectorCutoff_zero hx)
    hρ hρ₂ hε hsmall
    (show 0 < (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) by split <;> positivity)
    (Real.rpow_pos_of_pos hXp ξ)
    (fun n hn => mem_primaryElementBall.mp hn) hk early hbs.2.1 hβ
  have hZ : (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(36/100:ℝ) ∨
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) = X^(38/100:ℝ) := by
    cases early <;> norm_num
  have hBr := hr (stoppedNormDyadLength k) _ (norm b) hZ hsize.1 hsize.2 hbb.1 hbb.2
  have hBX : stoppedNormDyadLength k ≤ X := hBr.2.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (show (39/100:ℝ) ≤ 1 by norm_num))
  have hKR := centeredHeightKernel_norm_range 0 H _ hXp hK
  have hprod := stopped_dyad_product_range
    (div_nonneg (stoppedNormDyadLength_pos j).le (by norm_num))
    (stoppedNormDyadLength_pos k).le
    (show stoppedNormDyadLength j/2 ≤ norm a ∧ norm a ≤ 2*(stoppedNormDyadLength j/2) by
      constructor
      · exact hab.1
      · nlinarith [hab.2]) hbb ⟨hKR.1.le,hKR.2.le⟩
  refine ⟨by simpa only [show (35/100:ℝ)=7/20 by norm_num] using hBr.1,
    hBr.2,hBX,by linarith [hprod.1],by linarith [hprod.2],?_⟩
  exact stoppedBeta_label_shift_bound _ _ _ _ _ hρ hXp hXF
    (fun n hn => (mem_primaryElementBall.mp hn).1) hbs.1 (hbb.2.trans hBX) hk early hβ

end CubicFirstMoment

end

end OAI
