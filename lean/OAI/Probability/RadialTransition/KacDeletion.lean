import OAI.Probability.RadialTransition.FamilyStep

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def deletedKacPressure (φ : Potential) (m q : ℕ) (R t a β h : ℝ) : ℝ :=
  Real.log (boltzmannPartition (macroMeasure m q (t*h)) (fun x => β*macroKacEnergy φ m q R (t*a) x))/(t*((m:ℝ)*q/4)^3)

lemma family_kac_deletion {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ a R : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t ((m:ℝ)*q/4) β h-
      deletedKacPressure (familyPotential t b S) m q R t a β h| ≤
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  let : NeZero (m*q) := ⟨ne_of_gt (Nat.mul_pos hm hq)⟩
  have hba := prepend_nonneg ha hb
  have hRS := prepend_range hR hS
  have hsum := summable_prepend a hs
  have hrow' : 2197*t*bumpIntegral⁻¹*(∑' n, prepend a b n) ≤ (t^2/8)/8 := by rw [tsum_prepend _ hs]; exact hrow
  have hcont := continuous_familyPotential hba hRS hsum t
  have hbound := bounded_familyPotential hba hRS hsum t
  have hstable := stable_family_of_master ht0.le hba hRS hsum hsum (fun _ => le_rfl) hrow'
  let W := referenceMajorant t b S
  let K := fun i j => t*a*cellMajorant R bumpIntegral⁻¹ i j
  have hK : ∀ i j, 0 ≤ K i j := fun i j => mul_nonneg (mul_nonneg ht0.le ha) (cellMajorant_nonneg (zero_le_one.trans hR) (inv_nonneg.mpr bumpIntegral_pos.le) _ _)
  have hW : ∀ i j, 0 ≤ W i j := referenceMajorant_nonneg ht0.le hb hS
  have htotal (i j : Cell) : familyCellMajorant t b S i j+K i j = familyCellMajorant t (prepend a b) (prepend R S) i j :=
    (familyCellMajorant_prepend hb hS hs i j).symm
  have hcost := deletedPair_grid_bound (@gridEmbed (m*q)) (gridEmbed_injective _) (macroOf q)
    (measurableSet_halfCube ((m*q:ℕ)/4)) (halfCube_grid_cover (m*q))
    (continuous_familyPotential hb hS hs t) (continuous_singleAttraction R (t*a)) ht0 hβ (t*h)
    (familyCellMajorant t b S) K W (familyCellMajorant_nonneg ht0.le hb hS) hK
    (fun i j => by rw [htotal, htotal]; exact familyCellMajorant_symm _ _ _ _ _)
    (fun i => by simp_rw [htotal]; exact (familyCellMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le hba hRS hsum (gridEmbed i)).trans hrow')
    (familyPotential_grid_lower ht0.le hb hb hS hs hs (fun _ => le_rfl))
    (fun x y => by
      dsimp only [K, radialPair, singleAttraction]
      have hh := mul_le_mul_of_nonneg_left (scaledBumpProfile_le_cellMajorant hR x y) (mul_nonneg ht0.le ha)
      change -(t*a)*scaledBumpProfile R (dist x y) ≥ -(t*a*cellMajorant R bumpIntegral⁻¹ (cellOf x) (cellOf y))
      nlinarith)
    hW (family_abs_le_referenceMajorant ht hb hS hs)
  have hA : volume (halfCube (((m:ℝ)*q)/4)) ≠ ⊤ := by rw [volume_halfCube]; finiteness
  have hgrand := pairGrand_radial hcont hbound hstable hβ.le hA (t*h)
  rw [← familyPotential_prepend hb hS hs] at hcost
  simp only [Nat.cast_mul] at hcost
  rw [hgrand, grandOn_halfCube hcont hbound hstable hβ.le, grandOn_cube,
    deletedPair_macroKac hq (continuous_familyPotential hb hS hs t) (zero_lt_one.trans_le hR)] at hcost
  have hC : 0 ≤ referenceRowBound t (∑' n, b n) := referenceRowBound_nonneg ht0.le (tsum_nonneg hb)
  have hsumBound := deletionMajorant_grid_sum_range (m := m) hq (show 1 ≤ R₀ by linarith) hC hW
    (referenceMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le hb hS hs)
    (referenceMajorant_support hR₀ hrange)
  have hcoeff : 0 ≤ β/2*localMomentBound t β (t*h) :=
    mul_nonneg (by positivity) (localMomentBound_nonneg hβ.le _)
  have hlog := hcost.trans (mul_le_mul_of_nonneg_left hsumBound hcoeff)
  have hden : 0 < t*((m:ℝ)*q/4)^3 := by positivity
  unfold finiteGrandPressure deletedKacPressure
  rw [← sub_div, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  convert hlog using 1; first | rfl | (unfold boxPressureConstant; field_simp; ring)

end RadialTransition
end

end OAI
