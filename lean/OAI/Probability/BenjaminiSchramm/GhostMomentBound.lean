import OAI.Probability.BenjaminiSchramm.GhostCluster

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def quarterThreeQuarterMoment (p : unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, G.quarterTiltedMass ω x ^ (3 / 4 : ℝ) ∂G.law p

lemma quarterThreeQuarterMoment_aut (p : unitInterval) (φ : G.Aut) (x : V) :
    G.quarterThreeQuarterMoment p (φ.vertex x) = G.quarterThreeQuarterMoment p x := by
  unfold quarterThreeQuarterMoment
  conv_lhs => rw [← G.law_map_aut p φ]
  have hm : Measurable (fun ω => G.quarterTiltedMass ω (φ.vertex x) ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp (G.measurable_quarterTiltedMass _)
  rw [lintegral_map hm (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.quarterTiltedMass_aut]

theorem uniform_quarterGhost_moment_bound (hq : G.QuasiTransitive) (p : unitInterval)
    (hfin : ∀ x ∈ (G.orbitRepresentatives hq).roots,
      G.quarterThreeQuarterMoment p x < ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ x h, 0 ≤ h →
      G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ) := by
  let C := ∑ x ∈ (G.orbitRepresentatives hq).roots, G.quarterThreeQuarterMoment p x
  have hC : C < ⊤ := ENNReal.sum_lt_top.mpr hfin
  have hxC (x : V) : G.quarterThreeQuarterMoment p x ≤ C := by
    obtain ⟨y,hy,φ,rfl⟩ := (G.orbitRepresentatives hq).cover x
    rw [G.quarterThreeQuarterMoment_aut]
    exact Finset.single_le_sum (fun _ _ => bot_le) hy
  refine ⟨C.toReal + 1,by positivity,?_⟩
  intro x h hh
  have hxfin := lt_of_le_of_lt (hxC x) hC
  have hpow : Measurable (fun ω => G.quarterTiltedMass ω x ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp (G.measurable_quarterTiltedMass x)
  have hXi : Integrable (fun ω => (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ))
      (G.law p) := by
    simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top hpow.aemeasurable hxfin.ne
  have hI : (∫ ω, (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ) ∂G.law p) ≤ C.toReal := by
    have he := integral_toReal hpow.aemeasurable (ae_lt_top hpow hxfin.ne)
    calc
      _ = ∫ ω, (G.quarterTiltedMass ω x ^ (3 / 4 : ℝ)).toReal ∂G.law p :=
        integral_congr_ae (ae_of_all _ fun ω => ENNReal.toReal_rpow _ _)
      _ = (G.quarterThreeQuarterMoment p x).toReal := he
      _ ≤ C.toReal := ENNReal.toReal_mono hC.ne (hxC x)
  calc
    _ ≤ ∫ ω, h ^ (3 / 4 : ℝ) * (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ)
        ∂G.law p := by
      apply integral_mono
        (integrable_ghostKernel (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
          (fun _ => ENNReal.toReal_nonneg) hh) (hXi.const_mul _)
      intro ω
      exact (ghostKernel_le_threeQuarter hh ENNReal.toReal_nonneg).trans_eq
        (Real.mul_rpow hh ENNReal.toReal_nonneg)
    _ = h ^ (3 / 4 : ℝ) * ∫ ω, (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ)
        ∂G.law p := integral_const_mul _ _
    _ ≤ _ := by
      have hp : 0 ≤ h ^ (3 / 4 : ℝ) := Real.rpow_nonneg hh _
      nlinarith

omit [Countable V] [Countable E] in
lemma quarterGhost_square_bound {p : unitInterval} {K : ℝ}
    (hbound : ∀ x h, 0 ≤ h → G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ))
    (x : V) {h : ℝ} (hh : 0 ≤ h) :
    G.quarterGhostMagnetization p x h ^ 2 ≤ K ^ 2 * h ^ (3 / 2 : ℝ) := by
  have hnonneg : 0 ≤ G.quarterGhostMagnetization p x h :=
    integral_nonneg (fun _ => ghostKernel_nonneg hh ENNReal.toReal_nonneg)
  have hpow : (h ^ (3 / 4 : ℝ)) ^ 2 = h ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hh]
    norm_num
  calc
    _ ≤ (K * h ^ (3 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hnonneg (hbound x h hh) 2
    _ = _ := by rw [mul_pow,hpow]

omit [Countable V] [Countable E] in
lemma quarterGhostWeight_threeHalf (x v : V) :
    (G.quarterGhostWeight x v : ℝ) ^ (3 / 2 : ℝ) =
      (G.stabilizerWeight x v ^ (3 / 8 : ℝ)).toReal := by
  rw [← ENNReal.coe_toReal (G.quarterGhostWeight x v), G.coe_quarterGhostWeight,
    ENNReal.toReal_rpow, ← ENNReal.rpow_mul]
  norm_num

omit [Countable V] [Countable E] in
lemma rebased_quarterGhost_square_bound {p : unitInterval} {K : ℝ}
    (hbound : ∀ x h, 0 ≤ h → G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ))
    (x v : V) {h : ℝ} (hh : 0 ≤ h) :
    G.quarterGhostMagnetization p v (h * G.quarterGhostWeight x v) ^ 2 ≤
      K ^ 2 * h ^ (3 / 2 : ℝ) * (G.stabilizerWeight x v ^ (3 / 8 : ℝ)).toReal := by
  have hb := G.quarterGhost_square_bound hbound v (mul_nonneg hh (G.quarterGhostWeight x v).2)
  rw [Real.mul_rpow hh (G.quarterGhostWeight x v).2] at hb
  erw [G.quarterGhostWeight_threeHalf, ← mul_assoc] at hb
  exact hb

end CriticalPercolation.BondGraph

end

end OAI
