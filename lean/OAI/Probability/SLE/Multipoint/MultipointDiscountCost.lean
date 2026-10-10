import OAI.Probability.SLE.Multipoint.MultipointProductGenerator

namespace OAI

/-! Continuous nonnegative drift cost and its bounded localization. -/

noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal

namespace SLEExactGauge.Multipoint

lemma continuous_logVelocity (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logVelocity κ p.1 p.2) := by
  have hre : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.continuous_re.comp continuous_fst.fst
  have him : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.continuous_im.comp continuous_fst.fst
  have hN : Continuous (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) :=
    ((hre.sub (continuous_const.mul continuous_snd)).pow 2).add
      (Real.continuous_exp.comp (continuous_const.mul him))
  exact (Real.continuous_exp.comp him).div hN (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')

lemma continuous_branchRegulator (κ D σ : ℝ) : Continuous (branchRegulator κ D σ) := by
  unfold branchRegulator
  have h : Continuous (fun z : ℂ × ℝ => (σ*κ/4)*(z.2-z.1.im)) :=
    continuous_const.mul (continuous_snd.sub (Complex.continuous_im.comp continuous_fst))
  exact continuous_const.mul (Real.continuous_exp.comp h)

lemma productDriftCost_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) :
    Continuous (fun p : (ι → ℂ × ℝ) × ℝ => productDriftCost s κ D σ p.1 p.2) := by
  have hz (i : ι) : Continuous (fun p : (ι → ℂ × ℝ) × ℝ => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hv (i : ι) : Continuous (fun p : (ι → ℂ × ℝ) × ℝ => logVelocity κ (p.1 i) p.2) :=
    (continuous_logVelocity κ).comp ((hz i).prodMk continuous_snd)
  have hd (i : ι) : Continuous (fun p : (ι → ℂ × ℝ) × ℝ => branchRegulator κ (D i) (σ i) (p.1 i)) :=
    (continuous_branchRegulator κ (D i) (σ i)).comp (hz i)
  unfold productDriftCost
  apply continuous_const.mul
  apply Continuous.add <;> apply continuous_const.mul
  · exact continuous_finsetSum s (fun i _ => (hd i).mul ((hv i).pow 2))
  · apply continuous_finsetSum
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    apply Continuous.mul
    · apply ((hd ij.1).mul (hd ij.2)).rpow_const
      intro p
      exact Or.inl (mul_pos (mul_pos (hD _ hi) (Real.exp_pos _))
        (mul_pos (hD _ hj) (Real.exp_pos _))).ne'
    · exact (hv ij.1).mul (hv ij.2)

lemma productDriftCost_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (z : ι → ℂ × ℝ) (x : ℝ) :
    0 ≤ productDriftCost s κ D σ z x := by
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  have hC : 0 < driftAllowance (greenExponent κ)*driftThreshold (greenExponent κ)^(-greenExponent κ) :=
    mul_pos (driftAllowance_pos hp) (Real.rpow_pos_of_pos (driftThreshold_pos hp) _)
  have he : 0 < (negativeDrift (greenExponent κ)/2)/(4*((s.card : ℝ)+1)) :=
    absorption_epsilon_pos (div_pos (negativeDrift_pos hp) (by norm_num)) _
  have hL := youngConstant_pos hp (sq_pos_of_pos (angularCoefficientConstant_pos hp)) he
  unfold productDriftCost
  apply mul_nonneg hκ.le
  apply add_nonneg
  · apply mul_nonneg hC.le
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_pos (hD i hi) (Real.exp_pos _)).le (sq_nonneg _)
  · apply mul_nonneg hL.le
    apply Finset.sum_nonneg
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg
      (mul_pos (hD _ hi) (Real.exp_pos _)).le (mul_pos (hD _ hj) (Real.exp_pos _)).le) _)
      (mul_pos (logVelocity_pos κ (z ij.1) x) (logVelocity_pos κ (z ij.2) x)).le

theorem exists_bounded_discount_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (G : (ι → ℂ × ℝ) × ℝ → ℝ) (C : ℝ≥0),
      Continuous G ∧ (∀ p, 0 ≤ G p ∧ |G p| ≤ C) ∧
      (∀ p, ‖p‖ ≤ R → G p = productDriftCost s κ D σ p.1 p.2) := by
  let b : ContDiffBump (0 : (ι → ℂ × ℝ) × ℝ) := ⟨R+1, R+2, by linarith, by linarith⟩
  let G := fun p : (ι → ℂ × ℝ) × ℝ => b p*productDriftCost s κ D σ p.1 p.2
  have hGc : Continuous G := b.continuous.mul (productDriftCost_continuous s κ D σ hD)
  have hGs : HasCompactSupport G := b.hasCompactSupport.mul_right
  obtain ⟨A, hA⟩ := hGc.bounded_above_of_compact_support hGs
  refine ⟨G, Real.toNNReal A, hGc, ?_, ?_⟩
  · intro p
    refine ⟨mul_nonneg b.nonneg (productDriftCost_nonneg s κ hκ hκ8 D σ hD p.1 p.2), ?_⟩
    exact (show |G p| ≤ A by simpa only [Real.norm_eq_abs] using hA p).trans (Real.le_coe_toNNReal A)
  · intro p hp
    have hb : b p = 1 := b.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖p‖ ≤ R+1
      linarith)
    simp only [G, hb, one_mul]

end SLEExactGauge.Multipoint

end

end OAI
