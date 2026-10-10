import OAI.Analysis.IrrationalRotation.Couplings.OneCoordinateConditional

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.OneCoordinateCoupling
open CouplingMarginalBounds CouplingMixture FiniteKernelMixture

private lemma ofReal_total {I : Type*} [Fintype I] (q : ℝ) (p u : I → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hu : ∀ i, 0 ≤ u i) :
    ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (u i) =
      ENNReal.ofReal (q + ∑ i, p i * u i) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hu i))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hu i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (ENNReal.ofReal_mul (hp i)).symm

lemma intervalDensity_ge_one {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a < b) (hx : x ∈ Ico a b) : 1 ≤ intervalDensity a b x := by
  rw [intervalDensity, uniformDensity, Set.indicator_of_mem hx,
    baseLaw_interval_measure ha hb hab.le]
  exact (one_le_inv₀ (sub_pos.mpr hab)).mpr (by linarith)

lemma intervalLaw_Ici_eq_one {a b u : ℝ} (hab : a < b) (hu : u ≤ a) :
    intervalLaw a b (Ici u) = 1 := by
  let := intervalLaw_isProbabilityMeasure hab
  apply (mem_ae_iff_prob_eq_one measurableSet_Ici).mp
  filter_upwards [intervalLaw_ae_mem a b] with z hz
  exact hu.trans hz.1

lemma intervalLaw_Iio_eq_one {a b u : ℝ} (hab : a < b) (hu : b ≤ u) :
    intervalLaw a b (Iio u) = 1 := by
  let := intervalLaw_isProbabilityMeasure hab
  apply (mem_ae_iff_prob_eq_one measurableSet_Iio).mp
  filter_upwards [intervalLaw_ae_mem a b] with z hz
  exact hz.2.trans_le hu

section SourceParameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rightGivenLeft_component_lower (x : ℝ) (s : Set ℝ) (i : Fin 5)
    (hd : 1 ≤ leftDensity m a b i x) (hs : rightLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i) / 10 ≤
      rightGivenLeft κ m a b t x s := by
  unfold rightGivenLeft
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ x s i 10
  · exact ENNReal.one_le_ofReal.mpr hd
  · have hq := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    rw [ofReal_total _ _ _ (by linarith : 0 ≤ diagonalMass κ m a b t)
      (componentProbabilities_nonneg hκ0 (by linarith) ht0)
      (fun i => by fin_cases i <;> exact intervalDensity_nonneg _ _ _)]
    have hle := (leftMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le
    simpa only [leftMarginalDensity, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hle
  · exact hs

lemma leftGivenRight_component_lower (y : ℝ) (s : Set ℝ) (i : Fin 5)
    (hd : 1 ≤ rightDensity m a b i y) (hs : leftLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i) / 10 ≤
      leftGivenRight κ m a b t y s := by
  unfold leftGivenRight
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ y s i 10
  · exact ENNReal.one_le_ofReal.mpr hd
  · have hq := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    rw [ofReal_total _ _ _ (by linarith : 0 ≤ diagonalMass κ m a b t)
      (componentProbabilities_nonneg hκ0 (by linarith) ht0)
      (fun i => by fin_cases i <;> exact intervalDensity_nonneg _ _ _)]
    have hle := (rightMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht y).2.2.le
    simpa only [rightMarginalDensity, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hle
  · exact hs

theorem rightGivenLeft_crossing_lower {w x u : ℝ} (hw : w = a ∨ w = b)
    (hx0 : 0 ≤ x) (hxu : x < u) (hu : u ≤ 1 - w) :
    ENNReal.ofReal (rho κ m w) / 10 ≤ rightGivenLeft κ m a b t x (Ici u) := by
  have ha0 := width_pos (by linarith : 0 < m) ha
  have hb0 := width_pos (by linarith : 0 < m) hb
  rcases hw with hw | hw
  · subst w
    have hd : 1 ≤ leftDensity m a b 0 x := by
      change 1 ≤ intervalDensity 0 (1 - a / 2) x
      apply intervalDensity_ge_one (by norm_num) (by linarith) (by linarith)
      exact ⟨hx0, by linarith⟩
    have hs : rightLaw m a b 0 (Ici u) = 1 := by
      change intervalLaw (1 - a / 2) 1 (Ici u) = 1
      exact intervalLaw_Ici_eq_one (by linarith) (by linarith)
    exact rightGivenLeft_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht x (Ici u) 0 hd hs
  · subst w
    have hd : 1 ≤ leftDensity m a b 2 x := by
      change 1 ≤ intervalDensity 0 (1 - b / 2) x
      apply intervalDensity_ge_one (by norm_num) (by linarith) (by linarith)
      exact ⟨hx0, by linarith⟩
    have hs : rightLaw m a b 2 (Ici u) = 1 := by
      change intervalLaw (1 - b / 2) 1 (Ici u) = 1
      exact intervalLaw_Ici_eq_one (by linarith) (by linarith)
    exact rightGivenLeft_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht x (Ici u) 2 hd hs

theorem leftGivenRight_crossing_lower {w y u : ℝ} (hw : w = a ∨ w = b)
    (hy1 : y < 1) (huy : u ≤ y) (hu : w ≤ u) :
    ENNReal.ofReal (rho κ m w) / 10 ≤ leftGivenRight κ m a b t y (Iio u) := by
  have ha0 := width_pos (by linarith : 0 < m) ha
  have hb0 := width_pos (by linarith : 0 < m) hb
  rcases hw with hw | hw
  · subst w
    have hd : 1 ≤ rightDensity m a b 1 y := by
      change 1 ≤ intervalDensity (a / 2) 1 y
      apply intervalDensity_ge_one (by linarith) (by norm_num) (by linarith)
      exact ⟨by linarith, hy1⟩
    have hs : leftLaw m a b 1 (Iio u) = 1 := by
      change intervalLaw 0 (a / 2) (Iio u) = 1
      exact intervalLaw_Iio_eq_one (by linarith) (by linarith)
    exact leftGivenRight_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht y (Iio u) 1 hd hs
  · subst w
    have hd : 1 ≤ rightDensity m a b 3 y := by
      change 1 ≤ intervalDensity (b / 2) 1 y
      apply intervalDensity_ge_one (by linarith) (by norm_num) (by linarith)
      exact ⟨by linarith, hy1⟩
    have hs : leftLaw m a b 3 (Iio u) = 1 := by
      change intervalLaw 0 (b / 2) (Iio u) = 1
      exact intervalLaw_Iio_eq_one (by linarith) (by linarith)
    exact leftGivenRight_component_lower hκ0 hκ hm ha ha' hb hb' ht0 ht y (Iio u) 3 hd hs

end SourceParameters
end Invariant233.OneCoordinateCoupling

namespace Invariant233.OneCoordinateCoupling
open CouplingMixture CouplingMarginalBounds FiniteKernelMixture

lemma intervalDensity_ge_one_of_mem {a b x : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (hx : x ∈ Ico a b) :
    1 ≤ intervalDensity a b x := by
  simp only [intervalDensity, uniformDensity, Set.indicator_of_mem hx,
    baseLaw_interval_measure ha hb hab.le]
  exact (one_le_inv₀ (sub_pos.mpr hab)).2 (by linarith)

section SourceParameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

theorem rightGivenLeft_event_lower (i : Fin 5) (x : ℝ) (s : Set ℝ)
    (hd : 1 ≤ leftDensity m a b i x) (he : rightLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i / 10) ≤
      rightGivenLeft κ m a b t x s := by
  have hm0 : 0 < m := by linarith
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  have hd0 : ∀ i x, 0 ≤ leftDensity m a b i x := fun i x =>
    (leftDensity_bound (by linarith) (width_pos hm0 ha) ha'
      (width_pos hm0 hb) hb' i x).1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold rightGivenLeft
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ _ _ i
  · exact ENNReal.one_le_ofReal.mpr hd
  · rw [← ofReal_mixture_density _ _ _ hq0 hp0 hd0]
    exact (ENNReal.ofReal_le_ofReal
      (leftMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le).trans_eq
        (by norm_num)
  · exact he

theorem leftGivenRight_event_lower (i : Fin 5) (y : ℝ) (s : Set ℝ)
    (hd : 1 ≤ rightDensity m a b i y) (he : leftLaw m a b i s = 1) :
    ENNReal.ofReal (componentProbabilities κ m a b t i / 10) ≤
      leftGivenRight κ m a b t y s := by
  have hm0 : 0 < m := by linarith
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  have hd0 : ∀ i x, 0 ≤ rightDensity m a b i x := fun i x =>
    (rightDensity_bound (by linarith) (width_pos hm0 ha) ha'
      (width_pos hm0 hb) hb' i x).1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold leftGivenRight
  apply diagonalReplacementKernel_event_lower _ _ _ _ _ _ _ i
  · exact ENNReal.one_le_ofReal.mpr hd
  · rw [← ofReal_mixture_density _ _ _ hq0 hp0 hd0]
    exact (ENNReal.ofReal_le_ofReal
      (rightMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht y).2.2.le).trans_eq
        (by norm_num)
  · exact he

theorem rightGivenLeft_crossing {w u x : ℝ} (hw : w = a ∨ w = b)
    (hwu : w ≤ u) (huw : u ≤ 1 - w) (hx0 : 0 ≤ x) (hxu : x < u) :
    ENNReal.ofReal (rho κ m w / 10) ≤
      rightGivenLeft κ m a b t x (Ici u) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  rcases hw with hw | hw
  · subst w
    apply rightGivenLeft_event_lower hκ0 hκ hm ha ha' hb hb' ht0 ht (0 : Fin 5)
    · change 1 ≤ intervalDensity 0 (1 - a / 2) x
      apply intervalDensity_ge_one_of_mem <;> first | exact ⟨hx0, by linarith⟩ | linarith
    · change intervalLaw (1 - a / 2) 1 (Ici u) = 1
      apply intervalLaw_Ici_eq_one <;> linarith
  · subst w
    apply rightGivenLeft_event_lower hκ0 hκ hm ha ha' hb hb' ht0 ht (2 : Fin 5)
    · change 1 ≤ intervalDensity 0 (1 - b / 2) x
      apply intervalDensity_ge_one_of_mem <;> first | exact ⟨hx0, by linarith⟩ | linarith
    · change intervalLaw (1 - b / 2) 1 (Ici u) = 1
      apply intervalLaw_Ici_eq_one <;> linarith

theorem leftGivenRight_crossing {w u y : ℝ} (hw : w = a ∨ w = b)
    (hwu : w ≤ u) (huw : u ≤ 1 - w) (huy : u ≤ y) (hy1 : y < 1) :
    ENNReal.ofReal (rho κ m w / 10) ≤
      leftGivenRight κ m a b t y (Iio u) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  rcases hw with hw | hw
  · subst w
    apply leftGivenRight_event_lower hκ0 hκ hm ha ha' hb hb' ht0 ht (1 : Fin 5)
    · change 1 ≤ intervalDensity (a / 2) 1 y
      apply intervalDensity_ge_one_of_mem <;> first | exact ⟨by linarith, hy1⟩ | linarith
    · change intervalLaw 0 (a / 2) (Iio u) = 1
      apply intervalLaw_Iio_eq_one <;> linarith
  · subst w
    apply leftGivenRight_event_lower hκ0 hκ hm ha ha' hb hb' ht0 ht (3 : Fin 5)
    · change 1 ≤ intervalDensity (b / 2) 1 y
      apply intervalDensity_ge_one_of_mem <;> first | exact ⟨by linarith, hy1⟩ | linarith
    · change intervalLaw 0 (b / 2) (Iio u) = 1
      apply intervalLaw_Iio_eq_one <;> linarith

theorem pairLaw_fst_ae_mem_unit :
    ∀ᵐ x ∂(pairLaw κ m a b t).fst, x ∈ Ico (0 : ℝ) 1 := by
  rw [pairLaw_fst_density hκ0 hκ hm ha ha' hb hb' ht0 ht]
  exact (withDensity_absolutelyContinuous _ _).ae_le (intervalLaw_ae_mem 0 1)

theorem pairLaw_snd_ae_mem_unit :
    ∀ᵐ y ∂(pairLaw κ m a b t).snd, y ∈ Ico (0 : ℝ) 1 := by
  rw [pairLaw_snd_density hκ0 hκ hm ha ha' hb hb' ht0 ht]
  exact (withDensity_absolutelyContinuous _ _).ae_le (intervalLaw_ae_mem 0 1)

theorem rightGivenLeft_ae_all_crossings :
    ∀ᵐ x ∂(pairLaw κ m a b t).fst,
      ∀ w : ℝ, w = a ∨ w = b → ∀ u : ℝ, w ≤ u → u ≤ 1 - w → x < u →
        ENNReal.ofReal (rho κ m w / 10) ≤ rightGivenLeft κ m a b t x (Ici u) := by
  filter_upwards [pairLaw_fst_ae_mem_unit hκ0 hκ hm ha ha' hb hb' ht0 ht] with x hx
  intro w hw u hwu huw hxu
  exact rightGivenLeft_crossing hκ0 hκ hm ha ha' hb hb' ht0 ht hw hwu huw hx.1 hxu

theorem leftGivenRight_ae_all_crossings :
    ∀ᵐ y ∂(pairLaw κ m a b t).snd,
      ∀ w : ℝ, w = a ∨ w = b → ∀ u : ℝ, w ≤ u → u ≤ 1 - w → u ≤ y →
        ENNReal.ofReal (rho κ m w / 10) ≤ leftGivenRight κ m a b t y (Iio u) := by
  filter_upwards [pairLaw_snd_ae_mem_unit hκ0 hκ hm ha ha' hb hb' ht0 ht] with y hy
  intro w hw u hwu huw huy
  exact leftGivenRight_crossing hκ0 hκ hm ha ha' hb hb' ht0 ht hw hwu huw huy hy.2

end SourceParameters
end Invariant233.OneCoordinateCoupling

end

end OAI
