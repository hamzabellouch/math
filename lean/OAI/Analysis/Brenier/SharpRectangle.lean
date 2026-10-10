import OAI.Analysis.Brenier.SharpMaps

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Problem358

/-- A coordinate box, expressed in the Euclidean-space model used by the challenge. -/
def rectCoordBox {d : ℕ} (s : Fin d → Set ℝ) : Set (E d) :=
  {x | ∀ k, x k ∈ s k}

lemma rectCoordBox_measurable {d : ℕ} (s : Fin d → Set ℝ)
    (hs : ∀ k, MeasurableSet (s k)) : MeasurableSet (rectCoordBox s) := by
  have heq : rectCoordBox s = ⋂ k, (fun x : E d => x k) ⁻¹' s k := by
    ext x
    simp [rectCoordBox]
  rw [heq]
  exact MeasurableSet.iInter fun k =>
    (hs k).preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) k).measurable

lemma rectCoordBox_volume {d : ℕ} (s : Fin d → Set ℝ)
    (hs : ∀ k, MeasurableSet (s k)) :
    volume (rectCoordBox s) = ∏ k, volume (s k) := by
  have hm := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (s := Set.univ.pi s)
    ((MeasurableSet.pi (Set.to_countable (Set.univ : Set (Fin d)))
      (fun k _ => hs k)).nullMeasurableSet)
  calc
    volume (rectCoordBox s) = volume (Set.univ.pi s) := by
      simpa [rectCoordBox, Set.pi] using hm
    _ = ∏ k, volume (s k) := volume_pi_pi s

lemma rect_cube_eq (d : ℕ) :
    cube d = rectCoordBox (fun _ => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp [cube, rectCoordBox, abs_le]

lemma rect_cube_volume (d : ℕ) : volume (cube d) = (2 : ℝ≥0∞) ^ d := by
  rw [rect_cube_eq, rectCoordBox_volume _ (fun _ => measurableSet_Icc)]
  norm_num [Real.volume_Icc]

lemma rectCoordBox_uniform_mass {d : ℕ} (s : Fin d → Set ℝ)
    (hs : ∀ k, MeasurableSet (s k))
    (hsub : ∀ k, s k ⊆ Set.Icc (-1 : ℝ) 1) :
    uniformMeasure (cube d) (rectCoordBox s) =
      ∏ k, (volume (s k) / (2 : ℝ≥0∞)) := by
  have hbox : rectCoordBox s ⊆ cube d := by
    intro x hx k
    exact abs_le.mpr (hsub k (hx k))
  rw [uniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (rectCoordBox_measurable s hs),
    Set.inter_eq_left.mpr hbox, rectCoordBox_volume s hs, rect_cube_volume]
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.inv_pow]
  exact mul_comm _ _

/-- A thin rectangle contained in the region where the two sharpness maps disagree. -/
def sharpRectIntervals {d : ℕ} (i j : Fin d) (a b : ℝ) (k : Fin d) : Set ℝ :=
  if k = i then Set.Ioo a (a + b / 2)
  else if k = j then Set.Ioc (1 / 2 : ℝ) 1
  else Set.Icc (-1 : ℝ) 1

def sharpRectangle {d : ℕ} (i j : Fin d) (a b : ℝ) : Set (E d) :=
  rectCoordBox (sharpRectIntervals i j a b)

lemma sharpRectIntervals_measurable {d : ℕ} (i j : Fin d) (a b : ℝ) (k : Fin d) :
    MeasurableSet (sharpRectIntervals i j a b k) := by
  unfold sharpRectIntervals
  split_ifs <;> measurability

lemma sharpRectIntervals_subset {d : ℕ} (i j : Fin d) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a + b / 2 ≤ 1) (k : Fin d) :
    sharpRectIntervals i j a b k ⊆ Set.Icc (-1 : ℝ) 1 := by
  unfold sharpRectIntervals
  split_ifs
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  · exact Set.Subset.rfl

lemma sharpRectangle_mass {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b / 2 ≤ 1) :
    uniformMeasure (cube d) (sharpRectangle i j a b) = ENNReal.ofReal (b / 16) := by
  rw [sharpRectangle, rectCoordBox_uniform_mass _
    (sharpRectIntervals_measurable i j a b) (sharpRectIntervals_subset i j ha hab)]
  have hfactor : ∀ k : Fin d,
      volume (sharpRectIntervals i j a b k) / (2 : ℝ≥0∞) =
        (if k = i then ENNReal.ofReal (b / 4) else 1) *
        (if k = j then ENNReal.ofReal (1 / 4 : ℝ) else 1) := by
    intro k
    by_cases hi : k = i
    · subst k
      simp only [sharpRectIntervals, ite_eq_left, ite_eq_right hij, mul_one]
      rw [Real.volume_Ioo]
      have he : a + b / 2 - a = b / 2 := by ring
      rw [he]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    · by_cases hj : k = j
      · subst k
        simp only [sharpRectIntervals, ite_eq_right hi, ite_eq_left, one_mul, Real.volume_Ioc]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      · simp only [sharpRectIntervals, ite_eq_right hi, ite_eq_right hj, one_mul, Real.volume_Icc]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ b / 4)]
  congr 1
  ring

lemma sharpRectangle_real_mass {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b / 2 ≤ 1) :
    (uniformMeasure (cube d)).real (sharpRectangle i j a b) = b / 16 := by
  rw [Measure.real_def, sharpRectangle_mass hij ha hb hab,
    ENNReal.toReal_ofReal (by positivity)]

lemma sharpRectangle_measurable {d : ℕ} (i j : Fin d) (a b : ℝ) :
    MeasurableSet (sharpRectangle i j a b) :=
  rectCoordBox_measurable _ (sharpRectIntervals_measurable i j a b)

lemma sharpRectangle_subset_cube {d : ℕ} (i j : Fin d) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a + b / 2 ≤ 1) : sharpRectangle i j a b ⊆ cube d := by
  intro x hx k
  exact abs_le.mpr (sharpRectIntervals_subset i j ha hab k (hx k))

lemma sharpRectangle_subset_disagreement {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    sharpRectangle i j a b ⊆ {x | a < |x i| ∧ |x i| < a + b * x j} := by
  intro x hx
  have hi : a < x i ∧ x i < a + b / 2 := by
    simpa [sharpRectIntervals] using hx i
  have hj : 1 / 2 < x j ∧ x j ≤ 1 := by
    simpa [sharpRectIntervals, hij.symm] using hx j
  have hpos : 0 < x i := lt_of_le_of_lt ha hi.1
  rw [Set.mem_ofPred_eq, abs_of_pos hpos]
  constructor
  · exact hi.1
  · have hmul := mul_lt_mul_of_pos_left hj.1 hb
    linarith [hi.2]

/-- Integrate a unit lower bound on a finite-measure set. No global finiteness is needed. -/
lemma rect_integral_ge_measure {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} {R : Set X} {f : X → ℝ}
    (hR : MeasurableSet R) (hfinite : ρ R < ∞) (hf : Integrable f ρ)
    (hnonneg : ∀ x, 0 ≤ f x) (hbound : ∀ x ∈ R, 1 ≤ f x) :
    ρ.real R ≤ ∫ x, f x ∂ρ := by
  have hi : Integrable (R.indicator (fun _ : X => (1 : ℝ))) ρ :=
    ((integrableOn_const_iff (by finiteness)).mpr (Or.inr hfinite)).integrable_indicator hR
  have hle := integral_mono_ae hi hf (Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ R
    · simpa [Set.indicator_of_mem hx] using hbound x hx
    · simpa [Set.indicator_of_notMem hx] using hnonneg x))
  change (∫ x, R.indicator (1 : X → ℝ) x ∂ρ) ≤ _ at hle
  rwa [integral_indicator_one hR] at hle

lemma sharpRectangle_integral_lower {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b / 2 ≤ 1)
    {f : E d → ℝ} (hf : Integrable f (uniformMeasure (cube d)))
    (hnonneg : ∀ x, 0 ≤ f x)
    (hbound : ∀ x ∈ cube d, a < |x i| → |x i| < a + b * x j → 1 ≤ f x) :
    b / 16 ≤ ∫ x, f x ∂uniformMeasure (cube d) := by
  rw [← sharpRectangle_real_mass hij ha hb.le hab]
  apply rect_integral_ge_measure (sharpRectangle_measurable i j a b)
  · rw [sharpRectangle_mass hij ha hb.le hab]
    exact ENNReal.ofReal_lt_top
  · exact hf
  · exact hnonneg
  · intro x hx
    have hdis := sharpRectangle_subset_disagreement hij ha hb hx
    exact hbound x (sharpRectangle_subset_cube i j ha hab hx) hdis.1 hdis.2

lemma sharpRectangle_mapL2_lower {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b / 2 ≤ 1)
    {T S : E d → E d}
    (hint : Integrable (fun x => ‖T x - S x‖ ^ 2) (uniformMeasure (cube d)))
    (hbound : ∀ x ∈ cube d, a < |x i| → |x i| < a + b * x j →
      1 ≤ ‖T x - S x‖ ^ 2) :
    Real.sqrt (b / 16) ≤ mapL2Dist (uniformMeasure (cube d)) T S := by
  apply Real.sqrt_le_sqrt
  exact sharpRectangle_integral_lower hij ha hb hab hint (fun _ => sq_nonneg _) hbound

end Problem358

end

noncomputable section
open MeasureTheory
open scoped symmDiff
namespace Problem358.Sharpness

lemma slabMap_norm_sq_difference_le {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (x : E d) :
    ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2 ≤ 1 + b ^ 2 := by
  classical
  rw [slabMap_norm_sq_difference i j hij]
  by_cases hA : x ∈ centralCell i j a 0 <;>
    by_cases hB : x ∈ centralCell i j a b <;>
    simp [Set.indicator, Set.mem_symmDiff, hA, hB] <;> positivity

lemma integrable_slabMap_norm_sq_difference {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (ρ : Measure (E d)) [IsFiniteMeasure ρ] :
    Integrable (fun x => ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2) ρ := by
  have hm : Measurable (fun x => ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2) :=
    ((measurable_slabMap i j a 0).sub (measurable_slabMap i j a b)).norm.pow_const 2
  apply (integrable_const (1 + b ^ 2 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact slabMap_norm_sq_difference_le i j hij a b x

lemma slabMap_unit_lower_on_disagreement {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (x : E d) (hA : a < |x i|) (hB : |x i| < a + b * x j) :
    1 ≤ ‖slabMap i j a 0 x - slabMap i j a b x‖ ^ 2 := by
  classical
  have hA' : x ∉ centralCell i j a 0 := by
    simpa [centralCell] using not_le.mpr hA
  have hB' : x ∈ centralCell i j a b := hB.le
  simp only [slabMap, ite_eq_right hA', ite_eq_left hB']
  rw [norm_sq_outerSlope_sub_single i j hij]
  linarith [sq_nonneg b]

/-- A coarse lower bound sufficient for the sharp exponent, with no symmetric-difference
area calculation needed. -/
theorem slabMap_mapL2_lower {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b / 2 ≤ 1)
    :
    Real.sqrt (b / 16) ≤ mapL2Dist (uniformMeasure (cube d))
      (slabMap i j a 0) (slabMap i j a b) := by
  let : IsFiniteMeasure (uniformMeasure (cube d)) := ⟨by
    rw [uniformMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, rect_cube_volume,
      ENNReal.inv_mul_cancel (by positivity) (by finiteness)]
    exact ENNReal.one_lt_top⟩
  apply sharpRectangle_mapL2_lower hij ha hb hab
    (integrable_slabMap_norm_sq_difference i j hij a b _)
  intro x _ hA hB
  exact slabMap_unit_lower_on_disagreement i j hij a b x hA hB

end Problem358.Sharpness

end

end OAI
