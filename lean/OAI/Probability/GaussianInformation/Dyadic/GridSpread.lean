import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.Covers

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

def euclideanGridCell {n : ℕ} (base : Fin n → ℝ) (h : ℝ) (a : Fin n → ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, base i + h * a i ≤ x i ∧ x i < base i + h * (a i + 1)}

lemma measurableSet_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    (h : ℝ) (a : Fin n → ℤ) : MeasurableSet (euclideanGridCell base h a) := by
  unfold euclideanGridCell
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin n → ℝ))
  exact (measurableSet_le (measurable_const (a := base i + h * a i)) hm).inter
    (measurableSet_lt hm (measurable_const (a := base i + h * (a i + 1))))

lemma volume_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 ≤ h) (a : Fin n → ℤ) :
    volume (euclideanGridCell base h a) = ENNReal.ofReal (h ^ n) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_euclideanGridCell base h a).nullMeasurableSet]
  have he : WithLp.toLp 2 ⁻¹' euclideanGridCell base h a =
      Set.pi Set.univ (fun i => Ico (base i + h * a i) (base i + h * (a i + 1))) := by
    ext x
    simp [euclideanGridCell]
  rw [he, Real.volume_pi_Ico]
  have hf : ∀ i, base i + h * (a i + 1) - (base i + h * a i) = h := by
    intro i
    ring
  simp only [hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hh]

lemma euclideanGridCell_disjoint {n : ℕ} (base : Fin n → ℝ) {h : ℝ} (hh : 0 < h)
    {a b : Fin n → ℤ} (hab : a ≠ b) :
    Disjoint (euclideanGridCell base h a) (euclideanGridCell base h b) := by
  rw [Function.ne_iff] at hab
  obtain ⟨i, hi⟩ := hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain hl | hl := lt_or_gt_of_ne hi
  · have ht : (a i : ℝ) + 1 ≤ b i := by exact_mod_cast hl
    have hs := mul_le_mul_of_nonneg_left ht hh.le
    linarith [(hx i).2, (hy i).1]
  · have ht : (b i : ℝ) + 1 ≤ a i := by exact_mod_cast hl
    have hs := mul_le_mul_of_nonneg_left ht hh.le
    linarith [(hy i).2, (hx i).1]

lemma dist_le_of_mem_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 ≤ h) (a : Fin n → ℤ)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ euclideanGridCell base h a)
    (hy : y ∈ euclideanGridCell base h a) : dist x y ≤ Real.sqrt n * h := by
  have hsq : ‖x - y‖ ^ 2 ≤ (n : ℝ) * h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, h^2 := Finset.sum_le_sum fun i _ => by
        have hx1 := (hx i).1
        have hx2 := (hx i).2
        have hy1 := (hy i).1
        have hy2 := (hy i).2
        change (x i - y i)^2 ≤ h^2
        have hab : |x i - y i| ≤ h := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
        nlinarith [sq_abs (x i - y i)]
      _ = _ := by simp
  rw [dist_eq_norm]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hn
  have hnn := Real.sqrt_nonneg (n : ℝ)
  have hm : 0 ≤ Real.sqrt n * h := mul_nonneg hnn hh
  nlinarith [norm_nonneg (x - y)]

lemma euclidean_closedBall_volume_le (n : ℕ) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    volume.real (closedBall x r) ≤
      (r * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n)^n := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [measureReal_def, volume.addHaar_closedBall_eq_addHaar_ball]
  exact euclidean_ball_volume_le n hn x hr

lemma grid_ball_count {n : ℕ} (hn : 0 < n) (base : Fin n → ℝ)
    {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (_ : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n))
    (s : Finset (Fin n → ℤ))
    (hs : ∀ a ∈ s, (euclideanGridCell base h a ∩ closedBall c R).Nonempty) :
    (s.card : ℝ) ≤ ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n := by
  classical
  let A := ⋃ a ∈ s, euclideanGridCell base h a
  have hsub : A ⊆ closedBall c (R + Real.sqrt n * h) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hya, hy⟩ := hs a ha
    have hdist := dist_le_of_mem_euclideanGridCell base hh.le a hxa hya
    exact (dist_triangle x y c).trans (add_le_add hdist hy) |>.trans_eq (add_comm _ _)
  have hmeasure : volume A = (s.card : ℝ≥0∞) * ENNReal.ofReal (h^n) := by
    rw [measure_biUnion_finset
      (fun a _ b _ hab => euclideanGridCell_disjoint base hh hab)
      (fun a _ => measurableSet_euclideanGridCell base h a)]
    simp [volume_euclideanGridCell base hh.le]
  have hra : 0 < R + Real.sqrt n * h := by positivity
  have hfin : volume (closedBall c (R + Real.sqrt n * h)) ≠ ∞ := measure_closedBall_lt_top.ne
  have hreal : (s.card : ℝ) * h^n ≤ volume.real (closedBall c (R + Real.sqrt n * h)) := by
    have hm := ENNReal.toReal_mono hfin (measure_mono hsub)
    rw [hmeasure] at hm
    simpa [measureReal_def, ENNReal.toReal_ofReal (pow_nonneg hh.le n)] using hm
  have hC : 0 ≤ Real.exp 1 * Real.sqrt Real.pi := by positivity
  have hn' : 0 < Real.sqrt (n : ℝ) := by positivity
  have hscaled : (R + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n ≤
      h * ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi)) := by
    apply (div_le_iff₀ hn').mpr
    calc
      _ ≤ (L * (Real.sqrt n * h) + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_right (add_le_add hscale le_rfl) hC
      _ = _ := by ring
  have hcard := hreal.trans (euclidean_closedBall_volume_le n hn c hra)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
    (R + Real.sqrt n * h) * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n) hscaled n
  have hfinal := hcard.trans hpow
  rw [mul_pow, mul_comm (h^n)] at hfinal
  exact (mul_le_mul_iff_left₀ (pow_pos hh n)).mp hfinal

lemma exists_mem_euclideanGridCell {n : ℕ} (base : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ a : Fin n → ℤ, x ∈ euclideanGridCell base h a := by
  refine ⟨fun i => ⌊(x i - base i) / h⌋, fun i => ?_⟩
  have hl := (le_div_iff₀ hh).mp (Int.floor_le ((x i - base i) / h))
  have hu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((x i - base i) / h))
  constructor <;> nlinarith

lemma finite_grid_hitting_ball {n : ℕ} (hn : 0 < n) (base : Fin n → ℝ)
    {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n)) :
    {a : Fin n → ℤ | (euclideanGridCell base h a ∩ closedBall c R).Nonempty}.Finite := by
  by_contra hinf
  let C := ((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
  have hb := grid_ball_count hn base hh hR hL hscale c s (fun a ha => hs ha)
  have hceil := Nat.le_ceil C
  rw [hcard, Nat.cast_add, Nat.cast_one] at hb
  dsimp [C] at hceil
  linarith

lemma measure_ball_le_of_grid {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} (hn : 0 < n) (ξ : α → EuclideanSpace ℝ (Fin n))
    (base : Fin n → ℝ) {h R L : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hscale : R ≤ L * (Real.sqrt n * h)) (c : EuclideanSpace ℝ (Fin n))
    (b : ℝ≥0∞) (hgrid : ∀ a, μ (ξ ⁻¹' euclideanGridCell base h a) ≤ b) :
    μ (ξ ⁻¹' closedBall c R) ≤
      ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
  classical
  let hs := finite_grid_hitting_ball hn base hh hR hL hscale c
  let s := hs.toFinset
  have hsub : ξ ⁻¹' closedBall c R ⊆ ⋃ a ∈ s, ξ ⁻¹' euclideanGridCell base h a := by
    intro z hz
    obtain ⟨a, ha⟩ := exists_mem_euclideanGridCell base hh (ξ z)
    exact mem_iUnion₂.mpr ⟨a, hs.mem_toFinset.mpr ⟨ξ z, ha, hz⟩, ha⟩
  have hcard := grid_ball_count hn base hh hR hL hscale c s
    (fun a ha => hs.mem_toFinset.mp ha)
  calc
    μ (ξ ⁻¹' closedBall c R) ≤ μ (⋃ a ∈ s, ξ ⁻¹' euclideanGridCell base h a) := measure_mono hsub
    _ ≤ ∑ a ∈ s, μ (ξ ⁻¹' euclideanGridCell base h a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ s, b := Finset.sum_le_sum fun a _ => hgrid a
    _ = (s.card : ℝ≥0∞) * b := by simp
    _ ≤ ENNReal.ofReal (((L + 1) * (Real.exp 1 * Real.sqrt Real.pi))^n) * b := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard

end RepeatedLocalization

end OAI
