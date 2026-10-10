import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.Tubes

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def eCoordinate {n : ℕ} (z : Coordinate n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 z
noncomputable def eChart {n : ℕ} (z : Coordinate n) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (chart z)

lemma norm_eCoordinate_le_half {n : ℕ} (hn : 0 < n) {z : Coordinate n}
    (hz : z ∈ initialCube n) : ‖eCoordinate z‖ ≤ 1/2 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : ‖eCoordinate z‖^2 ≤ (1/2 : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, (1 / (2 * Real.sqrt n))^2 := Finset.sum_le_sum fun i _ => by
        have hl := hz i (mem_univ i)
        simp only [mem_Ico, neg_div] at hl
        change (z i)^2 ≤ _
        have ha : |z i| ≤ 1 / (2 * Real.sqrt n) := abs_le.mpr ⟨hl.1, hl.2.le⟩
        nlinarith [sq_abs (z i), abs_nonneg (z i)]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n from Nat.cast_nonneg _)
        field_simp
        nlinarith
  nlinarith [norm_nonneg (eCoordinate z)]

lemma chart_height_lipschitz {E : Type*} [SeminormedAddCommGroup E]
    {x y : E} (hx : ‖x‖ ≤ 1/2) (hy : ‖y‖ ≤ 1/2) :
    |Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2)| ≤ ‖x-y‖ := by
  have ax := norm_nonneg x
  have ay := norm_nonneg y
  have hx0 : 0 ≤ 1 - ‖x‖^2 := by nlinarith
  have hy0 : 0 ≤ 1 - ‖y‖^2 := by nlinarith
  have hx2 := Real.sq_sqrt hx0
  have hy2 := Real.sq_sqrt hy0
  have hx1 : 1/2 ≤ Real.sqrt (1 - ‖x‖^2) := by nlinarith [Real.sqrt_nonneg (1-‖x‖^2)]
  have hy1 : 1/2 ≤ Real.sqrt (1 - ‖y‖^2) := by nlinarith [Real.sqrt_nonneg (1-‖y‖^2)]
  have he : |Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2)| *
      (Real.sqrt (1 - ‖x‖^2) + Real.sqrt (1 - ‖y‖^2)) =
      |‖y‖ - ‖x‖| * (‖y‖ + ‖x‖) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (1 - ‖x‖^2) + Real.sqrt (1 - ‖y‖^2)),
      ← abs_mul, ← abs_of_nonneg (add_nonneg ay ax), ← abs_mul]
    congr 1
    nlinarith
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  have hsum : ‖y‖ + ‖x‖ ≤ 1 := by linarith
  have hp := mul_le_mul hn hsum (add_nonneg ay ax) (norm_nonneg (x-y))
  have hab := abs_nonneg (Real.sqrt (1 - ‖x‖^2) - Real.sqrt (1 - ‖y‖^2))
  nlinarith

lemma eChart_dist_le {n : ℕ} (hn : 0 < n) {z w : Coordinate n}
    (hz : z ∈ initialCube n) (hw : w ∈ initialCube n) :
    dist (eChart z) (eChart w) ≤ 2 * dist (eCoordinate z) (eCoordinate w) := by
  have hheight := chart_height_lipschitz (norm_eCoordinate_le_half hn hz) (norm_eCoordinate_le_half hn hw)
  have hs : ‖eChart z - eChart w‖^2 = ‖eCoordinate z - eCoordinate w‖^2 +
      (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, eChart, eCoordinate,
      PiLp.sub_apply, chart, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [dist_eq_norm, dist_eq_norm]
  have ha := abs_nonneg (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))
  have hb := norm_nonneg (eCoordinate z - eCoordinate w)
  have hc := norm_nonneg (eChart z - eChart w)
  nlinarith [sq_abs (Real.sqrt (1-‖eCoordinate z‖^2) - Real.sqrt (1-‖eCoordinate w‖^2))]

noncomputable def firstCoordinates {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => v i.castSucc)

lemma firstCoordinates_lipschitz (n : ℕ) : LipschitzWith 1 (firstCoordinates (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hs : ‖firstCoordinates x - firstCoordinates y‖^2 ≤ ‖x-y‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin n, (x i.castSucc - y i.castSucc)^2) ≤
      (∑ i : Fin n, (x i.castSucc - y i.castSucc)^2) + (x (Fin.last n)-y (Fin.last n))^2
    nlinarith [sq_nonneg (x (Fin.last n)-y (Fin.last n))]
  nlinarith [norm_nonneg (firstCoordinates x-firstCoordinates y), norm_nonneg (x-y)]

noncomputable def normalizedChart {n : ℕ} (Q : Cell n) (z : Coordinate n) :
    EuclideanSpace ℝ (Fin (n+1)) := (2 : ℝ)^Q.1 • (eChart z - eChart (cellCenter Q))

lemma normalizedChart_norm_le {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : ‖normalizedChart Q z‖ ≤ 2 := by
  have hchart := eChart_dist_le hn (cellSet_subset_initialCube hn Q hz)
    (cellSet_subset_initialCube hn Q (cellCenter_mem hn Q))
  have hgrid : ∀ w ∈ cellSet Q, eCoordinate w ∈ euclideanGridCell (cellLower Q) (cellWidth n Q.1) 0 := by
    intro w hw i
    rw [cellSet_eq_pi] at hw
    have hi := hw i (mem_univ i)
    simpa [euclideanGridCell, eCoordinate] using hi
  have hdiam := dist_le_of_mem_euclideanGridCell (cellLower Q) (cellWidth_pos hn).le 0
    (hgrid z hz) (hgrid _ (cellCenter_mem hn Q))
  have hp : 0 < (2 : ℝ)^Q.1 := by positivity
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have he : (2 : ℝ)^Q.1 * (Real.sqrt n * cellWidth n Q.1) = 1 := by
    unfold cellWidth
    field_simp
  unfold normalizedChart
  rw [norm_smul, Real.norm_of_nonneg hp.le, ← dist_eq_norm]
  calc
    _ ≤ (2 : ℝ)^Q.1 * (2 * (Real.sqrt n * cellWidth n Q.1)) :=
      mul_le_mul_of_nonneg_left (hchart.trans (mul_le_mul_of_nonneg_left hdiam (by norm_num))) hp.le
    _ = 2 := by nlinarith [he]

lemma normalizedChart_measurable {n : ℕ} (Q : Cell n) : Measurable (normalizedChart Q) := by
  unfold normalizedChart eChart
  have hc : Measurable (chart (n := n)) := measurable_chart n
  fun_prop

noncomputable def normalizedGridBase {n : ℕ} (Q : Cell n) : Fin n → ℝ :=
  fun i => (2 : ℝ)^Q.1 * (cellLower Q i - cellCenter Q i)

lemma normalizedGrid_mem_iff {n : ℕ} (Q : Cell n) (l : ℕ) (v : Fin n → ℤ) (z : Coordinate n) :
    firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v ↔
    ∀ i, cellLower Q i + cellWidth n (Q.1+l) * (v i : ℝ) ≤ z i ∧
      z i < cellLower Q i + cellWidth n (Q.1+l) * ((v i : ℝ)+1) := by
  have hp : 0 < (2 : ℝ)^Q.1 := by positivity
  have he (i : Fin n) : firstCoordinates (normalizedChart Q z) i =
      (2 : ℝ)^Q.1 * (z i - cellCenter Q i) := by
    simp [firstCoordinates, normalizedChart, eChart, chart]
  simp only [euclideanGridCell, mem_ofPred_eq, he, normalizedGridBase]
  apply forall_congr'
  intro i
  constructor
  · intro h
    constructor
    · have hh : (2 : ℝ)^Q.1 * (cellLower Q i + cellWidth n (Q.1+l)*(v i : ℝ) - cellCenter Q i) ≤
          (2 : ℝ)^Q.1 * (z i - cellCenter Q i) := by nlinarith [h.1]
      have hh' := (mul_le_mul_iff_right₀ hp).mp hh
      linarith
    · have hh : (2 : ℝ)^Q.1 * (z i - cellCenter Q i) <
          (2 : ℝ)^Q.1 * (cellLower Q i + cellWidth n (Q.1+l)*((v i : ℝ)+1) - cellCenter Q i) := by
        nlinarith [h.2]
      have hh' := (mul_lt_mul_iff_right₀ hp).mp hh
      linarith
  · intro h
    constructor
    · have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right h.1 (cellCenter Q i)) hp.le
      nlinarith
    · have hh := mul_lt_mul_of_pos_left (sub_lt_sub_right h.2 (cellCenter Q i)) hp
      nlinarith

lemma normalizedGrid_valid_of_inter {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ)
    (v : Fin n → ℤ) {z : Coordinate n} (hz : z ∈ cellSet Q)
    (hg : firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) : ∀ i, 0 ≤ v i ∧ v i < (2^l : ℕ) := by
  rw [normalizedGrid_mem_iff] at hg
  rw [cellSet_eq_pi] at hz
  intro i
  have hh := hz i (mem_univ i)
  dsimp only at hh
  have hw := cellWidth_pos (J := Q.1+l) hn
  have he : cellWidth n (Q.1+l) * (2 : ℝ)^l = cellWidth n Q.1 := by
    rw [cellWidth_add, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
  have hlr : (-1 : ℝ) < (v i : ℝ) := by
    by_contra h
    have hb := mul_le_mul_of_nonneg_left (le_of_not_gt h) hw.le
    nlinarith [hh.1, (hg i).2]
  have hur : (v i : ℝ) < (2 : ℝ)^l := by
    by_contra h
    have hb := mul_le_mul_of_nonneg_left (le_of_not_gt h) hw.le
    nlinarith [hh.2, (hg i).1]
  constructor
  · have : (-1 : ℤ) < v i := by exact_mod_cast hlr
    omega
  · exact_mod_cast hur

lemma normalizedGrid_child_mem {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l))
    {z : Coordinate n}
    (hg : firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) (fun i => (a i).val)) :
    z ∈ cellSet (childCell Q l a) := by
  rw [normalizedGrid_mem_iff] at hg
  rw [cellSet_eq_pi]
  intro i hi
  dsimp only
  rw [childCell_lower]
  have h := hg i
  simp only [Int.cast_natCast] at h
  change cellLower Q i + cellWidth n (Q.1+l)*(a i : ℝ) ≤ z i ∧
    z i < cellLower Q i + cellWidth n (Q.1+l)*(a i : ℝ) + cellWidth n (Q.1+l)
  constructor <;> nlinarith [h.1, h.2]

lemma measure_normalizedGrid_le {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    (b : ℝ≥0∞) (hchild : ∀ a, μ (cellSet (childCell Q l a)) ≤ b) (v : Fin n → ℤ) :
    μ ((firstCoordinates ∘ normalizedChart Q) ⁻¹' euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) ≤ b := by
  classical
  have hae : ∀ᵐ z ∂μ, z ∈ cellSet Q := by
    apply ae_iff.mpr
    exact hsupport
  by_cases hv : ∀ i, 0 ≤ v i ∧ v i < (2^l : ℕ)
  · let a : Fin n → Fin (2^l) := fun i => ⟨(v i).toNat, by
      exact (Int.toNat_lt (hv i).1).mpr (hv i).2⟩
    have he : (fun i => ((a i).val : ℤ)) = v := by
      funext i
      exact Int.toNat_of_nonneg (hv i).1
    refine (measure_mono_ae (hae.mono (fun z _ hg => ?_))).trans (hchild a)
    apply normalizedGrid_child_mem Q l a
    change firstCoordinates (normalizedChart Q z) ∈ euclideanGridCell (normalizedGridBase Q)
      ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v at hg
    simpa only [he] using hg
  · have hempty : μ ((firstCoordinates ∘ normalizedChart Q) ⁻¹' euclideanGridCell (normalizedGridBase Q)
        ((2 : ℝ)^Q.1 * cellWidth n (Q.1+l)) v) = 0 := by
      apply measure_mono_null (t := (cellSet Q)ᶜ) _ hsupport
      intro z hg hz
      exact hv (normalizedGrid_valid_of_inter hn Q l v hz hg)
    rw [hempty]
    exact bot_le

def DyadicSpread {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (B : ℝ) : Prop :=
  ∀ (l : ℕ) (R : Cell n), R.1 = Q.1 + l → cellSet R ⊆ cellSet Q →
    μ (cellSet R) ≤ ENNReal.ofReal (B * (2 : ℝ)^(-(n : ℝ)*l/2))

lemma DyadicSpread.child_floor {n : ℕ} (hn : 0 < n) {μ : Measure (Coordinate n)}
    {Q : Cell n} {B : ℝ} (hB : 0 ≤ B) (h : DyadicSpread μ Q B) (l : ℕ)
    (a : Fin n → Fin (2^l)) :
    μ (cellSet (childCell Q l a)) ≤ ENNReal.ofReal (B * (1/2 : ℝ)^((n/2)*l)) := by
  refine (h l (childCell Q l a) rfl (childCell_subset hn Q l a)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hB
  have hdiv : ((n/2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
  have he : -(n : ℝ) * l / 2 ≤ -(((n/2)*l : ℕ) : ℝ) := by
    simp only [Nat.cast_mul]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ l from Nat.cast_nonneg _) (sub_nonneg.mpr hdiv)]
  have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div, inv_pow] using hr

noncomputable def gridConstant : ℝ := 3 * (Real.exp 1 * Real.sqrt Real.pi)
noncomputable def tubeConstant : ℝ := 13 * max 1 gridConstant

lemma gridConstant_nonneg : 0 ≤ gridConstant := by unfold gridConstant; positivity
lemma tubeConstant_ge_one : 1 ≤ tubeConstant := by
  unfold tubeConstant
  nlinarith [le_max_left (1 : ℝ) gridConstant]

lemma dyadic_tube_tail {n : ℕ} (hn : 0 < n) (Q : Cell n)
    (μ : Measure (Coordinate n)) (hsupport : μ (cellSet Q)ᶜ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hspread : DyadicSpread μ Q B)
    (V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (n+1)))) (hV : (V : Set (EuclideanSpace ℝ (Fin (n+1)))).Nonempty)
    (e : ℕ) (he : Module.finrank ℝ V.direction + e ≤ n/2) (j : ℕ) :
    μ {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ (1/2 : ℝ)^j} ≤
      ENNReal.ofReal (B * tubeConstant^n * (1/2 : ℝ)^(e*j)) := by
  let δ : ℝ := (1/2 : ℝ)^j
  let q := Module.finrank ℝ V.direction
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw : 0 < (2 : ℝ)^Q.1 * cellWidth n (Q.1+j) := mul_pos (by positivity) (cellWidth_pos hn)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hscale : Real.sqrt n * ((2 : ℝ)^Q.1 * cellWidth n (Q.1+j)) = δ := by
    dsimp [cellWidth, δ]
    rw [pow_add]
    simp only [one_div, inv_pow]
    field_simp
  have ht := measure_affine_tube_le_of_grid μ hn (normalizedChart Q) firstCoordinates
    (firstCoordinates_lipschitz n) V hV (normalizedGridBase Q) hw (by norm_num : (0:ℝ) ≤ 2)
    hd (by norm_num : (0:ℝ) ≤ 2) (by rw [hscale])
    (ENNReal.ofReal (B * δ^(n/2)))
    (fun v => measure_normalizedGrid_le hn Q j μ hsupport _
      (fun a => by simpa only [δ, ← pow_mul, Nat.mul_comm j (n/2)] using hspread.child_floor hn hB j a) v)
  have hae : ∀ᵐ z ∂μ, z ∈ cellSet Q := by exact ae_iff.mpr hsupport
  have hmono : μ {z | infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ δ} ≤
      μ {z | ‖normalizedChart Q z‖ ≤ 2 ∧ infDist (normalizedChart Q z) (V : Set (EuclideanSpace ℝ (Fin (n+1)))) ≤ δ} := by
    apply measure_mono_ae
    exact hae.mono fun z hz hzd => ⟨normalizedChart_norm_le hn Q hz, hzd⟩
  refine (hmono.trans ht).trans ?_
  have hcn : 0 ≤ tubeConstant := le_trans (by norm_num) tubeConstant_ge_one
  have hg : 0 ≤ gridConstant := gridConstant_nonneg
  have hq : q ≤ n/2 := by dsimp [q]; omega
  have hqn : q ≤ n := hq.trans (Nat.div_le_self _ _)
  have hplane : ((4 * (2 : ℝ) + 5 * δ) / δ)^q ≤ ((13 : ℝ)/δ)^q := by
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff_of_pos_right hd).mpr
    linarith
  have hc : (13 : ℝ)^q * gridConstant^n ≤ tubeConstant^n := by
    calc
      _ ≤ (13 : ℝ)^n * (max 1 gridConstant)^n := by
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 13) hqn)
          (pow_le_pow_left₀ hg (le_max_right 1 gridConstant) n) (pow_nonneg hg _)
          (by positivity)
      _ = _ := by rw [← mul_pow]; rfl
  have hpow : δ^(n/2-q) ≤ δ^e := pow_le_pow_of_le_one hd.le hd1 (by omega)
  have hcancel : ((13 : ℝ)/δ)^q * δ^(n/2) = (13 : ℝ)^q * δ^(n/2-q) := by
    rw [pow_sub₀ δ hd.ne' hq, div_pow]
    ring
  have hreal : ((4 * (2 : ℝ) + 5 * δ)/δ)^q * gridConstant^n * (B * δ^(n/2)) ≤
      B * tubeConstant^n * δ^e := by
    calc
      _ ≤ ((13 : ℝ)/δ)^q * gridConstant^n * (B * δ^(n/2)) := by gcongr
      _ = B * gridConstant^n * (((13 : ℝ)/δ)^q * δ^(n/2)) := by ring
      _ = B * ((13 : ℝ)^q * gridConstant^n) * δ^(n/2-q) := by rw [hcancel]; ring
      _ ≤ B * tubeConstant^n * δ^e := by gcongr
  have hp : 0 ≤ ((4 * (2 : ℝ) + 5 * δ)/δ)^q := by positivity
  have hpg : 0 ≤ gridConstant^n := pow_nonneg hg _
  simp only [show (2:ℝ)+1=3 by norm_num]
  change ENNReal.ofReal (((4 * (2 : ℝ) + 5 * δ)/δ)^q) * ENNReal.ofReal (gridConstant^n) *
    ENNReal.ofReal (B * δ^(n/2)) ≤ _
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (mul_nonneg hp hpg)]
  convert ENNReal.ofReal_le_ofReal hreal using 1
  dsimp [δ]
  rw [← pow_mul, Nat.mul_comm j e]

end RepeatedLocalization

end OAI
