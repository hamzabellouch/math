import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.GroupFermionicCoefficients

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma cubeMass_nonneg {n : ℕ} (ψ : H1Vector n) (b : ℝ) : 0 ≤ cubeMass ψ b :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma grid_leading_summable {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    Summable (fun k : GridAssignment n =>
      gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (groupLeadingCount_nonneg _) (cubeMass_nonneg _ _))
    (fun k => mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (cubeMass_nonneg _ _))
    ((grid_hasSum_mass ψ hb).summable.mul_left ((n : ℝ)^(5/3 : ℝ)))

lemma grid_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    (b⁻¹)^2 * thomasFermiCoefficient *
        (∑' k : GridAssignment n,
          gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have HM := grid_hasSum_mass ψ hb
  have HK := grid_hasSum_kinetic ψ hb
  have HL := (grid_leading_summable ψ hb).hasSum
  have HS := (HL.mul_left ((b⁻¹)^2 * thomasFermiCoefficient)).sub
    (HM.mul_left ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)))
  apply hasSum_le _ HS HK
  intro k
  have H := grid_cube_kinetic_lower hn ψ hψ hb k
  nlinarith

section GridIndex
variable {I : Type*}

noncomputable def gridIndex (b : ℝ) (x : I → ℝ) : I → ℤ := fun i => ⌈x i / b⌉ - 1

lemma gridIndex_of_mem {b : ℝ} (hb : 0 < b) {k : I → ℤ} {x : I → ℝ}
    (hx : x ∈ gridBox b k) : gridIndex b x = k := by
  funext i
  have hi := Set.mem_univ_pi.mp hx i
  have hceil : ⌈x i / b⌉ = k i + 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · push_cast
      have h : (k i : ℝ) < x i / b := (lt_div_iff₀ hb).mpr (by nlinarith [hi.1])
      linarith
    · push_cast
      exact (div_le_iff₀ hb).mpr (by nlinarith [hi.2])
  simp only [gridIndex, hceil]
  omega

lemma mem_gridBox_index {b : ℝ} (hb : 0 < b) (x : I → ℝ) :
    x ∈ gridBox b (gridIndex b x) := by
  rw [gridBox, Set.mem_univ_pi]
  intro i
  have hL := Int.ceil_lt_add_one (x i / b)
  have hU := Int.le_ceil (x i / b)
  constructor
  · have h : (⌈x i/b⌉ : ℝ)-1 < x i/b := by linarith
    have hh := (lt_div_iff₀ hb).mp h
    simp only [gridIndex, Int.cast_sub, Int.cast_one]
    nlinarith
  · have hh := (div_le_iff₀ hb).mp hU
    simp only [gridIndex, Int.cast_sub, Int.cast_one]
    nlinarith

lemma gridIndex_measurable (b : ℝ) : Measurable (gridIndex b : (I → ℝ) → I → ℤ) := by
  apply Measurable.of_eval
  intro i
  have hi : Measurable (fun x : I → ℝ => x i / b) :=
    (measurable_pi_apply (X := fun _ : I => ℝ) i).div_const b
  have hc : Measurable (fun x : I → ℝ => ⌈x i / b⌉) := Int.measurable_ceil.comp hi
  exact hc.sub_const (1 : ℤ)

variable [Fintype I]

lemma gridBox_hasSum_weighted {b : ℝ} (hb : 0 < b) (F : (I → ℤ) → ℝ)
    {C : ℝ} (hF : ∀ k, ‖F k‖ ≤ C) {f : (I → ℝ) → ℝ} (hf : Integrable f) :
    HasSum (fun k => F k * ∫ x in gridBox b k, f x)
      (∫ x, F (gridIndex b x) * f x) := by
  have hfm : AEStronglyMeasurable (fun x : I → ℝ => F (gridIndex b x)) volume :=
    ((measurable_of_countable F).comp (gridIndex_measurable b)).aestronglyMeasurable
  have hi := hf.bdd_mul hfm (Filter.Eventually.of_forall (fun x => hF (gridIndex b x)))
  have H := hasSum_integral_iUnion (gridBox_measurable b) (gridBox_disjoint hb)
    (hi.integrableOn (s := ⋃ k, gridBox b k))
  rw [gridBox_iUnion hb, Measure.restrict_univ] at H
  apply H.congr_fun
  intro k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (gridBox_measurable b k)] with x hx
  rw [gridIndex_of_mem hb hx]

end GridIndex

lemma grid_leading_expectation {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    (∑' k : GridAssignment n,
      gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) =
    ∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
      gridLeadingCount (gridIndex b x) * ‖ψ.value s (WithLp.toLp 2 x)‖^2 := by
  have Hs (s : Spins n) := gridBox_hasSum_weighted hb
    (gridLeadingCount (n := n))
    (fun k => by
      change ‖groupLeadingCount _‖ ≤ (n : ℝ)^(5/3 : ℝ)
      rw [Real.norm_of_nonneg (groupLeadingCount_nonneg _)]
      exact groupLeadingCount_le _)
    (((ψ.value_L2 s).comp_measurePreserving
      (PiLp.volume_preserving_toLp (Fin n × Fin 3))).integrable_norm_pow (p := 2) (by decide))
  simp only [gridBox_integral_eq_cube, Function.comp_apply, WithLp.toLp_add] at Hs
  have H := hasSum_sum (fun s (_ : s ∈ (Finset.univ : Finset (Spins n))) => Hs s)
  convert H.tsum_eq using 1
  congr 1
  funext k
  unfold cubeMass H1Vector.translate gridShift
  rw [Finset.mul_sum]

lemma grid_count_expectation_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    (b⁻¹)^2 * thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        gridLeadingCount (gridIndex b x) * ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  rw [← grid_leading_expectation ψ hb]
  exact grid_kinetic_lower hn ψ hψ hb

lemma gridBox_volume {I : Type*} [Fintype I] (b : ℝ) (k : I → ℤ) :
    volume (gridBox b k) = ENNReal.ofReal b ^ Fintype.card I := by
  simp only [gridBox, volume_pi, Measure.pi_pi, Real.volume_Ioc]
  have he (i : I) : b*((k i : ℝ)+1) - b*(k i : ℝ) = b := by ring
  simp only [he, Finset.prod_const, Finset.card_univ]

lemma sum_indicator_rpow_disjoint {I X : Type*} [Fintype I]
    (s : I → Set X) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (w : I → ℝ) {p : ℝ} (hp : p ≠ 0) (x : X) :
    (∑ i, (s i).indicator (fun _ => w i) x)^p =
      ∑ i, (s i).indicator (fun _ => (w i)^p) x := by
  classical
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i,hi⟩ := hx
    have he (u : I → ℝ) : ∑ j, (s j).indicator (fun _ => u j) x = u i := by
      rw [Finset.sum_eq_single i]
      · exact Set.indicator_of_mem hi _
      · intro j _ hji
        exact Set.indicator_of_notMem (Set.disjoint_left.mp (hs hji.symm) hi) _
      · simp
    rw [he w, he (fun i => (w i)^p)]
  · have hn (i : I) : x ∉ s i := fun hi => hx ⟨i,hi⟩
    simp only [Set.indicator_of_notMem (hn _), Finset.sum_const_zero, Real.zero_rpow hp]

noncomputable def gridCellDensity {n : ℕ} (b : ℝ) (k : GridAssignment n)
    (y : Fin 3 → ℝ) : ℝ :=
  ∑ c : Set.range (gridCell k), (gridBox b c.val).indicator
    (fun _ => (b⁻¹)^3 *
      (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)) y

lemma cell_power_scaling {b : ℝ} (hb : 0 < b) {m : ℝ} (hm : 0 ≤ m) :
    b^3 * ((b⁻¹)^3*m)^(5/3 : ℝ) = (b⁻¹)^2*m^(5/3 : ℝ) := by
  have he : ((b⁻¹)^3)^(5/3 : ℝ) = (b⁻¹)^5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hb.le)]
    norm_num
  rw [Real.mul_rpow (by positivity) hm, he]
  field_simp

lemma gridCellDensity_power_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (k : GridAssignment n) :
    (∫ y : Fin 3 → ℝ, gridCellDensity b k y ^ (5/3 : ℝ)) =
      (b⁻¹)^2 * gridLeadingCount k := by
  let w : Set.range (gridCell k) → ℝ := fun c => (b⁻¹)^3 *
    (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)
  have hd : Pairwise (fun c d : Set.range (gridCell k) =>
      Disjoint (gridBox b c.val) (gridBox b d.val)) := by
    intro c d hcd
    exact gridBox_disjoint hb (fun he => hcd (Subtype.ext he))
  have hi (c : Set.range (gridCell k)) :
      Integrable ((gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ))) :=
    (integrableOn_const (by rw [gridBox_volume]; finiteness)).integrable_indicator
      (gridBox_measurable b c.val)
  have he (c : Set.range (gridCell k)) :
      (∫ y, (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y) =
        (b⁻¹)^2 *
          (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ) ^
            (5/3 : ℝ) := by
    rw [integral_indicator (gridBox_measurable b c.val), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, gridBox_volume,
      Fintype.card_fin, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb.le, smul_eq_mul]
    exact cell_power_scaling hb (Nat.cast_nonneg _)
  calc
    _ = ∫ y, ∑ c : Set.range (gridCell k),
        (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y =>
        sum_indicator_rpow_disjoint (fun c : Set.range (gridCell k) => gridBox b c.val)
          hd w (by norm_num) y)
    _ = ∑ c : Set.range (gridCell k), ∫ y,
        (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y :=
      integral_finsetSum _ (fun c _ => hi c)
    _ = _ := by
      simp_rw [he]
      rw [← Finset.mul_sum]
      rfl

noncomputable def sameCell1 (b x y : ℝ) : ℝ := if ⌈x/b⌉ = ⌈y/b⌉ then 1 else 0

lemma sameCell1_nonneg (b x y : ℝ) : 0 ≤ sameCell1 b x y := by
  unfold sameCell1
  split <;> norm_num

lemma sameCell1_le_one (b x y : ℝ) : sameCell1 b x y ≤ 1 := by
  unfold sameCell1
  split <;> norm_num

lemma sameCell1_periodic {b : ℝ} (hb : b ≠ 0) (x y : ℝ) :
    Function.Periodic (fun t => sameCell1 b (x+t) (y+t)) b := by
  intro t
  have hx : (x+(t+b))/b = (x+t)/b+1 := by field_simp; ring
  have hy : (y+(t+b))/b = (y+t)/b+1 := by field_simp; ring
  simp only [sameCell1, hx, hy, Int.ceil_add_one, add_left_inj]

lemma sameCell1_measurable (b x y : ℝ) :
    Measurable (fun t => sameCell1 b (x+t) (y+t)) := by
  have hx : Measurable (fun t : ℝ => ⌈(x+t)/b⌉) :=
    Int.measurable_ceil.comp ((measurable_const.add measurable_id).div_const b)
  have hy : Measurable (fun t : ℝ => ⌈(y+t)/b⌉) :=
    Int.measurable_ceil.comp ((measurable_const.add measurable_id).div_const b)
  exact measurable_const.ite (measurableSet_eq_fun hx hy) measurable_const

lemma sameCell1_Ioc {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : u ∈ Ioc 0 b) (d : ℝ) :
    sameCell1 b u (d+u) = (Ioc 0 b).indicator (fun _ => (1 : ℝ)) (d+u) := by
  have hc : ⌈u/b⌉ = 1 := Int.ceil_eq_iff.mpr (by
    norm_num
    exact ⟨div_pos hu.1 hb, (div_le_one hb).mpr hu.2⟩)
  have hd : ⌈(d+u)/b⌉ = 1 ↔ d+u ∈ Ioc 0 b := by
    rw [Int.ceil_eq_iff]
    norm_num
    exact and_congr (by simpa only [zero_mul] using (lt_div_iff₀ hb : 0 < (d+u)/b ↔ 0*b < d+u)) (div_le_one hb)
  simp only [sameCell1, hc, eq_comm (a := (1 : ℤ)), hd, Set.indicator]

lemma sameCell1_integral_zero {b : ℝ} (hb : 0 < b) (d : ℝ) :
    (∫ u in Ioc 0 b, sameCell1 b u (d+u)) = max 0 (b-|d|) := by
  have he : (∫ u in Ioc 0 b, sameCell1 b u (d+u)) =
      ∫ u in Ioc 0 b ∩ Ioc (-d) (b-d), (1 : ℝ) := by
    calc
      _ = ∫ u in Ioc 0 b, (Ioc (-d) (b-d)).indicator (fun _ => (1 : ℝ)) u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [sameCell1_Ioc hb hu]
        have hi : d+u ∈ Ioc 0 b ↔ u ∈ Ioc (-d) (b-d) := by
          constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
        simp only [Set.indicator, hi]
      _ = _ := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          Set.inter_comm]
  rw [he, Set.Ioc_inter_Ioc, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal', smul_eq_mul, mul_one]
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd, max_eq_left (neg_nonpos.mpr hd),
      min_eq_right (by linarith : b-d ≤ b), sub_zero, max_comm]
  · rw [abs_of_nonpos hd, max_eq_right (neg_nonneg.mpr hd),
      min_eq_left (by linarith : b ≤ b-d), max_comm]

lemma sameCell1_integral {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    (∫ t in Ioc 0 b, sameCell1 b (x+t) (y+t)) = max 0 (b-|y-x|) := by
  have hP := (sameCell1_periodic hb.ne' x y).intervalIntegral_add_eq 0 (-x)
  simp only [zero_add, intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_of_le (show -x ≤ -x+b by linarith)] at hP
  rw [hP]
  have hA := intervalIntegral.integral_comp_add_left
    (fun u => sameCell1 b u (y-x+u)) x (a := -x) (b := -x+b)
  simp only [add_neg_cancel, add_neg_cancel_left,
    intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_of_le (show -x ≤ -x+b by linarith)] at hA
  convert sameCell1_integral_zero hb (y-x) using 1
  rw [← hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [show y-x+(x+t) = y+t by ring])

noncomputable def sameGridCell (b : ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  ∏ j, sameCell1 b (x j) (y j)

noncomputable def flatFineKernel (b : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (b⁻¹)^6 * ∏ j, max 0 (b-|x j|)

lemma sameGridCell_integral {b : ℝ} (hb : 0 < b) (x y : Fin 3 → ℝ) :
    (∫ t, sameGridCell b (x+t) (y+t) ∂finiteCubeMeasure b (Fin 3)) =
      ∏ j, max 0 (b-|y j-x j|) := by
  unfold sameGridCell finiteCubeMeasure
  have H := integral_fintype_prod_eq_prod
    (fun j u => sameCell1 b (x j+u) (y j+u))
    (μ := fun _ : Fin 3 => volume.restrict (Ioc 0 b))
  exact H.trans (by simp_rw [sameCell1_integral hb])

lemma sameGridCell_nonneg (b : ℝ) (x y : Fin 3 → ℝ) : 0 ≤ sameGridCell b x y :=
  Finset.prod_nonneg (fun j _ => sameCell1_nonneg b (x j) (y j))

lemma sameGridCell_le_one (b : ℝ) (x y : Fin 3 → ℝ) : sameGridCell b x y ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j _; exact sameCell1_nonneg b (x j) (y j)
  · intro j _; exact sameCell1_le_one b (x j) (y j)

lemma sameGridCell_measurable (b : ℝ) (x y : Fin 3 → ℝ) :
    Measurable (fun t => sameGridCell b (x+t) (y+t)) := by
  apply Finset.measurable_prod
  intro j _
  exact (sameCell1_measurable b (x j) (y j)).comp
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j)

lemma sameGridCell_integrable (b : ℝ) (x y : Fin 3 → ℝ) :
    Integrable (fun t => sameGridCell b (x+t) (y+t)) (finiteCubeMeasure b (Fin 3)) := by
  have : IsFiniteMeasure (finiteCubeMeasure b (Fin 3)) := by
    unfold finiteCubeMeasure
    infer_instance
  apply (integrable_const (1 : ℝ)).mono' (sameGridCell_measurable b x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_of_nonneg (sameGridCell_nonneg ..)]
    exact sameGridCell_le_one ..)

noncomputable def translatedGridDensity {n : ℕ} (b : ℝ) (t : Fin 3 → ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (b⁻¹)^3 * ∑ i : Fin n, sameGridCell b ((fun j => x (i,j))+t) (y+t)

lemma translatedGridDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    (b⁻¹)^3 * (∫ t, translatedGridDensity b t x y ∂finiteCubeMeasure b (Fin 3)) =
      ∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j))) := by
  unfold translatedGridDensity
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => sameGridCell_integrable ..)]
  simp_rw [sameGridCell_integral hb]
  rw [← mul_assoc, ← pow_add, Finset.mul_sum]
  rfl

lemma sameCell1_eq_ite (b x y : ℝ) :
    sameCell1 b x y = if ⌈x/b⌉-1 = ⌈y/b⌉-1 then 1 else 0 := by
  simp only [sameCell1, sub_left_inj]

lemma sameGridCell_eq_ite (b : ℝ) (x y : Fin 3 → ℝ) :
    sameGridCell b x y = if gridIndex b x = gridIndex b y then 1 else 0 := by
  classical
  by_cases he : gridIndex b x = gridIndex b y
  · rw [ite_eq_left he]
    have hj (j : Fin 3) : sameCell1 b (x j) (y j) = 1 := by
      rw [sameCell1_eq_ite]
      exact ite_eq_left (congrFun he j)
    simp only [sameGridCell, hj, Finset.prod_const_one]
  · rw [ite_eq_right he]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [sameCell1_eq_ite]
    exact ite_eq_right hj

lemma sum_fiber_weight {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (g : I → J) (w : J → ℝ) :
    (∑ j, (Fintype.card {i : I // g i = j} : ℝ) * w j) = ∑ i, w (g i) := by
  calc
    _ = ∑ j, ∑ i : {i : I // g i = j}, w (g i) := by
      apply Finset.sum_congr rfl
      intro j _
      have he : (fun i : {i : I // g i = j} => w (g i)) = fun _ => w j := by
        funext i
        rw [i.property]
      rw [he]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := Fintype.sum_fiberwise g (fun i => w (g i))

lemma gridCellDensity_sum_particles {n : ℕ} (b : ℝ) (k : GridAssignment n)
    (y : Fin 3 → ℝ) :
    gridCellDensity b k y = (b⁻¹)^3 *
      ∑ i : Fin n, (gridBox b (gridCell k i)).indicator (fun _ => (1 : ℝ)) y := by
  classical
  unfold gridCellDensity
  have he (c : Set.range (gridCell k)) :
      (gridBox b c.val).indicator
        (fun _ => (b⁻¹)^3 *
          (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)) y =
      (b⁻¹)^3 *
        ((Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ) *
          (gridBox b c.val).indicator (fun _ => (1 : ℝ)) y) := by
    by_cases hy : y ∈ gridBox b c.val
    · simp only [Set.indicator_of_mem hy, mul_one]
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum, sum_fiber_weight]
  rfl

lemma mem_gridBox_iff_index {I : Type*} {b : ℝ} (hb : 0 < b) (k : I → ℤ)
    (x : I → ℝ) : x ∈ gridBox b k ↔ gridIndex b x = k := by
  constructor
  · exact gridIndex_of_mem hb
  · intro he
    rw [← he]
    exact mem_gridBox_index hb x

lemma sameGridCell_eq_indicator {b : ℝ} (hb : 0 < b) (x y : Fin 3 → ℝ) :
    sameGridCell b x y = (gridBox b (gridIndex b x)).indicator (fun _ => (1 : ℝ)) y := by
  rw [sameGridCell_eq_ite]
  simp only [Set.indicator, mem_gridBox_iff_index hb, eq_comm]

lemma translatedGridDensity_eq_cell {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    translatedGridDensity b t x y =
      gridCellDensity b (gridIndex b (fun ij => x ij+t ij.2)) (y+t) := by
  rw [gridCellDensity_sum_particles]
  unfold translatedGridDensity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact sameGridCell_eq_indicator hb (fun j => x (i,j)+t j) (y+t)

lemma translatedGridDensity_power_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) :
    (∫ y : Fin 3 → ℝ, translatedGridDensity b t x y ^ (5/3 : ℝ)) =
      (b⁻¹)^2 * gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) := by
  simp_rw [translatedGridDensity_eq_cell hb]
  calc
    _ = ∫ y, gridCellDensity b (gridIndex b (fun ij => x ij+t ij.2)) y ^ (5/3 : ℝ) :=
      integral_add_right_eq_self _ t
    _ = _ := gridCellDensity_power_integral hb _

end Coulomb

end

end OAI
