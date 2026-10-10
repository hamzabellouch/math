import OAI.Probability.GaussianPropeller.Analytic

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem integral_comp_neg {d : ℕ} (f : Space d → ℝ) (hf : AEStronglyMeasurable f (gaussian d)) :
    ∫ x, f (-x) ∂gaussian d = ∫ x, f x ∂gaussian d := by
  have hm : (gaussian d).map (fun x => -x) = gaussian d :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rw [← integral_map (by fun_prop) (hm.symm ▸ hf), hm]

theorem scoreMax_three {d : ℕ} (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v x = max ⟪v 0, x⟫ (max ⟪v 1, x⟫ ⟪v 2, x⟫) := by
  apply le_antisymm
  · apply (scoreMax_le_iff v x _).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact max_le (le_scoreMax v 0 x) (max_le (le_scoreMax v 1 x) (le_scoreMax v 2 x))

theorem three_range_identity (a b c : ℝ) :
    max a (max b c) + max (-a) (max (-b) (-c)) =
      (|a - b| + |a - c| + |b - c|) / 2 := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · simp [max_eq_right hbc, max_eq_right (hab.trans hbc),
        max_eq_left (neg_le_neg hbc), max_eq_left (neg_le_neg hab),
        abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hbc),
        abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc))]
      ring
    · rcases le_total a c with hac | hca
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_left (neg_le_neg hac),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hac),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
  · rcases le_total a c with hac | hca
    · simp [max_eq_right (hba.trans hac), max_eq_right hac,
        max_eq_left (neg_le_neg (hba.trans hac)), max_eq_right (neg_le_neg hba),
        abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonpos (sub_nonpos.mpr hac),
        abs_of_nonpos (sub_nonpos.mpr (hba.trans hac))]
      ring
    · rcases le_total b c with hbc | hcb
      · simp [max_eq_right hbc, max_eq_left hca,
          max_eq_left (neg_le_neg hbc), max_eq_right (neg_le_neg hba),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonpos (sub_nonpos.mpr hbc)]
        ring
      · simp [max_eq_left hcb, max_eq_left hba,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring

theorem width_three {d : ℕ} (v : Tuple d 3) :
    width v = (‖v.ofLp 0 - v.ofLp 1‖ + ‖v.ofLp 0 - v.ofLp 2‖ +
      ‖v.ofLp 1 - v.ofLp 2‖) / (2 * Real.sqrt (2 * Real.pi)) := by
  have he (x : Space d) : scoreMax v.ofLp x + scoreMax v.ofLp (-x) =
      (|⟪v.ofLp 0 - v.ofLp 1, x⟫| + |⟪v.ofLp 0 - v.ofLp 2, x⟫| +
        |⟪v.ofLp 1 - v.ofLp 2, x⟫|) / 2 := by
    simp only [scoreMax_three, inner_neg_right, inner_sub_left]
    exact three_range_identity _ _ _
  have hi (w : Space d) : Integrable (fun x => |⟪w, x⟫|) (gaussian d) :=
    ((integrable_id_gaussian d).const_inner w).abs
  have hneg : Integrable (fun x => scoreMax v.ofLp (-x)) (gaussian d) := by
    convert integrable_scoreMax (-v) using 1
    ext x
    simp only [scoreMax_three, PiLp.neg_apply, inner_neg_left, inner_neg_right]
  have h := integral_congr_ae (μ := gaussian d) (Filter.Eventually.of_forall he)
  rw [integral_add (integrable_scoreMax v) hneg,
    integral_comp_neg _ (integrable_scoreMax v).aestronglyMeasurable,
    integral_div] at h
  rw [integral_add (f := fun x => |⟪v.ofLp 0 - v.ofLp 1, x⟫| +
      |⟪v.ofLp 0 - v.ofLp 2, x⟫|) (g := fun x => |⟪v.ofLp 1 - v.ofLp 2, x⟫|)
      ((hi _).add (hi _)) (hi _), integral_add (hi _) (hi _)] at h
  simp_rw [gaussian, Analytic.integral_abs_inner_stdGaussian] at h
  change width v + width v = _ at h
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp [hs] at h ⊢
  nlinarith only [h]

theorem perimeter_sq_le {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      9 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
  have hcs : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      3 * (‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2) := by
    nlinarith [sq_nonneg (‖a-b‖ - ‖a-c‖), sq_nonneg (‖a-b‖ - ‖b-c‖),
      sq_nonneg (‖a-c‖ - ‖b-c‖)]
  have hid : ‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2 =
      3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) - ‖a+b+c‖^2 := by
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
    ring
  rw [hid] at hcs
  nlinarith [sq_nonneg ‖a+b+c‖]

theorem width_three_sq_le {d : ℕ} (v : Tuple d 3) :
    (width v)^2 ≤ (9 / (8 * Real.pi)) * ‖v‖^2 := by
  have hp := perimeter_sq_le (v.ofLp 0) (v.ofLp 1) (v.ofLp 2)
  have hnorm : ‖v‖^2 = ‖v.ofLp 0‖^2 + ‖v.ofLp 1‖^2 + ‖v.ofLp 2‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rw [← hnorm] at hp
  rw [width_three, div_pow]
  have hs : (2 * Real.sqrt (2 * Real.pi))^2 = 8 * Real.pi := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
  calc
    _ ≤ 9 * ‖v‖^2 := hp
    _ = 9 / (8 * Real.pi) * ‖v‖^2 * (8 * Real.pi) := by
      field_simp

theorem three_partition_bound {d : ℕ} {A : Fin 3 → Set (Space d)} (hA : IsPartition A) :
    value A ≤ 9 / (8 * Real.pi) := by
  have hpair : value A ≤ width (moments A) := by
    simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using
      pairing_le_width hA (moments A)
  have hsq := width_three_sq_le (moments A)
  rw [norm_moments_sq] at hsq
  have hn := value_nonneg A
  have hw : 0 ≤ width (moments A) := hn.trans hpair
  have hval := (sq_le_sq₀ hn hw).mpr hpair
  have hB : (0 : ℝ) < 9 / (8 * Real.pi) := by positivity
  nlinarith

theorem centroid_congr_ae {d : ℕ} {A B : Set (Space d)}
    (h : A =ᵐ[gaussian d] B) : centroid A = centroid B := by
  exact setIntegral_congr_set h

theorem value_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : value A = value B := by
  apply Finset.sum_congr rfl
  intro i _
  rw [centroid_congr_ae (h i)]

theorem partition_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (hA : IsPartition A) (hB : ∀ i, MeasurableSet (B i))
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : IsPartition B := by
  refine ⟨hB, ?_⟩
  have hh := ae_all_iff.mpr h
  filter_upwards [hA.2, hh] with x hx heq
  change ∀ i, (x ∈ A i) = (x ∈ B i) at heq
  obtain ⟨i, hi, hu⟩ := hx
  exact ⟨i, Eq.mp (heq i) hi, fun j hj => hu j (Eq.mpr (heq j) hj)⟩

theorem closedCell_eq_scoreCell_ae {d k : ℕ} (v : Fin k → Space d)
    (hv : Function.Injective v) (i : Fin k) :
    closedCell v i =ᵐ[gaussian d] scoreCell v i := by
  have ht (j : Fin k) (hij : i ≠ j) : ∀ᵐ x ∂gaussian d, ⟪v i, x⟫ ≠ ⟪v j, x⟫ := by
    rw [ae_iff]
    simpa only [not_not, inner_sub_left, sub_eq_zero] using
      gaussian_hyperplane_null (v i - v j) (sub_ne_zero.mpr (hv.ne hij)) 0
  have ht' := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun hij => ht j hij))
  filter_upwards [ht'] with x hx
  apply propext
  constructor
  · intro hc
    refine ⟨hc, fun j hji => ?_⟩
    exact lt_of_le_of_ne (hc j) (Ne.symm (hx j (ne_of_gt hji)))
  · exact fun hc => hc.1

noncomputable def axis0 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨0, by omega⟩ 1
noncomputable def axis1 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨1, by omega⟩ 1

noncomputable def sectorScores (d : ℕ) (hd : 2 ≤ d) : Tuple d 3 :=
  WithLp.toLp 2 ![(2 * Real.sqrt 3) • axis0 d hd,
    (-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd,
    (-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd]

theorem axis_inner (d : ℕ) (hd : 2 ≤ d) :
    ⟪axis0 d hd, axis0 d hd⟫ = 1 ∧ ⟪axis1 d hd, axis1 d hd⟫ = 1 ∧
      ⟪axis0 d hd, axis1 d hd⟫ = 0 ∧ ⟪axis1 d hd, axis0 d hd⟫ = 0 := by
  simp [axis0, axis1, EuclideanSpace.inner_single_left]

theorem sectorScores_scores (d : ℕ) (hd : 2 ≤ d) (x : Space d) :
    ⟪(sectorScores d hd).ofLp 0, x⟫ = 2 * Real.sqrt 3 * coord 0 x ∧
    ⟪(sectorScores d hd).ofLp 1, x⟫ = -Real.sqrt 3 * coord 0 x + 3 * coord 1 x ∧
    ⟪(sectorScores d hd).ofLp 2, x⟫ = -Real.sqrt 3 * coord 0 x - 3 * coord 1 x := by
  simp [sectorScores, axis0, axis1, coord, show 0 < d by omega, show 1 < d by omega,
    inner_add_left, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]

theorem sectorScores_closed (d : ℕ) (hd : 2 ≤ d) (i : Fin 3) :
    closedCell (sectorScores d hd).ofLp i = propeller d 3 i := by
  ext x
  obtain ⟨h0, h1, h2⟩ := sectorScores_scores d hd x
  fin_cases i <;>
    simp [closedCell, propeller, Fin.forall_fin_succ, h0, h1, h2, abs_le] <;>
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

theorem sectorScores_norms (d : ℕ) (hd : 2 ≤ d) :
    ‖sectorScores d hd‖^2 = 36 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 1‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 2‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 1 - (sectorScores d hd).ofLp 2‖ = 6 := by
  obtain ⟨h00, h11, h01, h10⟩ := axis_inner d hd
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn (x : Space d) : ‖x‖^2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
  constructor
  · rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    change ‖(2 * Real.sqrt 3) • axis0 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd‖^2 = 36
    simp only [hn, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      h00, h01, h10, h11, starRingEnd_apply, star_trivial]
    nlinarith only [hs]
  · have hsq (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖^2 = 36 := by
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals dsimp [sectorScores]
      all_goals simp only [hn, inner_smul_left, inner_smul_right,
        inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        h00, h01, h10, h11, starRingEnd_apply, star_trivial]
      all_goals nlinarith only [hs]
    have he (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 6 := by
      nlinarith [hsq i j hij, norm_nonneg ((sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j)]
    exact ⟨he 0 1 (by decide), he 0 2 (by decide), he 1 2 (by decide)⟩

theorem sectorScores_injective (d : ℕ) (hd : 2 ≤ d) :
    Function.Injective (sectorScores d hd).ofLp := by
  obtain ⟨_, h01, h02, h12⟩ := sectorScores_norms d hd
  intro i j hij
  have hz : ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 0 := by
    rw [hij, sub_self, norm_zero]
  fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]

theorem propeller_three (d : ℕ) (hd : 2 ≤ d) :
    IsPartition (propeller d 3) ∧ value (propeller d 3) = 9 / (8 * Real.pi) := by
  let v := sectorScores d hd
  have he (i : Fin 3) : propeller d 3 i =ᵐ[gaussian d] scoreCell v.ofLp i := by
    rw [← sectorScores_closed d hd i]
    exact closedCell_eq_scoreCell_ae v.ofLp (sectorScores_injective d hd) i
  have hp : IsPartition (propeller d 3) :=
    partition_congr_ae (scoreCell_partition v.ofLp)
      (fun i => by rw [← sectorScores_closed d hd i]; exact measurableSet_closedCell _ i)
      (fun i => (he i).symm)
  refine ⟨hp, le_antisymm (three_partition_bound hp) ?_⟩
  rw [value_congr_ae he]
  obtain ⟨hv, h01, h02, h12⟩ := sectorScores_norms d hd
  have hw : (width v)^2 = 36 * (9 / (8 * Real.pi)) := by
    rw [width_three, h01, h02, h12, div_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    field_simp; ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) v (moments (scoreCell v.ofLp))
  rw [pairing_scoreCell, Real.norm_eq_abs] at hcs
  have hs := (sq_le_sq₀ (abs_nonneg (width v))
    (mul_nonneg (norm_nonneg v) (norm_nonneg (moments (scoreCell v.ofLp))))).mpr hcs
  rw [sq_abs, mul_pow, norm_moments_sq, hw] at hs
  change 36 * (9 / (8 * Real.pi)) ≤ ‖sectorScores d hd‖^2 * _ at hs
  rw [hv] at hs
  linarith only [hs]

theorem append_empty_partition {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : IsPartition (Fin.lastCases ∅ A) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using (MeasurableSet.empty : MeasurableSet (∅ : Set (Space d)))
    · simpa only [Fin.lastCases_castSucc] using hA.1 j
  · filter_upwards [hA.2] with x hx
    obtain ⟨i, hi, hu⟩ := hx
    refine ⟨i.castSucc, ?_, ?_⟩
    · simpa only [Fin.lastCases_castSucc] using hi
    · intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [Fin.lastCases_last, Set.mem_empty_iff_false, false_implies]
      · intro hj
        exact congrArg Fin.castSucc (hu l (by simpa only [Fin.lastCases_castSucc] using hj))

theorem append_empty_value {d k : ℕ} (A : Fin k → Set (Space d)) :
    value (Fin.lastCases ∅ A) = value A := by
  simp [value, Fin.sum_univ_castSucc]

theorem propeller_succ (d k : ℕ) (hk : 3 ≤ k) :
    propeller d (k+1) = Fin.lastCases ∅ (propeller d k) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [propeller, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  · simp [propeller]

theorem propeller_attainment (d k : ℕ) (hd : 2 ≤ d) (hk : 3 ≤ k) :
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi) := by
  induction k, hk using Nat.le_induction with
  | base => exact propeller_three d hd
  | succ k hk ih =>
    rw [propeller_succ d k hk]
    exact ⟨append_empty_partition ih.1, (append_empty_value _).trans ih.2⟩

theorem centroid_norm_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖ ≤ 1 / Real.sqrt (2 * Real.pi) := by
  let z := centroid A
  let f : Space d → ℝ := fun x => ⟪z, x⟫
  have hi : Integrable f (gaussian d) := (integrable_id_gaussian d).const_inner z
  have he : ∫ x, (A.indicator f) x ∂gaussian d = ‖z‖^2 := by
    rw [integral_indicator hA]
    change (∫ x in A, ⟪z, x⟫ ∂gaussian d) = _
    rw [integral_inner (integrable_id_restrict d A)]
    exact real_inner_self_eq_norm_sq z
  have hz : ∫ x, f x ∂gaussian d = 0 := by
    change (∫ x, ⟪z, x⟫ ∂gaussian d) = 0
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  have hab : ∫ x, |f x| ∂gaussian d = ‖z‖ * (2 / Real.sqrt (2 * Real.pi)) :=
    Analytic.integral_abs_inner_stdGaussian z
  have hp (x : Space d) : A.indicator f x ≤ (|f x| + f x) / 2 := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      linarith only [le_abs_self (f x)]
    · rw [Set.indicator_of_notMem hx]
      linarith only [neg_abs_le (f x)]
  have h := integral_mono_ae (hi.indicator hA) ((hi.abs.add hi).div_const 2)
    (Filter.Eventually.of_forall hp)
  rw [he, integral_div] at h
  change ‖z‖^2 ≤ (∫ x, |f x| + f x ∂gaussian d) / 2 at h
  rw [integral_add hi.abs hi, hab, hz, add_zero] at h
  have hn := norm_nonneg z
  have hq : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
  have hn' : ‖z‖^2 ≤ (1 / Real.sqrt (2 * Real.pi)) * ‖z‖ := by
    convert h using 1; ring
  nlinarith only [hn, hq, hn']

theorem centroid_norm_sq_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    ‖centroid A‖^2 ≤ 1 / (2 * Real.pi) := by
  have h := (sq_le_sq₀ (norm_nonneg (centroid A)) (by positivity :
      0 ≤ 1 / Real.sqrt (2 * Real.pi))).mpr (centroid_norm_le hA)
  simpa only [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)] using h

theorem normalized_centroid_lt_two_thirds {d : ℕ} {A : Set (Space d)}
    (hA : MeasurableSet A) {C : ℝ} (hC : 9 / (8 * Real.pi) < C) :
    ‖centroid A‖ / Real.sqrt C < 2 / 3 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hCp : 0 < C := (by positivity : (0 : ℝ) < 9 / (8 * Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hn := centroid_norm_sq_le hA
  have hC' : 9 < C * (8 * Real.pi) := (div_lt_iff₀ (by positivity)).mp hC
  have hn' : ‖centroid A‖^2 * (2 * Real.pi) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hn
  have hsq : 9 * ‖centroid A‖^2 < 4 * C := by nlinarith only [hC', hn', hp]
  apply (div_lt_iff₀ ht).mpr
  have ht2 := Real.sq_sqrt hCp.le
  have hz := norm_nonneg (centroid A)
  nlinarith only [hsq, ht2, hz, ht]

end GaussianPropeller.Reduction

namespace GaussianPropeller

theorem main_attainment : MainAttainment := by
  intro n hn
  exact Reduction.propeller_attainment n (n+1) (by omega) (by omega)

end GaussianPropeller

end OAI
