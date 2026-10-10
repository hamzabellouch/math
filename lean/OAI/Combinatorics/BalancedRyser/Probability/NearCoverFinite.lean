import OAI.Combinatorics.BalancedRyser.Incidence.ProfileEmpiricalIncidence
import OAI.Combinatorics.BalancedRyser.Probability.NearCoverVisibility
import OAI.Combinatorics.BalancedRyser.Selection.ProfileOccupancy2

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal

namespace Balanced.NearCoverVisibility

theorem sum_le_tolerance_card_add_bad {α : Type*} [DecidableEq α]
    (C E : Finset α) (f : α → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hone : ∀ l ∈ C, f l ≤ 1)
    (hsmall : ∀ l ∈ C, l ∉ E → f l ≤ ε) :
    ∑ l ∈ C, f l ≤ ε * (C.card : ℝ) + (E.card : ℝ) := by
  have hp : ∀ l ∈ C, f l ≤ ε + if l ∈ E then 1 else 0 := by
    intro l hl
    by_cases he : l ∈ E
    · simp only [he, ↓reduceIte]
      linarith [hone l hl]
    · simpa only [he, ↓reduceIte, add_zero] using hsmall l hl he
  calc
    ∑ l ∈ C, f l ≤ ∑ l ∈ C, (ε + if l ∈ E then 1 else 0) :=
      Finset.sum_le_sum hp
    _ = ε * (C.card : ℝ) + ((C.filter fun l => l ∈ E).card : ℝ) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      ring
    _ ≤ ε * (C.card : ℝ) + (E.card : ℝ) := by
      gcongr
      exact fun l hl => (Finset.mem_filter.mp hl).2

theorem occupancy_deviation_le_one (k : ℕ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (l : Line F) :
    |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))| ≤ 1 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have ho : ((linePoints l ∩ uncoveredBy D).card : ℝ) /
      (Fintype.card F : ℝ) ≤ 1 := by
    apply (div_le_one hq).mpr
    exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left) |>.trans_eq
      (linePoints_card l))
  have hz : (0 : ℝ) ≤ ((linePoints l ∩ uncoveredBy D).card : ℝ) /
      (Fintype.card F : ℝ) := by positivity
  have hmu : Real.exp (-(k : ℝ)) ≤ 1 := by
    calc
      Real.exp (-(k : ℝ)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) k))
      _ = 1 := Real.exp_zero
  rw [abs_le]
  constructor <;> linarith [Real.exp_pos (-(k : ℝ))]

theorem empirical_absolute_row_deviation_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) (hDC : Disjoint D C) (hcard : C.card ≤ Fintype.card F)
    (hbad : ((exceptionalOccupancyLines k ε D).card : ℝ) ≤
      ε * (Fintype.card F : ℝ)) :
    (∫ x : Profile, |(∑' j : ℕ, x (0, j)) - Real.exp (-(k : ℝ))|
      ∂(empiricalProfileMeasure D C C : Measure Profile)) ≤ 2 * ε := by
  classical
  rw [FiniteProfile.empiricalProfileMeasure_integral]
  simp_rw [(FiniteProfile.lineProfile_zero_row_hasSum D C _).tsum_eq]
  let f : Line F → ℝ := fun l =>
    |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))|
  have hsum := sum_le_tolerance_card_add_bad C (exceptionalOccupancyLines k ε D)
    f hε (fun l _ => occupancy_deviation_le_one k D l) (by
      intro l hlC hlE
      apply le_of_lt
      apply lt_of_not_ge
      intro he
      apply hlE
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, he⟩
      intro hlD
      exact Finset.disjoint_left.mp hDC hlD hlC)
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcardR : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hcard
  have htotal : ε * (C.card : ℝ) + ((exceptionalOccupancyLines k ε D).card : ℝ) ≤
      2 * ε * (Fintype.card F : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hcardR hε]
  change (Fintype.card F : ℝ)⁻¹ * (∑ l ∈ C, f l) ≤ _
  calc
    _ ≤ (Fintype.card F : ℝ)⁻¹ * (2 * ε * (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum.trans htotal) (inv_nonneg.mpr hq.le)
    _ = 2 * ε := by field_simp

theorem nearCoverClass_integral_abs_tendsto
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hεnonneg : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => ∫ x : Profile,
      |(∑' j : ℕ, x (0, j)) - Real.exp (-(k : ℝ))|
      ∂(empiricalProfileMeasure (D n) (C n) (C n) : Measure Profile))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => empirical_absolute_row_deviation_le k (hεnonneg _) (D n) (C n)
      (hclass n).1.2.1 (hclass n).1.2.2 (hclass n).2.2.2.2)
  simpa using (hε.comp hq).const_mul 2

theorem empiricalMultiplicityMass_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) : empiricalMultiplicityMass D 0 =
      ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have heq : (Finset.univ.filter fun p : Point F => deletionMultiplicity D p = 0) =
      uncoveredBy D := by
    ext p
    simp [FiniteProfile.mem_uncoveredBy_iff]
  unfold empiricalMultiplicityMass
  rw [heq]

theorem core_density_error_le_twice_tv (k : ℕ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) :
    |((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 -
      Real.exp (-(k : ℝ))| ≤ 2 * deletionMultiplicityTV k D := by
  have hp : HasSum (deletionPoissonMass k) 1 := by
    unfold deletionPoissonMass
    simp only [ProbabilityTheory.poissonMeasure_real_singleton]
    exact ProbabilityTheory.hasSum_one_poissonMeasure (k : ℝ≥0)
  have hs := ((FiniteProfile.empirical_multiplicity_hasSum D).summable.sub hp.summable).abs
  have hzero : deletionPoissonMass k 0 = Real.exp (-(k : ℝ)) := by
    simp [deletionPoissonMass, ProbabilityTheory.poissonMeasure_real_singleton]
  have h := hs.le_tsum 0 (fun i _ => abs_nonneg (empiricalMultiplicityMass D i -
    deletionPoissonMass k i))
  rw [empiricalMultiplicityMass_zero, hzero] at h
  unfold deletionMultiplicityTV
  linarith

theorem nearCoverClass_sizeGap (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ q, ε q ≤ Real.exp (-(k : ℝ)) / 4) :
    ProfileClassSizeGap (Real.exp (-(k : ℝ)) / 2) (NearCoverClass k δ ε) := by
  intro F _ _ _ D C h
  right
  have herr := core_density_error_le_twice_tv k D
  have htv := h.2.2.2.1
  have hcap := FiniteProfile.core_cover_normalized_card_le D C h.2.1
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hdensity : Real.exp (-(k : ℝ)) / 2 ≤
      ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
    have hlower := (abs_le.mp herr).1
    linarith [hε (Fintype.card F)]
  exact (le_div_iff₀ hq).mp (hdensity.trans hcap)

theorem nearCoverClass_core_density_tendsto
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => ((uncoveredBy (D n)).card : ℝ) /
      (Fintype.card (F n) : ℝ) ^ 2) atTop (𝓝 (Real.exp (-(k : ℝ)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => 2 * ε (Fintype.card (F n))) atTop (𝓝 0) from
      by simpa using (hε.comp hq).const_mul 2)
  rw [Real.norm_eq_abs]
  exact (core_density_error_le_twice_tv k (D n)).trans
    (mul_le_mul_of_nonneg_left (hclass n).2.2.2.1 (by norm_num))

theorem nearCoverClass_limit_corner_budget
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : P (0, 0) = 0 ∧ c ≤ 1 := by
  constructor
  · have hcoord := hlim.2.1.apply_nhds (0, 0)
    have hz (n : ℕ) : planeProfile (D n) (C n) (0, 0) = 0 :=
      FiniteProfile.planeProfile_zero_zero_of_cover (D n) (C n) (hclass n).2.1
    simp only [hz] at hcoord
    exact tendsto_nhds_unique hcoord tendsto_const_nhds
  · apply le_of_tendsto hlim.1
    apply Eventually.of_forall
    intro n
    apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := F n))).mpr
    exact_mod_cast (hclass n).1.2.2

end Balanced.NearCoverVisibility

end

end OAI
