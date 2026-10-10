import Mathlib
import OAI.Probability.Ballisticity.Geometry.CoordinateStrip

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma quenched_stayUntil_ball_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) :
    quenchedKernel (ω, x) (StayUntil S n) = quenchedKernel (η, x) (StayUntil S n) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = StayUntil S n := by
    ext X
    exact ⟨fun h i hi => h ⟨i, Finset.mem_Iic.mpr hi⟩,
      fun h i => h i (Finset.mem_Iic.mp i.2)⟩
  rw [← hC]
  exact quenched_prefix_locality ω η x n hωη C

lemma noDropFinite_measurable_ball {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    @Measurable _ _ (rowSigma (LatticeBall x n)) _ (noDropFinite ℓ x n) := by
  apply measurable_of_row_locality _ (noDropFinite_measurable ℓ x n) _ x
    (by simp [LatticeBall])
  intro ω η h
  exact quenched_stayUntil_ball_locality ω η x _ n h

lemma noDropFinite_translation {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (n : ℕ) :
    noDropFinite ℓ x n ω = noDropFinite ℓ 0 n (fun a => ω (x + a)) := by
  let S : Set (Lattice d) := {y | dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition y) ℓ}
  have hm : Measurable (fun X : Path d => fun j => X j - x) := by fun_prop
  have h := congrArg (fun μ : Measure (Path d) => μ (StayUntil S n))
    (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_stayUntil S n)] at h
  have he : (fun X : Path d => fun j => X j - x) ⁻¹' StayUntil S n =
      StayUntil {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} n := by
    ext X
    simp only [StayUntil, S, Set.mem_preimage, Set.mem_ofPred_eq, dot_realPosition_sub]
    simp only [dot, realPosition, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    constructor <;> intro h j hj <;> have hh := h j hj <;> linarith
  simpa only [he, add_zero, noDropFinite] using h

lemma noDropQuenched_le_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (n : ℕ) : noDropQuenched ℓ x ω ≤ noDropFinite ℓ x n ω :=
  measure_mono (fun _ h i _ => h i)

lemma noDropFinite_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    Tendsto (fun n => noDropFinite ℓ x n ω) atTop (𝓝 (noDropQuenched ℓ x ω)) := by
  let S : Set (Lattice d) := {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ}
  have he : (⋂ n, StayUntil S n) = NoDrop ℓ x := by
    ext X
    exact ⟨fun h i => Set.mem_iInter.mp h i i le_rfl,
      fun h => Set.mem_iInter.mpr fun _ i _ => h i⟩
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun n => StayUntil S n)
    (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    (fun _ _ hmn _ h j hj => h j (hj.trans hmn)) ⟨0, measure_ne_top _ _⟩
  simpa only [he, Function.comp_def, noDropFinite, noDropQuenched] using h

noncomputable def clippedInverse (δ lam : ℝ) (q : ℝ≥0∞) : ℝ :=
  (max q.toReal δ) ^ (-lam)

lemma clippedInverse_measurable (δ lam : ℝ) : Measurable (clippedInverse δ lam) :=
  (measurable_id.ennreal_toReal.max measurable_const).pow_const _

lemma clippedInverse_bounds (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (q : ℝ≥0∞) : 0 ≤ clippedInverse δ lam q ∧ clippedInverse δ lam q ≤ δ ^ (-lam) := by
  exact ⟨Real.rpow_nonneg (hδ.le.trans (le_max_right _ _)) _,
    Real.rpow_le_rpow_of_nonpos hδ (le_max_right _ _) (neg_nonpos.mpr hlam)⟩

lemma clippedInverse_antitone {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    {q r : ℝ≥0∞} (hr : r ≠ ∞) (hqr : q ≤ r) :
    clippedInverse δ lam r ≤ clippedInverse δ lam q := by
  apply Real.rpow_le_rpow_of_nonpos (hδ.trans_le (le_max_right _ _))
    (max_le_max (ENNReal.toReal_mono hr hqr) le_rfl) (neg_nonpos.mpr hlam)

lemma clippedInverse_tendsto {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    {q : ℝ≥0∞} (hq : q ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (lam : ℝ)
    (hf : Tendsto f l (𝓝 q)) :
    Tendsto (fun a => clippedInverse δ lam (f a)) l (𝓝 (clippedInverse δ lam q)) :=
  (((ENNReal.tendsto_toReal hq).comp hf).max tendsto_const_nhds).rpow_const
    (Or.inl (ne_of_gt (hδ.trans_le (le_max_right _ _))))

lemma noDrop_clipped_inverse_L1 {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Tendsto (fun n => ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω)| ∂environmentLaw ν) atTop (𝓝 0) := by
  have hm (n : ℕ) := ((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ x)).sub
    ((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ x n))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := environmentLaw ν) (f := fun _ => (0 : ℝ))
    (fun _ => δ ^ (-lam)) (fun n => (hm n).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) (Filter.Eventually.of_forall fun ω => ?_)
  · simpa using ht
  · exact Filter.Eventually.of_forall fun ω => by
      have hq := clippedInverse_bounds lam hδ hlam (noDropQuenched ℓ x ω)
      have hn := clippedInverse_bounds lam hδ hlam (noDropFinite ℓ x n ω)
      have hle := clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ x ω n)
      change clippedInverse δ lam (noDropFinite ℓ x n ω) ≤
        clippedInverse δ lam (noDropQuenched ℓ x ω) at hle
      simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply, Function.comp_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith
  · have h := clippedInverse_tendsto (measure_ne_top _ _) hδ lam (noDropFinite_tendsto ℓ x ω)
    simpa only [noDropQuenched, sub_self, abs_zero, Pi.sub_apply, Function.comp_apply] using
      ((tendsto_const_nhds (x := clippedInverse δ lam (noDropQuenched ℓ x ω))).sub h).abs

lemma fresh_rows_prod {d : ℕ} {ι : Type*} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (s : Finset ι) (S : ι → Set (Lattice d)) (f : ι → Environment d → ℝ)
    (hS : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)))
    (hf : ∀ i ∈ s, @Measurable _ _ (rowSigma (S i)) _ (f i)) :
    (∫ ω, ∏ i ∈ s, f i ω ∂environmentLaw ν) =
      ∏ i ∈ s, ∫ ω, f i ω ∂environmentLaw ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)) :=
      hS.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
    have hm : @Measurable _ _ (rowSigma (⋃ i ∈ s, S i)) _
        (fun ω => ∏ i ∈ s, f i ω) := by
      apply Finset.measurable_fun_prod
      intro i hi
      exact (hf i (Finset.mem_insert_of_mem hi)).mono
        (rowSigma_mono (Set.subset_iUnion₂_of_subset i hi Set.Subset.rfl)) le_rfl
    have hd : Disjoint (S a) (⋃ i ∈ s, S i) := by
      apply Set.disjoint_iUnion_right.mpr
      intro i
      apply Set.disjoint_iUnion_right.mpr
      intro hi
      exact hS (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    simp only [Finset.prod_insert ha]
    rw [fresh_rows_factor ν hd (hf a (Finset.mem_insert_self _ _)) hm,
      ih hp (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma nonneg_prod_le_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ B) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ B ^ s.card := by
  refine ⟨Finset.prod_nonneg (fun i hi => (hf i hi).1), ?_⟩
  simpa only [Finset.prod_const] using
    Finset.prod_le_prod₀ (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)

lemma prod_difference_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {B : ℝ}
    (hB : 1 ≤ B) (hf : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ f i ∧ f i ≤ B) :
    (∏ i ∈ s, f i) ≤ (∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hft i (hi : i ∈ s) := hf i (Finset.mem_insert_of_mem hi)
    have ih := ih hft
    have hP := nonneg_prod_le_const s g (fun i hi =>
      ⟨(hft i hi).1, (hft i hi).2.1.trans (hft i hi).2.2⟩)
    have hsum : 0 ≤ ∑ i ∈ s, (f i - g i) := by
      exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hft i hi).2.1
    have hdiff : 0 ≤ f a - g a := sub_nonneg.mpr hfa.2.1
    have hb : 0 ≤ B ^ s.card := pow_nonneg (zero_le_one.trans hB) _
    have hbn : B ^ s.card ≤ B ^ s.card * B :=
      le_mul_of_one_le_right hb hB
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      pow_succ]
    calc
      f a * (∏ i ∈ s, f i) ≤
          f a * ((∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i)) :=
        mul_le_mul_of_nonneg_left ih (hfa.1.trans hfa.2.1)
      _ = g a * (∏ i ∈ s, g i) + (f a - g a) * (∏ i ∈ s, g i) +
          f a * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by ring
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * B ^ s.card +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
        · exact hP.2
        · exact hfa.2.2
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * (B ^ s.card * B) +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
      _ = _ := by ring

lemma clipped_inverse_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropQuenched_translation ℓ ω x]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ 0)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma clipped_inverse_finite_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropFinite_translation ℓ ω x n]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ 0 n)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma integrable_of_nonneg_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ a, 0 ≤ f a ∧ f a ≤ B) : Integrable f μ := by
  exact (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb a).1] using (hb a).2)).integrable le_rfl

lemma clipped_inverse_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {f : Environment d → ℝ≥0∞} (hf : Measurable f) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Integrable (fun ω => clippedInverse δ lam (f ω)) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ ((clippedInverse_measurable δ lam).comp hf)
    (fun _ => clippedInverse_bounds lam hδ hlam _)

lemma clipped_inverse_integral_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
    ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
      clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν := by
  have hi y := clipped_inverse_integrable ν (measurable_noDropQuenched ℓ y) hδ hlam
  have hj y := clipped_inverse_integrable ν (noDropFinite_measurable ℓ y n) hδ hlam
  rw [integral_sub (hi x) (hj x), clipped_inverse_integral_translation,
    clipped_inverse_finite_integral_translation, ← integral_sub (hi 0) (hj 0)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => (abs_of_nonneg (sub_nonneg.mpr
    (clippedInverse_antitone hδ hlam (measure_ne_top _ _)
      (noDropQuenched_le_finite ℓ 0 ω n)))).symm

lemma separated_clipped_inverse_product {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) ∂environmentLaw ν) ≤
        (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ^ k + ε := by
  classical
  let B := max 1 (δ ^ (-lam))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hlim := (noDrop_clipped_inverse_L1 ν ℓ 0 hδ hlam).const_mul (B ^ k * (k : ℝ))
  simp only [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨n, fun x hx => ?_⟩
  let f : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropQuenched ℓ (x i) ω)
  let g : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropFinite ℓ (x i) n ω)
  have hf i : Measurable (f i) :=
    (clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ (x i))
  have hg i : Measurable (g i) :=
    (clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ (x i) n)
  have hfb i ω : 0 ≤ f i ω ∧ f i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgb i ω : 0 ≤ g i ω ∧ g i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgf i ω : g i ω ≤ f i ω := clippedInverse_antitone hδ hlam
    (measure_ne_top _ _) (noDropQuenched_le_finite ℓ (x i) ω n)
  have hfi i := integrable_of_nonneg_bound (environmentLaw ν) (hf i) (hfb i)
  have hgi i := integrable_of_nonneg_bound (environmentLaw ν) (hg i) (hgb i)
  have hfpi : Integrable (fun ω => ∏ i, f i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hf i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => f i ω)
          (fun i _ => hfb i ω))
  have hgpi : Integrable (fun ω => ∏ i, g i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hg i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => g i ω)
          (fun i _ => hgb i ω))
  have hsum : Integrable (fun ω => ∑ i, (f i ω - g i ω)) (environmentLaw ν) :=
    integrable_finsetSum _ (fun i _ => (hfi i).sub (hgi i))
  have hbd := integral_mono hfpi (hgpi.add (hsum.const_mul (B ^ k)))
    (fun ω => by
      simpa using prod_difference_bound Finset.univ
        (fun i => f i ω) (fun i => g i ω) hB
        (fun i _ => ⟨(hgb i ω).1, hgf i ω, (hfb i ω).2⟩))
  simp only [Pi.add_apply] at hbd
  rw [integral_add hgpi (hsum.const_mul (B ^ k)), integral_const_mul,
    integral_finsetSum (f := fun i ω => f i ω - g i ω) _
      (fun i _ => (hfi i).sub (hgi i))] at hbd
  have hprod : (∫ ω, ∏ i, g i ω ∂environmentLaw ν) =
      (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ^ k := by
    rw [fresh_rows_prod ν Finset.univ (fun i => LatticeBall (x i) n) g
      (fun i _ j _ hij => hx hij) (fun i _ =>
        (clippedInverse_measurable δ lam).comp (noDropFinite_measurable_ball ℓ (x i) n))]
    simp only [g, clipped_inverse_finite_integral_translation ν ℓ _ δ lam n,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hgap i : (∫ ω, f i ω - g i ω ∂environmentLaw ν) =
      ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
        clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν :=
    clipped_inverse_integral_gap ν ℓ (x i) hδ hlam n
  simp only [hprod, hgap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hbd
  have hle : (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ≤
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_mono (clipped_inverse_integrable ν (noDropFinite_measurable ℓ 0 n) hδ hlam)
      (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam)
      (fun ω => clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ 0 ω n))
  have hpow := pow_le_pow_left₀
    (integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam _).1)) hle k
  change (∫ ω, ∏ i, f i ω ∂environmentLaw ν) ≤ _
  exact hbd.trans (add_le_add hpow (by simpa only [mul_assoc] using hn.le))

lemma latticeBall_disjoint_of_coordinate_gap {d : ℕ} (i : Fin d)
    {x y : Lattice d} {n : ℕ} (hxy : (2 * n : ℤ) < |x i - y i|) :
    Disjoint (LatticeBall x n) (LatticeBall y n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := hz i
  have hy := hz' i
  have hh := abs_add_le (x i - z i) (z i - y i)
  rw [sub_add_sub_cancel] at hh
  rw [abs_sub_comm (x i) (z i)] at hh
  omega

lemma noDrop_real_inverse_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν) := by
  obtain ⟨p, hp, hm⟩ := noDrop_inverse_moment ν hue ℓ hℓ htrans
  let lam := min p 1
  have hlam : 0 < lam := lt_min hp zero_lt_one
  have hfin : (∫⁻ ω, noDropQuenched ℓ 0 ω ^ (-lam) ∂environmentLaw ν) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun ω => ?_)) hm
    exact ENNReal.rpow_le_rpow_of_exponent_ge (prob_le_one)
      (neg_le_neg (min_le_left p 1))
  refine ⟨lam, hlam, min_le_right _ _, ?_⟩
  simpa only [ENNReal.toReal_rpow] using
    integrable_toReal_of_lintegral_ne_top
      ((measurable_noDropQuenched ℓ 0).pow_const (-lam)).aemeasurable hfin.ne

lemma prod_max_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    (∏ i ∈ s, max (f i) δ) ≤ (∏ i ∈ s, f i) + δ := by
  classical
  by_cases h : ∀ i ∈ s, δ ≤ f i
  · have heq : (∏ i ∈ s, max (f i) δ) = ∏ i ∈ s, f i :=
      Finset.prod_congr rfl (fun i hi => max_eq_left (h i hi))
    rw [heq]
    exact le_add_of_nonneg_right hδ
  · push Not at h
    obtain ⟨i, hi, hif⟩ := h
    have hp := Finset.prod_le_prod_of_subset_of_le_one₀
      (show {i} ⊆ s from Finset.singleton_subset_iff.mpr hi)
      (f := fun j => max (f j) δ)
      (fun j hj => (hf j hj).1.trans (le_max_left _ _))
      (fun j hj _ => max_le (hf j hj).2 hδ1)
    simp only [Finset.prod_singleton, max_eq_right hif.le] at hp
    exact hp.trans (le_add_of_nonneg_left (Finset.prod_nonneg (fun j hj => (hf j hj).1)))

lemma noDropQuenched_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : (noDropQuenched ℓ x ω).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (show (1 : ℝ≥0∞) ≠ ∞ by simp)
    (show noDropQuenched ℓ x ω ≤ 1 from prob_le_one)

noncomputable def noDropProduct {d k : ℕ} (ℓ : Vector d) (x : Fin k → Lattice d)
    (ω : Environment d) : ℝ := ∏ i, (noDropQuenched ℓ (x i) ω).toReal

noncomputable def clippedNoDropProduct {d k : ℕ} (ℓ : Vector d) (δ : ℝ)
    (x : Fin k → Lattice d) (ω : Environment d) : ℝ :=
  ∏ i, max (noDropQuenched ℓ (x i) ω).toReal δ

lemma noDropProduct_bounds {d k : ℕ} (ℓ : Vector d) (x : Fin k → Lattice d)
    (ω : Environment d) : 0 ≤ noDropProduct ℓ x ω ∧ noDropProduct ℓ x ω ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg),
    Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => noDropQuenched_toReal_le_one ℓ _ ω)⟩

lemma clippedNoDropProduct_bounds {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    δ ^ k ≤ clippedNoDropProduct ℓ δ x ω ∧ clippedNoDropProduct ℓ δ x ω ≤ 1 := by
  constructor
  · have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin k => δ) (g := fun i => max (noDropQuenched ℓ (x i) ω).toReal δ)
      (fun _ _ => hδ) (fun _ _ => le_max_right _ _)
    simpa [clippedNoDropProduct] using h
  · exact Finset.prod_le_one₀ (fun _ _ => hδ.trans (le_max_right _ _))
      (fun _ _ => max_le (noDropQuenched_toReal_le_one ℓ _ ω) hδ1)

lemma clippedNoDropProduct_error {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ≤ noDropProduct ℓ x ω + δ := by
  exact prod_max_bound Finset.univ (fun i => (noDropQuenched ℓ (x i) ω).toReal)
    hδ hδ1 (fun _ _ => ⟨ENNReal.toReal_nonneg,
      noDropQuenched_toReal_le_one ℓ _ ω⟩)

lemma noDropProduct_measurable {d k : ℕ} (ℓ : Vector d) :
    Measurable (fun z : Environment d × (Fin k → Lattice d) => noDropProduct ℓ z.2 z.1) := by
  apply measurable_from_prod_countable_left
  intro x
  exact Finset.measurable_fun_prod _ (fun i _ => (measurable_noDropQuenched ℓ (x i)).ennreal_toReal)

lemma clippedNoDropProduct_measurable {d k : ℕ} (ℓ : Vector d) (δ : ℝ) :
    Measurable (fun z : Environment d × (Fin k → Lattice d) => clippedNoDropProduct ℓ δ z.2 z.1) := by
  apply measurable_from_prod_countable_left
  intro x
  exact Finset.measurable_fun_prod _ (fun i _ =>
    (measurable_noDropQuenched ℓ (x i)).ennreal_toReal.max measurable_const)

lemma clippedNoDropProduct_inverse {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (lam : ℝ) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ^ (-lam) =
      ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) := by
  exact (Real.finsetProd_rpow Finset.univ _
    (fun _ _ => hδ.trans (le_max_right _ _)) _).symm

lemma separated_noDropProduct_inverse_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω)
    (hmom : Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν))
    (k : ℕ) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, clippedNoDropProduct ℓ δ x ω ^ (-lam) ∂environmentLaw ν) ≤
        2 * (max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)) ^ k := by
  obtain ⟨n, hn⟩ := separated_clipped_inverse_product ν ℓ hδ hlam k (show (0 : ℝ) < 1 by norm_num)
  refine ⟨n, fun x hx => ?_⟩
  simp_rw [clippedNoDropProduct_inverse ℓ hδ.le]
  have hle : (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ≤
      ∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν := by
    apply integral_mono_ae (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam) hmom
    filter_upwards [hpos] with ω hω
    exact Real.rpow_le_rpow_of_nonpos (ENNReal.toReal_pos hω.ne' (measure_ne_top _ _))
      (le_max_left _ _) (neg_nonpos.mpr hlam)
  have hnonneg : 0 ≤ ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam
      (noDropQuenched ℓ 0 ω)).1)
  have hp := pow_le_pow_left₀ hnonneg (hle.trans (le_max_right 1 _)) k
  have h1 := one_le_pow₀ (n := k) (le_max_left 1
    (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν))
  have h := hn x hx
  nlinarith

end DirectionalTransience
end
end

end OAI
