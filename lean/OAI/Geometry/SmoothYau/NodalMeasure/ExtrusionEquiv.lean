import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace YauCounterexamples
theorem lowerSemicontinuous_measure_neg {A X : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (F : A → X → ℝ) (hF : ∀ a, Measurable (F a))
    (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => μ {x | F a x < 0}) := by
  let G : A → X → ℝ≥0∞ := fun a => {x | F a x < 0}.indicator (fun _ => 1)
  have hG (a : A) : Measurable (G a) :=
    measurable_const.indicator (measurableSet_lt (hF a) measurable_const)
  have hGl (x : X) : LowerSemicontinuous (fun a => G a x) := by
    have ho : IsOpen {a | F a x < 0} := isOpen_lt (hc x) continuous_const
    exact ho.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)
  have hGi (a : A) : ∫⁻ x, G a x ∂μ = μ {x | F a x < 0} := by
    dsimp only [G]
    rw [lintegral_indicator (measurableSet_lt (hF a) measurable_const)]
    simp
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro a
  rw [← hGi a]
  calc
    ∫⁻ x, G a x ∂μ ≤ ∫⁻ x, liminf (fun a' => G a' x) (𝓝 a) ∂μ :=
      lintegral_mono (fun x => (hGl x).le_liminf a)
    _ ≤ liminf (fun a' => ∫⁻ x, G a' x ∂μ) (𝓝 a) := lintegral_liminf_le hG
    _ = liminf (fun a' => μ {x | F a' x < 0}) (𝓝 a) := by simp_rw [hGi]

theorem gaussian_pi_open_pos {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (s : Set (ι → ℝ)) (hs : IsOpen s) (hne : s.Nonempty) :
    0 < (Measure.pi (fun i => gaussianReal (m i) 1)) s := by
  have (i : ι) : Measure.IsOpenPosMeasure (gaussianReal (m i) 1) :=
    (gaussianReal_absolutelyContinuous' (m i) one_ne_zero).isOpenPosMeasure
  exact hs.measure_pos _ hne

def gaussianPairSignProduct (p : ℝ × ℝ × ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (p.2.1 + x 0) * (p.2.2 + p.1 * x 0 + Real.sqrt (1 - p.1 ^ 2) * x 1)

def gaussianPairOppositeProbability (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) {x | gaussianPairSignProduct p x < 0}

theorem gaussianPairOppositeProbability_pos (p : ℝ × ℝ × ℝ)
    (hp : -1 < p.1 ∧ p.1 < 1) : 0 < gaussianPairOppositeProbability p := by
  have hpos : 0 < Real.sqrt (1 - p.1 ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  apply gaussian_pi_open_pos
  · apply isOpen_lt _ continuous_const
    unfold gaussianPairSignProduct
    fun_prop
  · refine ⟨![1 - p.2.1, (-1 - p.2.2 - p.1 * (1 - p.2.1)) /
        Real.sqrt (1 - p.1 ^ 2)], ?_⟩
    change (p.2.1 + (1 - p.2.1)) *
      (p.2.2 + p.1 * (1 - p.2.1) + Real.sqrt (1 - p.1 ^ 2) *
        ((-1 - p.2.2 - p.1 * (1 - p.2.1)) / Real.sqrt (1 - p.1 ^ 2))) < 0
    field_simp
    nlinarith

theorem lowerSemicontinuous_gaussianPairOppositeProbability :
    LowerSemicontinuous gaussianPairOppositeProbability := by
  apply lowerSemicontinuous_measure_neg
  · intro p
    unfold gaussianPairSignProduct
    fun_prop
  · intro x
    unfold gaussianPairSignProduct
    fun_prop

theorem gaussian_opposite_uniform (a b M : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (hb : b < 1) (hM : 0 ≤ M) :
    ∃ q : ℝ, 0 < q ∧ ∀ p : ℝ × ℝ × ℝ,
      a ≤ p.1 → p.1 ≤ b → |p.2.1| ≤ M → |p.2.2| ≤ M →
      ENNReal.ofReal q ≤ gaussianPairOppositeProbability p := by
  let K : Set (ℝ × ℝ × ℝ) := Icc a b ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)
  have hKn : K.Nonempty := ⟨(a, 0, 0), ⟨⟨le_rfl, hab⟩, ⟨by constructor <;> linarith,
    by constructor <;> linarith⟩⟩⟩
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨p, hpK, hpmin⟩ := LowerSemicontinuousOn.exists_isMinOn hKn hKc
    (lowerSemicontinuous_gaussianPairOppositeProbability.lowerSemicontinuousOn K)
  have hprob : 0 < gaussianPairOppositeProbability p :=
    gaussianPairOppositeProbability_pos p ⟨ha.trans_le hpK.1.1, hpK.1.2.trans_lt hb⟩
  have hfinite : gaussianPairOppositeProbability p ≠ ∞ := measure_ne_top _ _
  refine ⟨(gaussianPairOppositeProbability p).toReal, ENNReal.toReal_pos hprob.ne' hfinite, ?_⟩
  intro z hza hzb hz1 hz2
  rw [ENNReal.ofReal_toReal hfinite]
  exact hpmin ⟨⟨hza, hzb⟩, abs_le.mp hz1, abs_le.mp hz2⟩

end YauCounterexamples

end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

def oppositeSet {X M : Type*} (D : Set X) (a b : X → M) (f : M → ℝ) : Set X :=
  {x | x ∈ D ∧ f (a x) * f (b x) < 0}

def signMass {X M : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : Set X) (a b : X → M) (f : M → ℝ) : ℝ≥0∞ :=
  μ (oppositeSet D a b f)

theorem oppositeSet_pos_mul {X M : Type*} (D : Set X) (a b : X → M)
    (f q : M → ℝ) (hq : ∀ y, 0 < q y) :
    oppositeSet D a b (fun y => q y * f y) = oppositeSet D a b f := by
  ext x
  simp only [oppositeSet, mem_ofPred_eq]
  have h : (q (a x) * f (a x)) * (q (b x) * f (b x)) =
      (q (a x) * q (b x)) * (f (a x) * f (b x)) := by ring
  rw [h, mul_neg_iff]
  simp [not_lt.mpr (mul_pos (hq (a x)) (hq (b x))).le,
    mul_pos (hq (a x)) (hq (b x))]

theorem oppositeSet_const_mul {X M : Type*} (D : Set X) (a b : X → M)
    (f : M → ℝ) (c : ℝ) (hc : c ≠ 0) :
    oppositeSet D a b (fun y => c * f y) = oppositeSet D a b f := by
  ext x
  simp only [oppositeSet, mem_ofPred_eq]
  have h : (c * f (a x)) * (c * f (b x)) = c ^ 2 * (f (a x) * f (b x)) := by ring
  rw [h, mul_neg_iff]
  simp [sq_pos_of_ne_zero hc, not_lt.mpr (sq_nonneg c)]

theorem lowerSemicontinuous_measure_neg {A X : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (F : A → X → ℝ) (hF : ∀ a, Measurable (F a))
    (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => μ {x | F a x < 0}) := by
  let G : A → X → ℝ≥0∞ := fun a => {x | F a x < 0}.indicator (fun _ => 1)
  have hG (a : A) : Measurable (G a) :=
    measurable_const.indicator (measurableSet_lt (hF a) measurable_const)
  have hGl (x : X) : LowerSemicontinuous (fun a => G a x) := by
    have ho : IsOpen {a | F a x < 0} := isOpen_lt (hc x) continuous_const
    exact ho.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)
  have hGi (a : A) : ∫⁻ x, G a x ∂μ = μ {x | F a x < 0} := by
    dsimp only [G]
    rw [lintegral_indicator (measurableSet_lt (hF a) measurable_const)]
    simp
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro a
  rw [← hGi a]
  calc
    ∫⁻ x, G a x ∂μ ≤ ∫⁻ x, liminf (fun a' => G a' x) (𝓝 a) ∂μ :=
      lintegral_mono (fun x => (hGl x).le_liminf a)
    _ ≤ liminf (fun a' => ∫⁻ x, G a' x ∂μ) (𝓝 a) := lintegral_liminf_le hG
    _ = liminf (fun a' => μ {x | F a' x < 0}) (𝓝 a) := by simp_rw [hGi]

theorem lowerSemicontinuous_signMass {A X M : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (D : Set X) (a b : X → M) (F : A → M → ℝ)
    (hFa : ∀ p, Measurable (fun x => F p (a x)))
    (hFb : ∀ p, Measurable (fun x => F p (b x)))
    (hc : ∀ x, Continuous (fun p => F p x)) :
    LowerSemicontinuous (fun p => signMass μ D a b (F p)) := by
  have h := lowerSemicontinuous_measure_neg (μ.restrict D)
    (fun p x => F p (a x) * F p (b x))
    (fun p => (hFa p).mul (hFb p)) (fun x => (hc _).mul (hc _))
  have heq (p : A) : (μ.restrict D) {x | F p (a x) * F p (b x) < 0} =
      signMass μ D a b (F p) := by
    have hm : MeasurableSet {x | F p (a x) * F p (b x) < 0} :=
      measurableSet_lt ((hFa p).mul (hFb p)) measurable_const
    rw [Measure.restrict_apply hm]
    unfold signMass
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, oppositeSet]
    exact and_comm
  simpa only [heq] using h

def swept {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) (s : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ z ∈ s, ∃ t ∈ Icc 0 d, x = z - Pi.single i t}

@[simp] theorem swept_empty {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) :
    swept i d (∅ : Set (ι → ℝ)) = ∅ := by ext x; simp [swept]

theorem swept_mono {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) :
    Monotone (swept i d) := by
  rintro s t h x ⟨z, hz, r, hr, hx⟩
  exact ⟨z, h hz, r, hr, hx⟩

theorem swept_iUnion {ι J : Type*} [DecidableEq ι] (i : ι) (d : ℝ)
    (s : J → Set (ι → ℝ)) : swept i d (⋃ j, s j) = ⋃ j, swept i d (s j) := by
  ext x
  simp only [swept, mem_ofPred_eq, mem_iUnion]
  aesop

def sweptVolume {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (d : ℝ) :
    OuterMeasure (ι → ℝ) where
  measureOf s := volume (swept i d s)
  empty := by simp
  mono := fun h => measure_mono (swept_mono i d h)
  iUnion_nat := fun s _ => by rw [swept_iUnion]; exact measure_iUnion_le _

theorem swept_subset_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (s : Set (ι → ℝ)) (p : ι → ℝ) (hp : p ∈ s)
    (hs : ediam s ≠ (∞ : ℝ≥0∞)) :
    swept i d s ⊆ Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
      (fun j => p j + Metric.diam s) := by
  rintro x ⟨z, hz, t, ht, rfl⟩
  have hdist : ∀ j, dist (z j) (p j) ≤ Metric.diam s :=
    (dist_pi_le_iff Metric.diam_nonneg).mp (Metric.dist_le_diam_of_mem' hs hz hp)
  constructor
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      linarith [ht.2]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, ite_eq_right hji, sub_zero]
      linarith
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same]
      linarith [ht.1]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, sub_zero]
      linarith

lemma prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommMonoid R] (i : ι) (a b : R) :
    (∏ j : ι, if j = i then a else b) = a * b ^ (Fintype.card ι - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then a else b)
    (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  calc
    (∏ j ∈ Finset.univ.erase i, if j = i then a else b) =
        ∏ _j ∈ Finset.univ.erase i, b := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    _ = b ^ (Fintype.card ι - 1) := by simp

lemma swept_box_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d r : ℝ) (p : ι → ℝ) :
    volume (Icc (fun j => p j - r - if j = i then d else 0) (fun j => p j + r)) =
      ENNReal.ofReal (2 * r + d) * (ENNReal.ofReal (2 * r)) ^ (Fintype.card ι - 1) := by
  rw [Real.volume_Icc_pi]
  have h (j : ι) : ENNReal.ofReal (p j + r - (p j - r - if j = i then d else 0)) =
      if j = i then ENNReal.ofReal (2 * r + d) else ENNReal.ofReal (2 * r) := by
    split_ifs <;> congr 1 <;> ring
  simp only [h]
  exact prod_one_special i _ _

theorem sweptVolume_le_of_ediam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ))
    (hs : ediam s ≤ ENNReal.ofReal d) :
    sweptVolume i d s ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        ediam s ^ (Fintype.card ι - 1) := by
  obtain hse | ⟨p, hp⟩ := s.eq_empty_or_nonempty
  · subst s
    simp
  have hfin : ediam s ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hr : Metric.diam s ≤ d := ENNReal.toReal_le_of_le_ofReal hd.le hs
  have hr0 : 0 ≤ Metric.diam s := Metric.diam_nonneg
  have her : ENNReal.ofReal (Metric.diam s) = ediam s :=
    ENNReal.ofReal_toReal hfin
  change volume (swept i d s) ≤ _
  calc
    volume (swept i d s) ≤
        volume (Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
          (fun j => p j + Metric.diam s)) :=
      measure_mono (swept_subset_box i d s p hp hfin)
    _ = ENNReal.ofReal (2 * Metric.diam s + d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) :=
      swept_box_volume i _ _ _
    _ ≤ ENNReal.ofReal (3 * d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) := by
      gcongr
      linarith
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), her, mul_pow]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

theorem sweptVolume_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ)) :
    volume (swept i d s) ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) s := by
  let c : ℝ≥0∞ := 3 * ENNReal.ofReal d * 2 ^ (Fintype.card ι - 1)
  have hc : c ≠ (∞ : ℝ≥0∞) := by
    dsimp [c]
    finiteness
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have h := OuterMeasure.le_mkMetric
    (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) (sweptVolume i d)
    (ENNReal.ofReal d) (ENNReal.ofReal_pos.mpr hd)
    (sweptVolume_le_of_ediam_le i d hd)
  have heq : (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) =
      c • (fun r : ℝ≥0∞ => r ^ ((Fintype.card ι - 1 : ℕ) : ℝ)) := by
    ext r
    simp [ENNReal.rpow_natCast]
  rw [heq, OuterMeasure.mkMetric_smul _ hc hc0] at h
  have hs := h s
  simpa only [smul_apply, smul_eq_mul, OuterMeasure.coe_mkMetric,
    Measure.hausdorffMeasure, sweptVolume, c, OuterMeasure.coe_mk] using hs

theorem oppositeSet_subset_swept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 ≤ d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    oppositeSet D id (fun x => x + Pi.single i d) f ⊆
      swept i d (P ∩ {z | f z = 0}) := by
  rintro x ⟨hx, hsign⟩
  let g : ℝ → ℝ := fun t => f (x + Pi.single i t)
  have hcont : ContinuousOn g (Icc 0 d) := by
    apply hf.comp (continuous_const.add (continuous_single i)).continuousOn
    exact fun t ht => hseg x hx t ht
  have hg0 : g 0 = f x := by simp [g]
  have hgd : g d = f (x + Pi.single i d) := rfl
  have hz : (0 : ℝ) ∈ g '' Icc 0 d := by
    rcases mul_neg_iff.mp hsign with h | h
    · apply intermediate_value_Icc' hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.2.le h.1.le
    · apply intermediate_value_Icc hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.1.le h.2.le
  obtain ⟨t, ht, hzero⟩ := hz
  refine ⟨x + Pi.single i t, ⟨hseg x hx t ht, hzero⟩, t, ht, ?_⟩
  simp

theorem signMass_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    signMass volume D id (fun x => x + Pi.single i d) f ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) (P ∩ {z | f z = 0}) :=
  (measure_mono (oppositeSet_subset_swept i d hd.le D P f hf hseg)).trans
    (sweptVolume_le_hausdorff i d hd _)

def signCertificate {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f : (ι → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ p, ∑ i, (ENNReal.ofReal (d p))⁻¹ *
    signMass volume {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
      id (fun x => x + Pi.single i (d p)) f

theorem lowerSemicontinuous_signCertificate {A ι J : Type*}
    [TopologicalSpace A] [FirstCountableTopology A]
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (F : A → (ι → ℝ) → ℝ)
    (hm : ∀ a, Measurable (F a)) (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => signCertificate P d (F a)) := by
  apply lowerSemicontinuous_sum
  intro p _
  apply lowerSemicontinuous_sum
  intro i _
  have hb : Measurable (fun x : ι → ℝ => x + Pi.single i (d p)) :=
    (continuous_id.add continuous_const).measurable
  have h := lowerSemicontinuous_signMass ((ENNReal.ofReal (d p))⁻¹ • volume)
    {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
    id (fun x => x + Pi.single i (d p)) F
    (fun a => hm a) (fun a => (hm a).comp hb) hc
  simpa only [signMass, Measure.smul_apply, smul_eq_mul] using h

theorem signCertificate_le_hausdorff_on_union {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (hd : ∀ p, 0 < d p)
    (hPi : ∀ p, IsOpen (P p)) (hPc : ∀ p, Convex ℝ (P p))
    (hPd : Pairwise fun p q => Disjoint (P p) (P q)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f (⋃ p, P p)) :
    signCertificate P d f ≤
      ((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1))) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) ((⋃ p, P p) ∩ {z | f z = 0}) := by
  let μ : Measure (ι → ℝ) := Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ)
  let c : ℝ≥0∞ := 3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)
  have hterm (p : J) (i : ι) : (ENNReal.ofReal (d p))⁻¹ *
      signMass volume {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
        id (fun x => x + Pi.single i (d p)) f ≤ c * μ (P p ∩ {z | f z = 0}) := by
    have hseg : ∀ x ∈ {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p},
        ∀ t ∈ Icc 0 (d p), x + Pi.single i t ∈ P p := by
      rintro x ⟨hx, hy⟩ t ht
      have hc := hPc p hx hy (show 0 ≤ 1 - t / d p by
        have := (div_le_one (hd p)).mpr ht.2
        linarith) (div_nonneg ht.1 (hd p).le) (by ring : 1 - t / d p + t / d p = 1)
      convert hc using 1
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        field_simp [ne_of_gt (hd p)]
        ring
      · simp only [Pi.single_eq_of_ne hji]
        ring
    have h := signMass_le_hausdorff i (d p) (hd p) _ (P p) f (hf.mono (subset_iUnion P p)) hseg
    have hc0 : ENNReal.ofReal (d p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hd p))
    calc
      _ ≤ (ENNReal.ofReal (d p))⁻¹ *
          ((3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
            μ (P p ∩ {z | f z = 0})) := mul_le_mul_right h _
      _ = _ := by
        unfold c
        rw [show 3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1) =
          ENNReal.ofReal (d p) * (3 * 2 ^ (Fintype.card ι - 1)) by ring,
          ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  have hms (p : J) : MeasurableSet (P p ∩ {z | f z = 0}) := by
    obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp (hf.mono (subset_iUnion P p))
      {0} isClosed_singleton
    change MeasurableSet (P p ∩ f ⁻¹' {0})
    rw [inter_comm, heq]
    exact hC.measurableSet.inter (hPi p).measurableSet
  have hdis : Pairwise (fun p q => Disjoint (P p ∩ {z | f z = 0})
      (P q ∩ {z | f z = 0})) := by
    intro p q hpq
    exact (hPd hpq).mono inter_subset_left inter_subset_left
  have hsum : ∑ p, μ (P p ∩ {z | f z = 0}) ≤ μ ((⋃ p, P p) ∩ {z | f z = 0}) := by
    have heq : μ (⋃ p, P p ∩ {z | f z = 0}) = ∑ p, μ (P p ∩ {z | f z = 0}) := by
      simpa only [tsum_fintype] using measure_iUnion hdis hms
    rw [← heq]
    rw [iUnion_inter]

  calc
    signCertificate P d f ≤ ∑ p : J, ∑ _i : ι, c * μ (P p ∩ {z | f z = 0}) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun i _ => hterm p i
    _ = ((Fintype.card ι : ℝ≥0∞) * c) * ∑ p : J, μ (P p ∩ {z | f z = 0}) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hsum _

theorem signCertificate_pos_mul {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f q : (ι → ℝ) → ℝ)
    (hq : ∀ x, 0 < q x) :
    signCertificate P d (fun x => q x * f x) = signCertificate P d f := by
  unfold signCertificate signMass
  simp_rw [oppositeSet_pos_mul _ _ _ f q hq]

theorem signCertificate_const_mul {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f : (ι → ℝ) → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    signCertificate P d (fun x => c * f x) = signCertificate P d f := by
  unfold signCertificate signMass
  simp_rw [oppositeSet_const_mul _ _ _ f c hc]

theorem signCertificate_le_volume {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f : (ι → ℝ) → ℝ) :
    signCertificate P d f ≤ (Fintype.card ι : ℝ≥0∞) *
      ∑ p, (ENNReal.ofReal (d p))⁻¹ * volume (P p) := by
  calc
    signCertificate P d f ≤ ∑ p : J, ∑ _i : ι,
        (ENNReal.ofReal (d p))⁻¹ * volume (P p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_right
      exact measure_mono (fun _ hx => hx.1.1)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]

theorem signCertificate_le_hausdorff {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (hd : ∀ p, 0 < d p)
    (hPi : ∀ p, IsOpen (P p)) (hPc : ∀ p, Convex ℝ (P p))
    (hPd : Pairwise fun p q => Disjoint (P p) (P q)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f (⋃ p, P p)) :
    signCertificate P d f ≤
      ((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1))) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) {z | f z = 0} :=
  (signCertificate_le_hausdorff_on_union P d hd hPi hPc hPd f hf).trans
    (mul_le_mul_right (measure_mono inter_subset_right) _)

theorem signCertificate_le_ambient_hausdorff {ι J M : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (hd : ∀ p, 0 < d p)
    (hPi : ∀ p, IsOpen (P p)) (hPc : ∀ p, Convex ℝ (P p))
    (hPd : Pairwise fun p q => Disjoint (P p) (P q))
    (ψ : (ι → ℝ) → M) (hψ : ContinuousOn ψ (⋃ p, P p))
    (c : M → (ι → ℝ)) (K : ℝ≥0) (hc : LipschitzWith K c)
    (hcψ : ∀ x ∈ ⋃ p, P p, c (ψ x) = x) (u : M → ℝ) (hu : Continuous u) :
    signCertificate P d (fun x => u (ψ x)) ≤
      (((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1))) *
        (K : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
          Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) {z | u z = 0} := by
  have hf : ContinuousOn (fun x => u (ψ x)) (⋃ p, P p) :=
    hu.continuousOn.comp hψ (mapsTo_univ _ _)
  have hsub : ((⋃ p, P p) ∩ {x | u (ψ x) = 0}) ⊆ c '' {z | u z = 0} := by
    rintro x ⟨hx, hz⟩
    exact ⟨ψ x, hz, hcψ x hx⟩
  have hm := hc.hausdorffMeasure_image_le
    (show (0 : ℝ) ≤ (Fintype.card ι - 1 : ℕ) by positivity) {z | u z = 0}
  calc
    _ ≤ _ := signCertificate_le_hausdorff_on_union P d hd hPi hPc hPd _ hf
    _ ≤ _ := mul_le_mul_right (measure_mono hsub) _
    _ ≤ _ := by
      simpa only [ENNReal.rpow_natCast, mul_assoc] using mul_le_mul_right hm
        ((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)))

end YauCounterexamples.SignTests
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

lemma normalWaveEquiv_axis_shift (x : Fin 3 → ℝ) (d : ℝ) (i : Fin 3) :
    normalWaveEquiv (x+Pi.single i d) =
      normalWaveEquiv x+d • EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [map_add,←normalWaveEquiv_single]
  have he : Pi.single i d = d • Pi.single i (1:ℝ) := by
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he,map_smul]

def coordinateRegionMeasure (C : Set (Fin 3 → ℝ)) : Measure NormalWaveSpace :=
  Measure.map normalWaveEquiv (volume.restrict C)

lemma coordinateRegionMeasure_sign_le (C P : Set (Fin 3 → ℝ))
    (d : ℝ) (i : Fin 3) (hC : ∀ x ∈ C, x ∈ P ∧ x+Pi.single i d ∈ P)
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    coordinateRegionMeasure C {x | f x*f (x+d • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0} ≤
      SignTests.signMass volume {x | x ∈ P ∧ x+Pi.single i d ∈ P}
        id (fun x => x+Pi.single i d) (f ∘ normalWaveEquiv) := by
  have hm : MeasurableSet {x | f x*f (x+d • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0} :=
    isOpen_lt (hf.mul (hf.comp (continuous_id.add continuous_const))) continuous_const |>.measurableSet
  rw [coordinateRegionMeasure,Measure.map_apply normalWaveEquiv.continuous.measurable hm,
    Measure.restrict_apply (hm.preimage normalWaveEquiv.continuous.measurable)]
  apply measure_mono
  rintro x ⟨hx,hxC⟩
  refine ⟨hC x hxC,?_⟩
  simpa only [mem_preimage,mem_ofPred_eq,Function.comp_apply,id_eq,normalWaveEquiv_axis_shift] using hx

lemma coordinateRegionMeasure_univ (C : Set (Fin 3 → ℝ)) :
    coordinateRegionMeasure C univ = volume C := by
  rw [coordinateRegionMeasure,Measure.map_apply normalWaveEquiv.continuous.measurable MeasurableSet.univ]
  simp

lemma coordinateRegionMeasure_ae {C : Set (Fin 3 → ℝ)} (hC : MeasurableSet C)
    {P : NormalWaveSpace → Prop} (hP : ∀ x ∈ C, P (normalWaveEquiv x)) :
    ∀ᵐ y ∂coordinateRegionMeasure C, P y := by
  have h : ∀ᵐ y ∂coordinateRegionMeasure C, normalWaveEquiv.symm y ∈ C := by
    apply (ae_map_iff normalWaveEquiv.continuous.measurable.aemeasurable
      (hC.preimage normalWaveEquiv.symm.continuous.measurable)).mpr
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ae_restrict_mem hC
  filter_upwards [h] with y hy
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hP (normalWaveEquiv.symm y) hy

instance coordinateRegionMeasure_finite (C : Set (Fin 3 → ℝ))
    [IsFiniteMeasure (volume.restrict C)] : IsFiniteMeasure (coordinateRegionMeasure C) :=
  Measure.isFiniteMeasure_map _ _

theorem coordinate_region_score_le_certificate {J : Type*} [Fintype J]
    (P C : J → Set (Fin 3 → ℝ)) (d : J → ℝ) (hd : ∀ a, 0 < d a)
    (hC : ∀ a, ∀ x ∈ C a, ∀ i : Fin 3, x ∈ P a ∧ x+Pi.single i (d a) ∈ P a)
    (hfin : ∀ a, IsFiniteMeasure (coordinateRegionMeasure (C a)))
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    ENNReal.ofReal (∑ a, (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal) ≤
      SignTests.signCertificate P d (f ∘ normalWaveEquiv) := by
  classical
  have hnon (a : J) : 0 ≤ (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal := by
    exact mul_nonneg (inv_nonneg.mpr (hd a).le) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hnon a)]
  apply Finset.sum_le_sum
  intro a _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hd a).le),
    ENNReal.ofReal_inv_of_pos (hd a),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  gcongr
  exact coordinateRegionMeasure_sign_le (C a) (P a) (d a) i
    (fun x hx => hC a x hx i) hf

theorem coordinate_region_score_le_nodal {J : Type*} [Fintype J]
    (P C : J → Set (Fin 3 → ℝ)) (d : J → ℝ) (hd : ∀ a, 0 < d a)
    (hP : ∀ a, IsOpen (P a)) (hPc : ∀ a, Convex ℝ (P a))
    (hPd : Pairwise fun a b => Disjoint (P a) (P b))
    (hC : ∀ a, ∀ x ∈ C a, ∀ i : Fin 3, x ∈ P a ∧ x+Pi.single i (d a) ∈ P a)
    (hfin : ∀ a, IsFiniteMeasure (coordinateRegionMeasure (C a)))
    {f : NormalWaveSpace → ℝ} (hf : Continuous f) :
    ENNReal.ofReal (∑ a, (d a)⁻¹ * ∑ i : Fin 3,
      (coordinateRegionMeasure (C a)
        {x | f x*f (x+d a • EuclideanSpace.basisFun (Fin 3) ℝ i) < 0}).toReal) ≤
      36 * Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | f (normalWaveEquiv x) = 0}) := by
  apply (coordinate_region_score_le_certificate P C d hd hC hfin hf).trans
  have h := SignTests.signCertificate_le_hausdorff_on_union P d hd hP hPc hPd
    (f ∘ normalWaveEquiv) (hf.comp normalWaveEquiv.continuous).continuousOn
  norm_num at h
  exact h

end YauCounterexamples

end

open Set Function MeasureTheory
open scoped ENNReal
namespace YauCounterexamples.SignTests
abbrev extrusionEquiv (n : ℕ) : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
lemma extrusionEquiv_apply {n : ℕ} (x : Fin (n+1) → ℝ) :
    extrusionEquiv n x=(x 0, Fin.tail x) := by
  ext i <;> simp [extrusionEquiv,MeasurableEquiv.piFinSuccAbove,Fin.tail]
def extrudeSet {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  extrusionEquiv n ⁻¹' (Ioo 0 1 ×ˢ P)
lemma extrudeSet_volume {n : ℕ} (P : Set (Fin n → ℝ)) :
    volume (extrudeSet P)=volume P := by
  rw [extrudeSet,(volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).measure_preimage_emb
    (extrusionEquiv n).measurableEmbedding]
  change (volume.prod volume) (Ioo (0:ℝ) 1 ×ˢ P)=volume P
  rw [Measure.prod_prod]
  simp
lemma tail_shift_succ {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin n) (d : ℝ) :
    Fin.tail (x+Pi.single i.succ d)=Fin.tail x+Pi.single i d := by
  ext j
  simp [Fin.tail,Pi.single_apply]
lemma head_shift_succ {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin n) (d : ℝ) :
    (x+Pi.single i.succ d : Fin (n+1) → ℝ) 0=x 0 := by simp
lemma tail_shift_zero {n : ℕ} (x : Fin (n+1) → ℝ) (d : ℝ) :
    Fin.tail (x+Pi.single 0 d)=Fin.tail x := by
  ext j
  simp [Fin.tail]
lemma signMass_extrude_succ {n : ℕ} (P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (d : ℝ) :
    signMass volume {x | x∈extrudeSet P ∧ x+Pi.single i.succ d∈extrudeSet P}
      id (fun x => x+Pi.single i.succ d) (f ∘ Fin.tail) =
    signMass volume {x | x∈P ∧ x+Pi.single i d∈P}
      id (fun x => x+Pi.single i d) f := by
  unfold signMass
  have he : oppositeSet {x | x∈extrudeSet P ∧ x+Pi.single i.succ d∈extrudeSet P}
      id (fun x => x+Pi.single i.succ d) (f ∘ Fin.tail) =
      extrudeSet (oppositeSet {x | x∈P ∧ x+Pi.single i d∈P} id (fun x => x+Pi.single i d) f) := by
    ext x
    simp only [oppositeSet,extrudeSet,mem_preimage,extrusionEquiv_apply,
      mem_prod,mem_ofPred_eq,Function.comp_apply,id_eq,head_shift_succ,tail_shift_succ]
    tauto
  rw [he,extrudeSet_volume]
lemma signMass_extrude_zero {n : ℕ} (P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (d : ℝ) :
    signMass volume {x | x∈extrudeSet P ∧ x+Pi.single 0 d∈extrudeSet P}
      id (fun x => x+Pi.single 0 d) (f ∘ Fin.tail)=0 := by
  unfold signMass
  have he : oppositeSet {x | x∈extrudeSet P ∧ x+Pi.single 0 d∈extrudeSet P}
      id (fun x => x+Pi.single 0 d) (f ∘ Fin.tail)=∅ := by
    ext x
    simp only [oppositeSet,mem_ofPred_eq,Function.comp_apply,id_eq,tail_shift_zero,mem_empty_iff_false,iff_false]
    intro hx
    nlinarith [sq_nonneg (f (Fin.tail x))]
  rw [he,measure_empty]
theorem signCertificate_extrude {n : ℕ} {J : Type*} [Fintype J]
    (P : J → Set (Fin n → ℝ)) (d : J → ℝ) (f : (Fin n → ℝ) → ℝ) :
    signCertificate (fun j => extrudeSet (P j)) d (f ∘ Fin.tail)=signCertificate P d f := by
  unfold signCertificate
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_succ,signMass_extrude_zero,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [signMass_extrude_succ]
end YauCounterexamples.SignTests
end

end OAI
