import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightSlab

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def StrictRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  ∀ j < n, dot (realPosition (X j)) ℓ < dot (realPosition (X n)) ℓ

def TrueRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  StrictRecord ℓ X n ∧ X ∈ FutureNoDrop ℓ n

def FirstTrueRecord {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : Prop :=
  0 < n ∧ TrueRecord ℓ X n ∧ ∀ j, 0 < j → j < n → ¬ TrueRecord ℓ X j

lemma measurableSet_strictRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | StrictRecord ℓ X n} := by
  simp only [StrictRecord, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt
      ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
        (measurable_pi_apply j))
      ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
        (measurable_pi_apply n))

lemma measurableSet_trueRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | TrueRecord ℓ X n} :=
  (measurableSet_strictRecord ℓ n).inter (measurableSet_futureNoDrop ℓ n)

lemma measurableSet_firstTrueRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | FirstTrueRecord ℓ X n} := by
  simp only [FirstTrueRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_trueRecord ℓ n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => (measurableSet_trueRecord ℓ j).compl))

lemma wordDepartures_mem_iff {d : ℕ} (x y : Lattice d) (w : List (Direction d)) :
    y ∈ wordDepartures x w ↔ ∃ j < w.length, y = wordPath x w j := by
  induction w generalizing x with
  | nil => simp [wordDepartures]
  | cons e w ih =>
    rw [wordDepartures, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨j + 1, by simpa using hj, rfl⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact Or.inl (by simpa using he)
      | succ j => exact Or.inr ⟨j, by simpa using hj, he⟩

lemma strictRecord_congr_prefix {d : ℕ} (ℓ : Vector d) {X Y : Path d} {n m : ℕ}
    (hn : n ≤ m) (hXY : ∀ j ≤ m, X j = Y j) :
    StrictRecord ℓ X n ↔ StrictRecord ℓ Y n := by
  simp only [StrictRecord]
  constructor <;> intro h j hj
  · simpa only [hXY j (hj.le.trans hn), hXY n hn] using h j hj
  · simpa only [hXY j (hj.le.trans hn), hXY n hn] using h j hj

def AdmissibleTrueWord {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : Prop :=
  0 < w.length ∧
  (∀ j < w.length, 0 ≤ dot (realPosition (wordPath 0 w j)) ℓ ∧
    dot (realPosition (wordPath 0 w j)) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ) ∧
  ∀ j, 0 < j → j < w.length → StrictRecord ℓ (wordPath 0 w) j →
    ∃ k, j < k ∧ k < w.length ∧ dot (realPosition (wordPath 0 w k)) ℓ <
      dot (realPosition (wordPath 0 w j)) ℓ

lemma admissibleTrueWord_record {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) :
    ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
  exact (hw.2.1 j hj).2

lemma suffix_noDrop_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    (fun j => X (n + j) - X n) ∈ NoDrop ℓ 0 ↔ X ∈ FutureNoDrop ℓ n := by
  change (∀ j, dot (realPosition 0) ℓ ≤ dot (realPosition (X (n + j) - X n)) ℓ) ↔ _
  simp only [dot_realPosition_sub, FutureNoDrop, Set.mem_ofPred_eq]
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  rw [hzero]
  exact forall_congr' fun j => sub_nonneg

lemma firstTrueWord_characterization {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (X : Path d) (hX : X ∈ wordCylinder 0 w) :
    (X ∈ NoDrop ℓ 0 ∧ FirstTrueRecord ℓ X w.length) ↔
      AdmissibleTrueWord ℓ w ∧
        (fun j => X (w.length + j) - wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
  have hx0 : X 0 = 0 := by simpa only [wordPath_zero] using hX 0 (Nat.zero_le _)
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  have hrec (j : ℕ) (hj : j ≤ w.length) :
      StrictRecord ℓ X j ↔ StrictRecord ℓ (wordPath 0 w) j :=
    strictRecord_congr_prefix ℓ hj hX
  have hsuf : (fun j => X (w.length + j) - wordPath 0 w w.length) ∈ NoDrop ℓ 0 ↔
      X ∈ FutureNoDrop ℓ w.length := by
    rw [← hX w.length le_rfl]
    exact suffix_noDrop_iff ℓ X w.length
  rw [hsuf]
  constructor
  · rintro ⟨hD, hn, ⟨hr, hs⟩, hfirst⟩
    refine ⟨⟨hn, ?_, ?_⟩, hs⟩
    · intro j hj
      constructor
      · simpa only [← hX j hj.le, hzero] using hD j
      · simpa only [← hX j hj.le, ← hX w.length le_rfl] using hr j hj
    · intro j hj hjn hrj
      have hnot := hfirst j hj hjn
      have hnotD : X ∉ FutureNoDrop ℓ j := fun h => hnot ⟨(hrec j hjn.le).mpr hrj, h⟩
      change ¬ ∀ k, dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j + k))) ℓ at hnotD
      push Not at hnotD
      obtain ⟨k, hk⟩ := hnotD
      have hjk : j < j + k := by
        by_contra hh
        have he : j + k = j := by omega
        rw [he] at hk
        exact (lt_irrefl _) hk
      have hklen : j + k < w.length := by
        by_contra hh
        have hle : w.length ≤ j + k := by omega
        have hs' := hs (j + k - w.length)
        change dot (realPosition (X w.length)) ℓ ≤
          dot (realPosition (X (w.length + (j + k - w.length)))) ℓ at hs'
        rw [Nat.add_sub_of_le hle] at hs'
        exact (not_lt_of_ge ((hr j hjn).le.trans hs')) hk
      exact ⟨j + k, hjk, hklen, by
        simpa only [← hX (j + k) hklen.le, ← hX j hjn.le] using hk⟩
  · rintro ⟨⟨hn, hpre, hbad⟩, hs⟩
    have hr : StrictRecord ℓ X w.length := (hrec _ le_rfl).mpr fun j hj => (hpre j hj).2
    refine ⟨?_, hn, ⟨hr, hs⟩, ?_⟩
    · intro j
      by_cases hj : j < w.length
      · simpa only [hX j hj.le, hzero] using (hpre j hj).1
      · have hle : w.length ≤ j := by omega
        have ht := hs (j - w.length)
        change dot (realPosition (X w.length)) ℓ ≤
          dot (realPosition (X (w.length + (j - w.length)))) ℓ at ht
        rw [Nat.add_sub_of_le hle] at ht
        exact (le_of_eq (congrArg (fun x : Lattice d => dot (realPosition x) ℓ) hx0.symm)).trans
          ((hr 0 hn).le.trans ht)
    · intro j hj hjn ⟨hrj, hsj⟩
      obtain ⟨k, hjk, hk, hdrop⟩ := hbad j hj hjn ((hrec j hjn.le).mp hrj)
      have ht := hsj (k - j)
      change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j + (k - j)))) ℓ at ht
      rw [Nat.add_sub_of_le hjk.le, hX j hjn.le, hX k hk.le] at ht
      exact (not_lt_of_ge ht) hdrop

lemma firstTrueRecord_unique {d : ℕ} (ℓ : Vector d) (X : Path d) {m n : ℕ}
    (hm : FirstTrueRecord ℓ X m) (hn : FirstTrueRecord ℓ X n) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (hn.2.2 m hm.1 h hm.2.1)
  · exact h
  · exact False.elim (hm.2.2 n hn.1 h hn.2.1)

noncomputable def conditionedLaw {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (annealedLaw ν).restrict (NoDrop ℓ 0)

lemma conditionedLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (conditionedLaw ν ℓ) := by
  constructor
  simp only [conditionedLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)

lemma conditionedLaw_apply_of_subset {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ * annealedLaw ν A := by
  rw [conditionedLaw, Measure.smul_apply, Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hAD, smul_eq_mul]

lemma conditioned_true_word_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (hw : AdmissibleTrueWord ℓ w)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * conditionedLaw ν ℓ A := by
  have hE : MeasurableSet ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) :=
    (hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder _ _)
  have hED : ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ⊆ NoDrop ℓ 0 := by
    rintro X ⟨hXA, hX⟩
    exact ((firstTrueWord_characterization ℓ w X hX).mpr ⟨hw, hAD hXA⟩).1
  rw [conditionedLaw_apply_of_subset ν ℓ _ hE hED,
    annealed_record_suffix ν ℓ w (admissibleTrueWord_record ℓ w hw) A hA hAD,
    conditionedLaw_apply_of_subset ν ℓ A hA hAD]
  ac_rfl

lemma piLE_iSup_eq {d : ℕ} :
    (⨆ n : ℕ, Filtration.piLE (X := fun _ : ℕ => Lattice d) n) =
      (inferInstance : MeasurableSpace (Path d)) := by
  apply le_antisymm (iSup_le fun n => Filtration.piLE.le n)
  change (⨆ n : ℕ, MeasurableSpace.comap (fun X : Path d => X n) inferInstance) ≤ _
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup _ n)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hm : @Measurable (Path d) (Lattice d)
      (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance) _
        (fun X => X n) := by
    have hc : Measurable (fun f : (i : Finset.Iic n) → Lattice d =>
        f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
    exact hc.comp (Measurable.of_comap_le le_rfl)
  exact hm.comap_le

lemma prefix_probability_lower {d : ℕ} (μ : Measure (Path d))
    (E : Set (Path d)) (p : ℝ≥0∞) (n : ℕ)
    (h : ∀ f : Path d, p * μ (pathCylinder f n) ≤ μ (E ∩ pathCylinder f n))
    (S : Set (Path d)) (hS : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => Lattice d) n] S) :
    p * μ S ≤ μ (E ∩ S) := by
  classical
  rw [Filtration.piLE_eq_comap_frestrictLe] at hS
  obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [measure_partition_prefix μ _ n, measure_partition_prefix μ (E ∩ _) n,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro f
  have hc : Preorder.frestrictLe n ⁻¹' B ∩ pathCylinder (extendPrefix n f) n =
      if f ∈ B then pathCylinder (extendPrefix n f) n else ∅ := by
    split_ifs with hf
    · apply Set.inter_eq_right.mpr
      intro X hX
      change Preorder.frestrictLe n X ∈ B
      have he : Preorder.frestrictLe n X = f := by
        funext j
        change X j = f j
        simpa only [extendPrefix_apply n f j (Finset.mem_Iic.mp j.2)]
          using hX j (Finset.mem_Iic.mp j.2)
      rwa [he]
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hB, hX⟩
      have he : Preorder.frestrictLe n X = f := by
        funext j
        change X j = f j
        simpa only [extendPrefix_apply n f j (Finset.mem_Iic.mp j.2)]
          using hX j (Finset.mem_Iic.mp j.2)
      exact hf (by simpa only [Set.mem_preimage, he] using hB)
  rw [Set.inter_assoc, hc]
  split_ifs
  · exact h _
  · simp

lemma ae_of_prefix_probability_lower {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    (E : Set (Path d)) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : 0 < p) (hpt : p ≠ ∞)
    (h : ∀ (n : ℕ) (f : Path d),
      p * μ (pathCylinder f n) ≤ μ (E ∩ pathCylinder f n)) : ∀ᵐ X ∂μ, X ∈ E := by
  let g : Path d → ℝ := E.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hE
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (Path d)) := Filtration.piLE
  have hlo (n : ℕ) : ∀ᵐ X ∂μ, p.toReal ≤ μ[g | ℱ n] X := by
    apply ae_of_ae_trim (ℱ.le n)
    apply ae_le_of_forall_setIntegral_le (integrable_const p.toReal)
      (integrable_condExp.trim (ℱ.le n) stronglyMeasurable_condExp)
    intro S hS _
    rw [← setIntegral_trim (ℱ.le n) stronglyMeasurable_const hS,
      ← setIntegral_trim (ℱ.le n) stronglyMeasurable_condExp hS,
      setIntegral_condExp (ℱ.le n) hg hS]
    have hh := prefix_probability_lower μ E p n (h n) S hS
    have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hh
    rw [ENNReal.toReal_mul] at hreal
    simpa only [g, setIntegral_indicator hE, setIntegral_const, smul_eq_mul,
      mul_one, one_mul, Measure.real, Set.inter_comm E S, mul_comm] using hreal
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] g := by
    change StronglyMeasurable[⨆ n, Filtration.piLE (X := fun _ : ℕ => Lattice d) n] g
    rw [piLE_iSup_eq]
    exact stronglyMeasurable_const.indicator hE
  have hlim := hg.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  filter_upwards [ae_all_iff.mpr hlo, hlim] with X hX hlimX
  have hge : p.toReal ≤ g X := ge_of_tendsto hlimX (Eventually.of_forall hX)
  by_contra hnot
  have hzero : g X = 0 := Set.indicator_of_notMem hnot _
  rw [hzero] at hge
  exact (not_le_of_gt (ENNReal.toReal_pos hp.ne' hpt)) hge

lemma annealed_record_cylinder_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Path d) (n : ℕ) (hn : 0 < n) (hr : StrictRecord ℓ f n) :
    annealedLaw ν ((fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (f n) ∩
      pathCylinder f n) =
      annealedLaw ν (pathCylinder f n) * annealedLaw ν (NoDrop ℓ 0) := by
  by_cases hf : f 0 = 0
  · let S : Set (Lattice d) := {y | ∃ j < n, y = f j}
    let T : Set (Lattice d) := {y | dot (realPosition (f n)) ℓ ≤ dot (realPosition y) ℓ}
    have hST : Disjoint S T := by
      apply Set.disjoint_left.mpr
      rintro y ⟨j, hj, rfl⟩ hy
      exact (not_le_of_gt (hr j hj)) hy
    have hS0 : (0 : Lattice d) ∈ S := ⟨0, hn, hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω, 0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j, hj, rfl⟩)
    rw [annealed_apply ν ((measurableSet_noDrop ℓ (f n)).preimage
      (by fun_prop) |>.inter (measurableSet_pathCylinder f n))]
    simp_rw [quenched_prefix_future _ _ _ hf n (measurableSet_noDrop ℓ (f n))]
    change (∫⁻ ω, quenchedKernel (ω, 0) (pathCylinder f n) * noDropQuenched ℓ (f n) ω
      ∂environmentLaw ν) = _
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST) hm
      (measurable_noDropQuenched_rows ℓ (f n)),
      annealed_noDrop_translation, ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hzero : annealedLaw ν (pathCylinder f n) = 0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hzero, hzero, zero_mul]

def PrefixDetermined {d : ℕ} (n : ℕ) (A : Set (Path d)) : Prop :=
  ∀ X Y, (∀ j ≤ n, X j = Y j) → (X ∈ A ↔ Y ∈ A)

lemma prefixDetermined_mono {d : ℕ} {n m : ℕ} (hm : n ≤ m)
    {A : Set (Path d)} (hA : PrefixDetermined n A) : PrefixDetermined m A :=
  fun X Y hXY => hA X Y (fun j hj => hXY j (hj.trans hm))

lemma prefixDetermined_inter {d : ℕ} {n : ℕ} {A B : Set (Path d)}
    (hA : PrefixDetermined n A) (hB : PrefixDetermined n B) : PrefixDetermined n (A ∩ B) :=
  fun X Y hXY => and_congr (hA X Y hXY) (hB X Y hXY)

lemma prefixDetermined_cylinder {d : ℕ} (f : Path d) (n : ℕ) :
    PrefixDetermined n (pathCylinder f n) := by
  intro X Y hXY
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]

open scoped Classical in
lemma prefixDetermined_inter_cylinder {d : ℕ} (A : Set (Path d)) (n : ℕ)
    (hA : PrefixDetermined n A) (f : Path d) :
    A ∩ pathCylinder f n = if f ∈ A then pathCylinder f n else ∅ := by
  classical
  split_ifs with hf
  · exact Set.inter_eq_right.mpr fun X hX => (hA X f hX).mpr hf
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hXA, hX⟩
    exact hf ((hA X f hX).mp hXA)

lemma annealed_record_event_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (n : ℕ) (hn : 0 < n) (A : Set (Path d)) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) :
    annealedLaw ν (A ∩ FutureNoDrop ℓ n) =
      annealedLaw ν A * annealedLaw ν (NoDrop ℓ 0) := by
  classical
  rw [measure_partition_prefix (annealedLaw ν) (A ∩ _) n,
    measure_partition_prefix (annealedLaw ν) A n, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ A
  · have he : (A ∩ FutureNoDrop ℓ n) ∩ pathCylinder g n =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (g n) ∩ pathCylinder g n := by
      ext X
      constructor
      · rintro ⟨⟨_, hD⟩, hX⟩
        refine ⟨?_, hX⟩
        change ∀ j, dot (realPosition (g n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ at hD
        simpa only [← hX n le_rfl] using hD
      · rintro ⟨hD, hX⟩
        refine ⟨⟨(hA X g hX).mpr hg, ?_⟩, hX⟩
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ
        change ∀ j, dot (realPosition (g n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ at hD
        simpa only [hX n le_rfl] using hD
    have hAc : A ∩ pathCylinder g n = pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder A n hA g, ite_eq_left hg]
    rw [he, hAc]
    exact annealed_record_cylinder_noDrop ν ℓ g n hn (hr g hg)
  · have hzero : A ∩ pathCylinder g n = ∅ := by
      rw [prefixDetermined_inter_cylinder A n hA g, ite_eq_right hg]
    have he : (A ∩ FutureNoDrop ℓ n) ∩ pathCylinder g n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hXA, _⟩, hX⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hzero) X ⟨hXA, hX⟩
    rw [he, hzero, measure_empty, zero_mul]

def NextRecordAfter {d : ℕ} (ℓ : Vector d) (N n : ℕ) : Set (Path d) :=
  {X | N < n ∧ StrictRecord ℓ X n ∧ ∀ j, N < j → j < n → ¬ StrictRecord ℓ X j}

lemma nextRecordAfter_prefix {d : ℕ} (ℓ : Vector d) (N n : ℕ) :
    PrefixDetermined n (NextRecordAfter ℓ N n) := by
  intro X Y hXY
  simp only [NextRecordAfter, Set.mem_ofPred_eq]
  apply and_congr Iff.rfl
  apply and_congr (strictRecord_congr_prefix ℓ le_rfl hXY)
  exact forall_congr' fun j => forall_congr' fun _ => forall_congr' fun hj =>
    not_congr (strictRecord_congr_prefix ℓ hj.le hXY)

lemma measurableSet_nextRecordAfter {d : ℕ} (ℓ : Vector d) (N n : ℕ) :
    MeasurableSet (NextRecordAfter ℓ N n) := by
  simp only [NextRecordAfter, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_strictRecord ℓ n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => (measurableSet_strictRecord ℓ j).compl))

lemma nextRecordAfter_disjoint {d : ℕ} (ℓ : Vector d) (N : ℕ) :
    Pairwise (fun m n => Disjoint (NextRecordAfter ℓ N m) (NextRecordAfter ℓ N n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hXm hXn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hXn.2.2 m hXm.1 h hXm.2.1
  · exact hXm.2.2 n hXn.1 h hXn.2.1

lemma exists_strictRecord_gt {d : ℕ} (ℓ : Vector d) (X : Path d)
    (ht : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) (N : ℕ) :
    ∃ n, N < n ∧ StrictRecord ℓ X n := by
  classical
  let b := ∑ j ∈ Finset.range (N + 1), |dot (realPosition (X j)) ℓ|
  have hb (j : ℕ) (hj : j ≤ N) : dot (realPosition (X j)) ℓ ≤ b := by
    apply (le_abs_self _).trans
    exact Finset.single_le_sum (f := fun j => |dot (realPosition (X j)) ℓ|)
      (fun k _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have he : ∃ n, b < dot (realPosition (X n)) ℓ :=
    Filter.Eventually.exists (show ∀ᶠ n : ℕ in atTop, b < dot (realPosition (X n)) ℓ from
      ht (eventually_gt_atTop b))
  refine ⟨Nat.find he, ?_, ?_⟩
  · by_contra hh
    exact (not_lt_of_ge (hb (Nat.find he) (by omega))) (Nat.find_spec he)
  · intro j hj
    exact (le_of_not_gt (Nat.find_min he hj)).trans_lt (Nat.find_spec he)

end DirectionalTransience
end
end

end OAI
