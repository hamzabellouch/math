import Mathlib
import OAI.Probability.Ballisticity.Estimates.WordDepartures

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def StayUntil {d : ℕ} (S : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i ∈ S}

def Stay {d : ℕ} (S : Set (Lattice d)) : Set (Path d) :=
  {X | ∀ i, X i ∈ S}

lemma measurableSet_stayUntil {d : ℕ} (S : Set (Lattice d)) (n : ℕ) :
    MeasurableSet (StayUntil S n) := by
  simp only [StayUntil, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma measurableSet_stay {d : ℕ} (S : Set (Lattice d)) :
    MeasurableSet (Stay S) := by
  simp only [Stay, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma restrict_prefix_fiber {d : ℕ} (n : ℕ)
    (f : (i : Finset.Iic n) → Lattice d) :
    (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f} =
      pathCylinder (extendPrefix n f) n := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · intro hh i hi
    simpa [extendPrefix, hi] using congrFun hh ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro hh
    funext i
    simpa [extendPrefix, Finset.mem_Iic.mp i.2] using hh i (Finset.mem_Iic.mp i.2)

lemma quenched_stayUntil_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) (n : ℕ) :
    quenchedKernel (ω, x) (StayUntil S n) = quenchedKernel (η, x) (StayUntil S n) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = StayUntil S n := by
    ext X
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h i
      exact h i (Finset.mem_Iic.mp i.2)
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ A) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← hA, ← tsum_measure_preimage_singleton A.to_countable hm,
    ← tsum_measure_preimage_singleton A.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  by_cases hf : extendPrefix n f.val 0 = x
  · rw [quenched_pathCylinder _ _ _ hf, quenched_pathCylinder _ _ _ hf]
    apply Finset.prod_congr rfl
    intro i hi
    have hie : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hiS : extendPrefix n f.val i ∈ S := by
      rw [extendPrefix_apply _ _ _ hie]
      exact f.property _
    simp only [edgeWeight, hωη hiS]
  · rw [quenched_pathCylinder_zero _ _ _ hf, quenched_pathCylinder_zero _ _ _ hf]

lemma quenched_stay_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    quenchedKernel (ω, x) (Stay S) = quenchedKernel (η, x) (Stay S) := by
  have hS : Stay S = ⋂ n, StayUntil S n := by
    ext X
    simp only [Stay, StayUntil, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h _ i _ => h i, fun h i => h i i le_rfl⟩
  have hm : Antitone (StayUntil S) := fun m n hmn X hX i hi => hX i (hi.trans hmn)
  rw [hS, hm.measure_iInter (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩,
    hm.measure_iInter (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  congr 1
  funext n
  exact quenched_stayUntil_congr S ω η hωη x n

lemma measurable_stay_rows {d : ℕ} (S : Set (Lattice d)) (x : Lattice d) (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => quenchedKernel (ω, x) (Stay S)) := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have hm : Measurable (fun η : Environment d => quenchedKernel (η, x) (Stay S)) :=
    (Kernel.measurable_coe _ (measurableSet_stay S)).comp
      (measurable_id.prodMk measurable_const)
  have he : (fun ω : Environment d => quenchedKernel (ω, x) (Stay S)) =
      (fun η : Environment d => quenchedKernel (η, x) (Stay S)) ∘ patch := by
    funext ω
    exact quenched_stay_congr S ω (patch ω) (fun y hy => by simp [patch, hy]) x
  rw [he]
  exact hm.comp hp

lemma measurable_noDropQuenched_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    @Measurable _ _ (rowSigma {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ}) _
      (noDropQuenched ℓ x) :=
  measurable_stay_rows {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} x
    (show dot (realPosition x) ℓ ≤ dot (realPosition x) ℓ from le_rfl)

lemma noDropQuenched_lower_step {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (e : Direction d) (he : 0 ≤ dot (realPosition (step e)) ℓ) :
    ((ω x).1 e : ℝ≥0∞) * noDropQuenched ℓ (x + step e) ω ≤ noDropQuenched ℓ x ω := by
  let f := wordPath x [e]
  have hm := quenched_prefix_future ω x f (by simp [f]) 1
    (measurableSet_noDrop ℓ (x + step e))
  have hf1 : f 1 = x + step e := by simp [f, wordPath]
  rw [hf1] at hm
  have hcy : pathCylinder f 1 = wordCylinder x [e] := rfl
  rw [hcy, quenched_wordCylinder] at hm
  have hw : ENNReal.ofReal (wordWeight ω x [e]) = ((ω x).1 e : ℝ≥0∞) := by
    simp [wordWeight]
  rw [hw] at hm
  unfold noDropQuenched
  rw [← hm]
  apply measure_mono
  intro X hX n
  rcases n with _ | n
  · simpa only [show X 0 = x from hX.2 0 (by simp)] using
      (le_refl (dot (realPosition x) ℓ))
  · have ht := hX.1 n
    change dot (realPosition (x + step e)) ℓ ≤ dot (realPosition (X (1 + n))) ℓ at ht
    rw [dot_realPosition_add] at ht
    simpa only [Nat.add_comm 1 n] using (le_trans (le_add_of_nonneg_right he) ht)

lemma dot_realPosition_nsmul {d : ℕ} (n : ℕ) (x : Lattice d) (ℓ : Vector d) :
    dot (realPosition (n • x)) ℓ = (n : ℝ) * dot (realPosition x) ℓ := by
  induction n with
  | zero => simp [dot, realPosition]
  | succ n ih =>
    rw [succ_nsmul, dot_realPosition_add, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma noDrop_positive_limsup {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (he : 0 < dot (realPosition (step e)) ℓ)
    (hp : 0 < annealedLaw ν (NoDrop ℓ 0)) :
    ∀ᵐ ω ∂environmentLaw ν,
      ω ∈ limsup (fun n : ℕ => {ω | 0 < noDropQuenched ℓ (n • step e) ω}) atTop := by
  let A : ℕ → Set (Environment d) := fun n => {ω | 0 < noDropQuenched ℓ (n • step e) ω}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt measurable_const (measurable_noDropQuenched ℓ _)
  have hsame (n : ℕ) : environmentLaw ν (A n) = environmentLaw ν (A 0) := by
    have hA : A n = (fun ω : Environment d => fun a => ω (n • step e + a)) ⁻¹' A 0 := by
      ext ω
      simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, zero_nsmul]
      rw [noDropQuenched_translation]
    rw [hA, ← Measure.map_apply (by fun_prop) (hAm 0), environment_translation]
  have hpos : 0 < environmentLaw ν (A 0) := by
    by_contra hn
    have hz : environmentLaw ν (A 0) = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hq : noDropQuenched ℓ 0 =ᵐ[environmentLaw ν] 0 := by
      apply ae_iff.mpr
      simpa only [A, zero_nsmul, pos_iff_ne_zero, Pi.zero_apply] using hz
    have hi := (lintegral_eq_zero_iff (measurable_noDropQuenched ℓ 0)).mpr hq
    rw [annealed_noDrop_translation] at hi
    exact (ne_of_gt hp) hi
  have htail : ∀ S ∈ (cofinite : Filter (Lattice d)),
      MeasurableSet[rowSigma S] (limsup A atTop) := by
    intro S hS
    have hfin : Sᶜ.Finite := mem_cofinite.mp hS
    obtain ⟨B, hB⟩ := (hfin.image (fun y => dot (realPosition y) ℓ)).bddAbove
    have ht : Tendsto (fun n : ℕ => dot (realPosition (n • step e)) ℓ) atTop atTop := by
      simp_rw [dot_realPosition_nsmul]
      exact tendsto_natCast_atTop_atTop.atTop_mul_const he
    obtain ⟨k, hk⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop B))
    rw [← limsup_nat_add A k]
    apply @MeasurableSet.measurableSet_limsup _ (rowSigma S)
    intro n
    apply measurableSet_lt measurable_const
    apply (measurable_noDropQuenched_rows ℓ ((n + k) • step e)).mono _ le_rfl
    apply rowSigma_mono
    intro y hy
    by_contra hyS
    have hBy : dot (realPosition y) ℓ ≤ B := hB ⟨y, hyS, rfl⟩
    exact (not_le_of_gt (hk (n + k) (Nat.le_add_left k n))) (le_trans hy hBy)
  have hEpos : 0 < environmentLaw ν (limsup A atTop) := by
    apply lt_of_lt_of_le hpos
    rw [limsup_eq_iInf_iSup_of_nat]
    change environmentLaw ν (A 0) ≤ environmentLaw ν (⋂ n, ⋃ i ≥ n, A i)
    have ha : Antitone (fun n => ⋃ i ≥ n, A i) := by
      intro n m hnm ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨i, hi, hω⟩ := hω
      exact ⟨i, le_trans hnm hi, hω⟩
    rw [ha.measure_iInter (fun n => (MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => hAm i).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    apply le_iInf
    intro n
    rw [← hsame n]
    exact measure_mono (Set.subset_iUnion_of_subset n (Set.subset_iUnion_of_subset le_rfl le_rfl))
  have hEone := (environment_tail_zero_one ν htail).resolve_left (ne_of_gt hEpos)
  exact ae_iff.mpr ((prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hAm)).mpr hEone)

lemma noDropQuenched_positive_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ)
    (hp : 0 < annealedLaw ν (NoDrop ℓ 0)) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x, 0 < noDropQuenched ℓ x ω := by
  have h0 : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω := by
    obtain ⟨κ, hκ, hκae⟩ := environment_uniform_elliptic ν hue
    filter_upwards [hκae, noDrop_positive_limsup ν ℓ e he hp] with ω hω hE
    obtain ⟨n, hn⟩ := (mem_limsup_iff_frequently_mem.mp hE).exists
    have htransfer : ∀ n : ℕ, 0 < noDropQuenched ℓ (n • step e) ω →
        0 < noDropQuenched ℓ 0 ω := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        apply ih
        apply lt_of_lt_of_le _ (noDropQuenched_lower_step ℓ ω (n • step e) e he.le)
        apply ENNReal.mul_pos
        · apply ne_of_gt
          exact_mod_cast (lt_of_lt_of_le hκ (hω (n • step e) e))
        · simpa only [succ_nsmul] using ne_of_gt hn
    exact htransfer n hn
  apply ae_all_iff.mpr
  intro x
  have ht : Measurable (fun ω : Environment d => fun a => ω (x + a)) := by fun_prop
  have hm := environment_translation ν x
  have hmap : ∀ᵐ ω ∂(environmentLaw ν).map (fun η : Environment d => fun a => η (x + a)),
      0 < noDropQuenched ℓ 0 ω := by rwa [hm]
  have ha := (ae_map_iff ht.aemeasurable ((measurable_noDropQuenched ℓ 0) measurableSet_Ioi)).mp hmap
  filter_upwards [ha] with ω hω
  simpa only [noDropQuenched_translation ℓ ω x, Set.mem_Ioi] using hω

lemma annealed_record_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d))
    (hrecord : ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ) :
    annealedLaw ν ((fun X : Path d => fun i => X (w.length + i)) ⁻¹'
      NoDrop ℓ (wordPath 0 w w.length) ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * annealedLaw ν (NoDrop ℓ 0) := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w)
  let T : Set (Lattice d) := {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_le_of_gt (hrecord z hz)) hz'
  have hw (ω : Environment d) : quenchedKernel (ω, 0)
      ((fun X : Path d => fun i => X (w.length + i)) ⁻¹' NoDrop ℓ y ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * noDropQuenched ℓ y ω := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length
      (measurableSet_noDrop ℓ y)
    change quenchedKernel (ω, 0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω, 0) (wordCylinder 0 w) * noDropQuenched ℓ y ω at hh
    rwa [quenched_wordCylinder] at hh
  rw [annealed_apply ν (((by fun_prop : Measurable (fun X : Path d => fun i => X (w.length + i))))
    (measurableSet_noDrop ℓ y) |>.inter (measurableSet_wordCylinder 0 w))]
  simp_rw [hw]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((measurable_wordWeight_on 0 w (fun _ hz => hz)).ennreal_ofReal)
    (measurable_noDropQuenched_rows ℓ y)]
  rw [← annealed_wordCylinder, annealed_noDrop_translation]

lemma quenched_futureNoDrop_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (hzero : ∀ y, noDropQuenched ℓ y ω = 0) (n : ℕ) :
    quenchedKernel (ω, x) (FutureNoDrop ℓ n) = 0 := by
  let E := fun f : (i : Finset.Iic n) → Lattice d =>
    (fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (extendPrefix n f n) ∩
      pathCylinder (extendPrefix n f) n
  have hE (f : (i : Finset.Iic n) → Lattice d) : quenchedKernel (ω, x) (E f) = 0 := by
    by_cases hf : extendPrefix n f 0 = x
    · change quenchedKernel (ω, x) (_ ∩ _) = 0
      rw [quenched_prefix_future ω x _ hf n (measurableSet_noDrop _ _)]
      change _ * noDropQuenched ℓ _ ω = 0
      rw [hzero, mul_zero]
    · apply measure_mono_null Set.inter_subset_right
      exact quenched_pathCylinder_zero ω x _ hf n
  apply measure_mono_null (t := ⋃ f, E f) _ (measure_iUnion_null hE)
  intro X hX
  apply Set.mem_iUnion.mpr
  refine ⟨fun i => X i, ?_⟩
  constructor
  · change ∀ j, dot (realPosition (extendPrefix n (fun i => X i) n)) ℓ ≤
        dot (realPosition (X (n + j))) ℓ
    simpa [extendPrefix, FutureNoDrop] using hX
  · intro i hi
    simp [extendPrefix, hi]

lemma noDrop_positive_of_directionallyTransient {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    0 < annealedLaw ν (NoDrop ℓ 0) := by
  by_contra hn
  have hzero : annealedLaw ν (NoDrop ℓ 0) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hq : ∀ᵐ ω ∂environmentLaw ν, ∀ x, noDropQuenched ℓ x ω = 0 := by
    apply ae_all_iff.mpr
    intro x
    apply (lintegral_eq_zero_iff (measurable_noDropQuenched ℓ x)).mp
    rw [annealed_noDrop_translation ν ℓ x, hzero]
  have hnzero (n : ℕ) : annealedLaw ν (FutureNoDrop ℓ n) = 0 := by
    rw [annealed_apply ν (measurableSet_futureNoDrop ℓ n)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hq] with ω hω
    exact quenched_futureNoDrop_zero ℓ ω 0 hω n
  have hnone : ∀ᵐ X ∂annealedLaw ν, ∀ n, X ∉ FutureNoDrop ℓ n := by
    apply ae_all_iff.mpr
    intro n
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnzero n
  have hfalse : ∀ᵐ X ∂annealedLaw ν, False := by
    filter_upwards [htrans, hnone] with X ht hh
    obtain ⟨n, hn⟩ := tendsto_atTop_has_minimum _ ht
    exact hh n (fun i => hn (n + i))
  obtain ⟨X, hX⟩ := hfalse.exists
  exact hX

lemma measure_partition_prefix {d : ℕ} (μ : Measure (Path d)) (A : Set (Path d)) (n : ℕ) :
    μ A = ∑' f : (i : Finset.Iic n) → Lattice d, μ (A ∩ pathCylinder (extendPrefix n f) n) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict A)
    (s := Set.univ) (Set.to_countable _) (f := fun X : Path d => Preorder.frestrictLe n X)
    (fun f _ => (Preorder.measurable_frestrictLe n) (measurableSet_singleton f))
  simp only [Set.preimage_univ, Measure.restrict_apply
    MeasurableSet.univ, Set.univ_inter] at h
  rw [tsum_subtype Set.univ (fun f => (μ.restrict A)
    ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f})), Set.indicator_univ] at h
  rw [← h]
  apply tsum_congr
  intro f
  rw [Measure.restrict_apply ((Preorder.measurable_frestrictLe n) (measurableSet_singleton f)),
    restrict_prefix_fiber, Set.inter_comm]

lemma lintegral_partition_prefix {d : ℕ} (μ : Measure (Path d)) (A : Set (Path d))
    (n : ℕ) (g : ((i : Finset.Iic n) → Lattice d) → ℝ≥0∞) :
    (∫⁻ X in A, g (Preorder.frestrictLe n X) ∂μ) =
      ∑' f : (i : Finset.Iic n) → Lattice d,
        g f * μ (A ∩ pathCylinder (extendPrefix n f) n) := by
  rw [← lintegral_map (measurable_of_countable g) (Preorder.measurable_frestrictLe n),
    lintegral_countable']
  apply tsum_congr
  intro f
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton f),
    Measure.restrict_apply ((Preorder.measurable_frestrictLe n) (measurableSet_singleton f)),
    restrict_prefix_fiber, Set.inter_comm]

def FutureEvent {d : ℕ} (B : Lattice d → Set (Path d)) (n : ℕ) : Set (Path d) :=
  {X | (fun j => X (n + j)) ∈ B (X n)}

lemma measurableSet_futureEvent {d : ℕ} (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) (n : ℕ) : MeasurableSet (FutureEvent B n) := by
  have he : FutureEvent B n = ⋃ y, {X : Path d | X n = y} ∩
      (fun X : Path d => fun j => X (n + j)) ⁻¹' B y := by
    ext X
    simp only [FutureEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨X n, rfl, h⟩
    · rintro ⟨y, rfl, h⟩
      exact h
  rw [he]
  apply MeasurableSet.iUnion
  intro y
  exact (measurableSet_eq_fun (measurable_pi_apply n) measurable_const).inter
    ((by fun_prop : Measurable (fun X : Path d => fun j => X (n + j))) (hB y))

lemma quenched_past_future {d : ℕ} (ω : Environment d) (x : Lattice d) (n : ℕ)
    (C : Set ((i : Finset.Iic n) → Lattice d)) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    quenchedKernel (ω, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C ∩ FutureEvent B n) =
      ∫⁻ X in (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C,
        quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x) := by
  classical
  let Q := fun X : Path d => Preorder.frestrictLe n X
  let g := fun f : (i : Finset.Iic n) → Lattice d =>
    quenchedKernel (ω, extendPrefix n f n) (B (extendPrefix n f n))
  have hr : (∫⁻ X in Q ⁻¹' C, quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x)) =
      ∑' f : (i : Finset.Iic n) → Lattice d,
        g f * quenchedKernel (ω, x) (Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n) := by
    convert lintegral_partition_prefix (quenchedKernel (ω, x)) (Q ⁻¹' C) n g using 1
    apply lintegral_congr
    intro X
    simp [g, extendPrefix]
  rw [hr, measure_partition_prefix _ _ n]
  apply tsum_congr
  intro f
  have hcf (X : Path d) (hX : X ∈ pathCylinder (extendPrefix n f) n) : Q X = f := by
    rw [← restrict_prefix_fiber] at hX
    exact hX
  by_cases hC : f ∈ C
  · have hpc : Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n = pathCylinder (extendPrefix n f) n := by
      apply Set.inter_eq_right.mpr
      intro X hX
      change Q X ∈ C
      simpa only [hcf X hX] using hC
    have hfc : (Q ⁻¹' C ∩ FutureEvent B n) ∩ pathCylinder (extendPrefix n f) n =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' B (extendPrefix n f n) ∩
          pathCylinder (extendPrefix n f) n := by
      ext X
      constructor
      · rintro ⟨⟨_, hF⟩, hX⟩
        exact ⟨by simpa only [FutureEvent, Set.mem_ofPred_eq, Set.mem_preimage, ← hX n le_rfl] using hF, hX⟩
      · rintro ⟨hF, hX⟩
        refine ⟨⟨by change Q X ∈ C; simpa only [hcf X hX] using hC, ?_⟩, hX⟩
        change (fun j => X (n + j)) ∈ B (X n)
        simpa only [Set.mem_preimage, hX n le_rfl] using hF
    change quenchedKernel (ω, x) ((Q ⁻¹' C ∩ FutureEvent B n) ∩ _) = _
    rw [hpc, hfc]
    by_cases hf : extendPrefix n f 0 = x
    · rw [quenched_prefix_future ω x _ hf n (hB _)]
      exact mul_comm _ _
    · rw [quenched_pathCylinder_zero ω x _ hf, mul_zero]
      exact measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x _ hf n)
  · have hz : Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX, hcy⟩
      exact hC (by simpa only [Set.mem_preimage, hcf X hcy] using hX)
    change quenchedKernel (ω, x) ((Q ⁻¹' C ∩ FutureEvent B n) ∩ _) = _
    rw [hz, measure_empty, mul_zero]
    apply measure_mono_null (t := Q ⁻¹' C ∩ pathCylinder (extendPrefix n f) n)
      (by intro X hX; exact ⟨hX.1.1, hX.2⟩)
    rw [hz, measure_empty]

end DirectionalTransience
end
end

end OAI
