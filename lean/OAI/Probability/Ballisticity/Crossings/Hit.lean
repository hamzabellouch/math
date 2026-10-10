import Mathlib
import OAI.Probability.Ballisticity.Estimates.StayUntil

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def HitAt {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  {X | X n ∈ T ∧ ∀ i < n, X i ∈ S}

def Hit {d : ℕ} (S T : Set (Lattice d)) : Set (Path d) := ⋃ n, HitAt S T n

lemma measurableSet_hitAt {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    MeasurableSet (HitAt S T n) := by
  apply MeasurableSet.inter ((measurable_pi_apply n) T.to_countable.measurableSet)
  change MeasurableSet {X : Path d | ∀ i < n, X i ∈ S}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma measurableSet_hit {d : ℕ} (S T : Set (Lattice d)) : MeasurableSet (Hit S T) :=
  MeasurableSet.iUnion (measurableSet_hitAt S T)

lemma hitAt_pairwise_disjoint {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) :
    Pairwise (fun n m => Disjoint (HitAt S T n) (HitAt S T m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro X hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact Set.disjoint_left.mp hST (hm.2 n h) hn.1
  · exact Set.disjoint_left.mp hST (hn.2 m h) hm.1

noncomputable def hitKernel {d : ℕ} (S T : Set (Lattice d)) : Kernel (State d) (Lattice d) :=
  Kernel.sum fun n => (quenchedKernel.restrict (measurableSet_hitAt S T n)).map (fun X => X n)

lemma hitKernel_apply {d : ℕ} (S T U : Set (Lattice d)) (z : State d) :
    hitKernel S T z U = ∑' n, quenchedKernel z (HitAt S (T ∩ U) n) := by
  rw [hitKernel, Kernel.sum_apply' _ _ U.to_countable.measurableSet]
  apply tsum_congr
  intro n
  rw [Kernel.map_apply' _ (measurable_pi_apply n) _ U.to_countable.measurableSet,
    Kernel.restrict_apply' _ _ _ ((measurable_pi_apply n) U.to_countable.measurableSet)]
  congr 1
  ext X
  simp only [Set.mem_inter_iff, Set.mem_preimage, HitAt, Set.mem_ofPred_eq]
  tauto

lemma hitKernel_total {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) (z : State d) :
    hitKernel S T z Set.univ = quenchedKernel z (Hit S T) := by
  rw [hitKernel_apply, Set.inter_univ]
  exact (measure_iUnion (hitAt_pairwise_disjoint hST) (measurableSet_hitAt S T)).symm

lemma hitKernel_total_le_one {d : ℕ} {S T : Set (Lattice d)} (hST : Disjoint S T) (z : State d) :
    hitKernel S T z Set.univ ≤ 1 := by
  rw [hitKernel_total hST]
  exact prob_le_one

lemma quenched_hitAt_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    quenchedKernel (ω, x) (HitAt S T n ∩ FutureEvent B n) =
      ∫⁻ X in HitAt S T n, quenchedKernel (ω, X n) (B (X n)) ∂quenchedKernel (ω, x) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | f ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ T ∧ ∀ i : Finset.Iic n, (i : ℕ) < n → f i ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = HitAt S T n := by
    ext X
    constructor
    · intro h
      exact ⟨h.1, fun i hi => h.2 ⟨i, Finset.mem_Iic.mpr hi.le⟩ hi⟩
    · intro h
      exact ⟨h.1, fun i hi => h.2 i hi⟩
  simpa only [hC] using quenched_past_future ω x n C B hB

lemma hitKernel_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    (∫⁻ y, quenchedKernel (ω, y) (B y) ∂hitKernel S T (ω, x)) =
      quenchedKernel (ω, x) (⋃ n, HitAt S T n ∩ FutureEvent B n) := by
  rw [hitKernel, Kernel.sum_apply, lintegral_sum_measure]
  rw [measure_iUnion (fun n m hnm => (hitAt_pairwise_disjoint hST hnm).mono
    Set.inter_subset_left Set.inter_subset_left)
    (fun n => (measurableSet_hitAt S T n).inter (measurableSet_futureEvent B hB n))]
  apply tsum_congr
  intro n
  rw [Kernel.map_apply _ (measurable_pi_apply n),
    lintegral_map (measurable_of_countable _) (measurable_pi_apply n), Kernel.restrict_apply]
  exact (quenched_hitAt_future ω x S T n B hB).symm

lemma hitKernel_noDrop_le {d : ℕ} (ω : Environment d) (x : Lattice d) (ℓ : Vector d)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hS : ∀ y ∈ S, dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ)
    (hT : ∀ y ∈ T, dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ) :
    (∫⁻ y, noDropQuenched ℓ y ω ∂hitKernel S T (ω, x)) ≤ noDropQuenched ℓ x ω := by
  unfold noDropQuenched
  rw [hitKernel_future ω x hST (NoDrop ℓ) (measurableSet_noDrop ℓ)]
  apply measure_mono
  intro X hX
  obtain ⟨n, hn, hF⟩ := Set.mem_iUnion.mp hX
  intro i
  by_cases hi : i < n
  · exact hS _ (hn.2 i hi)
  · have hni : n ≤ i := by omega
    have hh := hF (i - n)
    dsimp only at hh
    rw [Nat.add_sub_of_le hni] at hh
    exact (hT _ hn.1).trans hh

def Cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Path d) :=
  {X | ∃ n, dot (realPosition x) ℓ + H ≤ dot (realPosition (X n)) ℓ ∧
    ∀ i < n, dot (realPosition x) ℓ ≤ dot (realPosition (X i)) ℓ}

def Strip {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ ∧
    dot (realPosition y) ℓ < dot (realPosition x) ℓ + H}

def Upper {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) : Set (Lattice d) :=
  {y | dot (realPosition x) ℓ + H ≤ dot (realPosition y) ℓ}

lemma disjoint_strip_upper {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Disjoint (Strip ℓ x H) (Upper ℓ x H) := by
  apply Set.disjoint_left.mpr
  intro y hy hu
  exact (not_lt_of_ge hu) hy.2

lemma cross_eq_hit {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Cross ℓ x H = Hit (Strip ℓ x H) (Upper ℓ x H) := by
  classical
  ext X
  constructor
  · rintro ⟨n, hn, hp⟩
    have hex : ∃ k, dot (realPosition x) ℓ + H ≤ dot (realPosition (X k)) ℓ := ⟨n, hn⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro i hi
    refine ⟨hp i (hi.trans_le (Nat.find_min' hex hn)), ?_⟩
    exact lt_of_not_ge (Nat.find_min hex hi)
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact ⟨n, hn.1, fun i hi => (hn.2 i hi).1⟩

lemma measurableSet_cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    MeasurableSet (Cross ℓ x H) := by
  rw [cross_eq_hit]
  exact measurableSet_hit _ _

lemma cross_antitone {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Antitone (Cross ℓ x) := by
  intro H K hHK X hX
  obtain ⟨n, hn, hp⟩ := hX
  exact ⟨n, (add_le_add_right hHK _).trans hn, hp⟩

lemma iInter_cross_subset_noDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    (⋂ H : ℕ, Cross ℓ x H) ⊆ NoDrop ℓ x := by
  intro X hX n
  by_contra hn
  have hbound : ∃ b : ℝ, ∀ i ≤ n, dot (realPosition (X i)) ℓ < b := by
    obtain ⟨b, hb⟩ := ((Finset.range (n + 1)).finite_toSet.image
      (fun i => dot (realPosition (X i)) ℓ)).bddAbove
    refine ⟨b + 1, fun i hi => ?_⟩
    have hbi := hb (Set.mem_image_of_mem _ (show i ∈ (Finset.range (n + 1) : Set ℕ) by
      simp only [Finset.mem_coe, Finset.mem_range]; omega))
    linarith
  obtain ⟨b, hb⟩ := hbound
  obtain ⟨H, hH⟩ := exists_nat_gt (b - dot (realPosition x) ℓ)
  obtain ⟨m, hm, hp⟩ := Set.mem_iInter.mp hX H
  by_cases hmn : m ≤ n
  · have hh := hb m hmn
    linarith
  · exact hn (hp n (by omega))

lemma noDrop_subset_cross_of_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (X : Path d) (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop)
    (hD : X ∈ NoDrop ℓ x) (H : ℝ) : X ∈ Cross ℓ x H := by
  obtain ⟨n, hn⟩ := (hX.eventually (eventually_ge_atTop (dot (realPosition x) ℓ + H))).exists
  exact ⟨n, hn, fun i _ => hD i⟩

def TransientPaths {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}

lemma measurableSet_transientPaths {d : ℕ} (ℓ : Vector d) :
    MeasurableSet (TransientPaths ℓ) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
    (measurable_pi_apply n)

lemma transientPaths_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    (fun X : Path d => fun n => X n - x) ⁻¹' TransientPaths ℓ = TransientPaths ℓ := by
  ext X
  constructor
  · intro h
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp h (b - dot (realPosition x) ℓ)] with n hn
    rw [dot_realPosition_sub] at hn
    linarith
  · intro h
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp h (b + dot (realPosition x) ℓ)] with n hn
    rw [dot_realPosition_sub]
    linarith

lemma quenched_directionallyTransient_ae {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x,
      ∀ᵐ X ∂quenchedKernel (ω, x), X ∈ TransientPaths ℓ := by
  apply ae_all_iff.mpr
  intro x
  have hm : MeasurableSet (TransientPaths ℓ)ᶜ := (measurableSet_transientPaths ℓ).compl
  have he (ω : Environment d) : quenchedKernel (ω, x) (TransientPaths ℓ)ᶜ =
      quenchedKernel ((fun a => ω (x + a)), 0) (TransientPaths ℓ)ᶜ := by
    have h := congrArg (fun μ : Measure (Path d) => μ (TransientPaths ℓ)ᶜ)
      (quenched_translation ω x 0)
    rw [Measure.map_apply (by fun_prop) hm, Set.preimage_compl,
      transientPaths_translation] at h
    simpa only [add_zero] using h
  have hz : (∫⁻ ω, quenchedKernel (ω, x) (TransientPaths ℓ)ᶜ ∂environmentLaw ν) = 0 := by
    simp_rw [he]
    have hm0 : Measurable (fun ω : Environment d => quenchedKernel (ω, 0) (TransientPaths ℓ)ᶜ) :=
      (Kernel.measurable_coe _ hm).comp (measurable_id.prodMk measurable_const)
    rw [← lintegral_map hm0 (show Measurable (fun ω : Environment d => fun a => ω (x + a)) by
      fun_prop), environment_translation]
    rw [← annealed_apply ν hm]
    exact ae_iff.mp htrans
  have hzero := (lintegral_eq_zero_iff ((Kernel.measurable_coe _ hm).comp
    (measurable_id.prodMk measurable_const))).mp hz
  filter_upwards [hzero] with ω hω
  exact ae_iff.mpr hω

noncomputable def crossingQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) : ℝ≥0∞ := quenchedKernel (ω, x) (Cross ℓ x H)

lemma crossingQuenched_antitone {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    Antitone (fun H => crossingQuenched ℓ x H ω) := by
  intro H K hHK
  exact measure_mono (cross_antitone ℓ x hHK)

lemma crossingQuenched_tendsto_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x,
      Tendsto (fun H : ℕ => crossingQuenched ℓ x H ω) atTop (𝓝 (noDropQuenched ℓ x ω)) := by
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  intro x
  have he : (⋂ H : ℕ, Cross ℓ x H) =ᵐ[quenchedKernel (ω, x)] NoDrop ℓ x := by
    filter_upwards [hω x] with X hX
    apply propext
    constructor
    · exact fun h => iInter_cross_subset_noDrop ℓ x h
    · intro hD
      exact Set.mem_iInter.mpr fun H => noDrop_subset_cross_of_tendsto ℓ x X hX hD H
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun H : ℕ => Cross ℓ x H)
    (fun H => (measurableSet_cross ℓ x H).nullMeasurableSet)
    (fun H K hHK => cross_antitone ℓ x (Nat.cast_le.mpr hHK))
    ⟨0, measure_ne_top _ _⟩
  rw [measure_congr he] at h
  exact h

lemma quenched_hitAt_congr {d : ℕ} (S T : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) (n : ℕ) :
    quenchedKernel (ω, x) (HitAt S T n) = quenchedKernel (η, x) (HitAt S T n) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | f ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ T ∧ ∀ i : Finset.Iic n, (i : ℕ) < n → f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = HitAt S T n := by
    ext X
    constructor
    · intro h
      exact ⟨h.1, fun i hi => h.2 ⟨i, Finset.mem_Iic.mpr hi.le⟩ hi⟩
    · intro h
      exact ⟨h.1, fun i hi => h.2 i hi⟩
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
    have hin : i < n := Finset.mem_range.mp hi
    have hiS : extendPrefix n f.val i ∈ S := by
      rw [extendPrefix_apply _ _ _ hin.le]
      exact f.property.2 _ hin
    simp only [edgeWeight, hωη hiS]
  · rw [quenched_pathCylinder_zero _ _ _ hf, quenched_pathCylinder_zero _ _ _ hf]

lemma hitKernel_congr {d : ℕ} (S T : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    hitKernel S T (ω, x) = hitKernel S T (η, x) := by
  apply Measure.ext
  intro U _
  rw [hitKernel_apply, hitKernel_apply]
  exact tsum_congr fun n => quenched_hitAt_congr S (T ∩ U) ω η hωη x n

lemma measurable_hitKernel_rows {d : ℕ} (S T : Set (Lattice d)) (x : Lattice d) (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => hitKernel S T (ω, x)) := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have hm : Measurable (fun η : Environment d => hitKernel S T (η, x)) :=
    (hitKernel S T).measurable.comp (measurable_id.prodMk measurable_const)
  have he : (fun ω : Environment d => hitKernel S T (ω, x)) =
      (fun η : Environment d => hitKernel S T (η, x)) ∘ patch := by
    funext ω
    exact hitKernel_congr S T ω (patch ω) (fun y hy => by simp [patch, hy]) x
  rw [he]
  exact hm.comp hp

lemma crossingQuenched_eq_hitKernel {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = hitKernel (Strip ℓ x H) (Upper ℓ x H) (ω, x) Set.univ := by
  rw [hitKernel_total (disjoint_strip_upper ℓ x H), crossingQuenched, cross_eq_hit]

lemma measurable_crossingQuenched_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {H : ℝ} (hH : 0 < H) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (crossingQuenched ℓ x H) := by
  change @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (fun ω => crossingQuenched ℓ x H ω)
  simp_rw [crossingQuenched_eq_hitKernel]
  exact (Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_hitKernel_rows _ _ x ⟨le_rfl, by linarith⟩)

lemma crossingQuenched_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    crossingQuenched ℓ x 0 ω = 1 := by
  have he : Cross ℓ x 0 =ᵐ[quenchedKernel (ω, x)] Set.univ := by
    filter_upwards [quenched_initial_ae (ω, x)] with X hX
    apply propext
    change X ∈ Cross ℓ x 0 ↔ True
    refine ⟨fun _ => trivial, fun _ => ⟨0, ?_, by simp⟩⟩
    simp [hX]
  rw [crossingQuenched, measure_congr he, measure_univ]

lemma crossingQuenched_lower_step {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (e : Direction d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) {H : ℝ} (hH : 0 ≤ H) :
    (κ : ℝ≥0∞) * crossingQuenched ℓ x H ω ≤
      crossingQuenched ℓ x (H + dot (realPosition (step e)) ℓ) ω := by
  let S := Strip ℓ x H
  let T := Upper ℓ x H
  let B := fun y : Lattice d => wordCylinder y [e]
  have hB (y : Lattice d) : MeasurableSet (B y) := measurableSet_wordCylinder y [e]
  have hInt : (κ : ℝ≥0∞) * hitKernel S T (ω, x) Set.univ ≤
      ∫⁻ y, quenchedKernel (ω, y) (B y) ∂hitKernel S T (ω, x) := by
    rw [← lintegral_const]
    apply lintegral_mono
    intro y
    change _ ≤ quenchedKernel (ω, y) (wordCylinder y [e])
    rw [quenched_wordCylinder]
    simpa [wordWeight] using (ENNReal.coe_le_coe.mpr (hκ y))
  rw [hitKernel_future ω x (disjoint_strip_upper ℓ x H) B hB] at hInt
  rw [crossingQuenched_eq_hitKernel ℓ x H]
  refine hInt.trans (measure_mono ?_)
  intro X hX
  obtain ⟨n, hn, hF⟩ := Set.mem_iUnion.mp hX
  have hn1 : X (n + 1) = X n + step e := hF 1 (by simp)
  refine ⟨n + 1, ?_, ?_⟩
  · rw [hn1, dot_realPosition_add]
    have ht : dot (realPosition x) ℓ + H ≤ dot (realPosition (X n)) ℓ := hn.1
    linarith
  · intro i hi
    rcases lt_or_eq_of_le (show i ≤ n by omega) with hi | rfl
    · exact (hn.2 i hi).1
    · exact (le_add_of_nonneg_right hH).trans hn.1

lemma mass_of_small_mean {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    {s : ℝ≥0} (hs : 0 < s) (hmean : (∫⁻ a, f a ∂μ) ≤ (s : ℝ≥0∞)) :
    (1 : ℝ≥0∞) ≤ 2 * μ {a | f a ≤ 2 * (s : ℝ≥0∞)} := by
  let B := {a | f a ≤ 2 * (s : ℝ≥0∞)}
  let G := {a | 2 * (s : ℝ≥0∞) ≤ f a}
  have hcover : (1 : ℝ≥0∞) ≤ μ B + μ G := by
    calc
      1 = μ Set.univ := (measure_univ).symm
      _ ≤ μ (B ∪ G) := measure_mono (fun a _ => le_total (f a) (2 * (s : ℝ≥0∞)))
      _ ≤ μ B + μ G := measure_union_le _ _
  have hmark : (2 * (s : ℝ≥0∞)) * μ G ≤ (s : ℝ≥0∞) :=
    (mul_meas_ge_le_lintegral₀ hf.aemeasurable _).trans hmean
  have hc := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ B, measure_ne_top μ G⟩) hcover
  have hm := ENNReal.toReal_mono ENNReal.coe_ne_top hmark
  rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top μ B) (measure_ne_top μ G)] at hc
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hm
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ B))).mp
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  change 1 ≤ 2 * (μ B).toReal
  nlinarith

noncomputable def endpointLaw {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) : Measure (Lattice d) :=
  (crossingQuenched ℓ x H ω)⁻¹ • hitKernel (Strip ℓ x H) (Upper ℓ x H) (ω, x)

lemma crossingQuenched_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω ≤ 1 := prob_le_one

lemma crossingQuenched_ne_top {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (crossingQuenched_le_one ℓ x H ω)

lemma endpointLaw_total {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d)
    (ha : crossingQuenched ℓ x H ω ≠ 0) : endpointLaw ℓ x H ω Set.univ = 1 := by
  rw [endpointLaw, Measure.smul_apply, smul_eq_mul, ← crossingQuenched_eq_hitKernel,
    ENNReal.inv_mul_cancel ha (crossingQuenched_ne_top ℓ x H ω)]

lemma endpointLaw_total_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    endpointLaw ℓ x H ω Set.univ ≤ 1 := by
  by_cases ha : crossingQuenched ℓ x H ω = 0
  · rw [endpointLaw, Measure.smul_apply, smul_eq_mul, ← crossingQuenched_eq_hitKernel, ha, mul_zero]
    exact zero_le
  · rw [endpointLaw_total ℓ x H ω ha]

lemma endpointLaw_mean_le {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 ≤ H)
    (ω : Environment d) :
    (∫⁻ y, noDropQuenched ℓ y ω ∂endpointLaw ℓ x H ω) ≤
      noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω := by
  rw [endpointLaw, lintegral_smul_measure, smul_eq_mul, ENNReal.div_eq_inv_mul]
  apply mul_le_mul_right
  exact hitKernel_noDrop_le ω x ℓ (disjoint_strip_upper ℓ x H)
    (fun _ hy => hy.1) (fun _ hy => (le_add_of_nonneg_right hH).trans hy)

end DirectionalTransience
end
end

end OAI
