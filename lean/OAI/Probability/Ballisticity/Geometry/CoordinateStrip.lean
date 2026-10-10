import Mathlib
import OAI.Probability.Ballisticity.Estimates.LowerClip

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma integrable_log_sum
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {h : ℕ → α → ℝ} (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hm : ∀ j, AEMeasurable (h j) μ)
    (hint : ∀ j, Integrable (fun a => Real.log (1 + h j a)) μ) (n : ℕ) :
    Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  let Z : ℕ → α → ℝ := fun j a => Real.log (1 + h j a)
  have hup : Integrable (fun a => Real.log n + prefixMax (fun j => Z j a) n) μ :=
    (integrable_const _).add (integrable_prefixMax μ hint n)
  apply hup.mono'
    (Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun j _ => hm j))).aestronglyMeasurable
  filter_upwards [hh] with a ha
  simp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
    have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
    linarith))]
  exact log_sum_le_log_add_prefixMax _ ha hn0

lemma stationary_tail_growth_obstruction
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {c h : ℕ → α → ℝ} {X : ℕ → ℕ → α → ℝ} {Z : ℕ → ℕ → α → ℝ}
    (hcint : Integrable (c 0) μ)
    (hcid : ∀ j, IdentDistrib (c j) (c 0) μ μ)
    (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hhid : ∀ j, IdentDistrib (h j) (h 0) μ μ)
    (hhint : Integrable (fun a => Real.log (1 + h 0 a)) μ)
    (hXid : ∀ n R, IdentDistrib (X 0 R) (X n R) μ μ)
    (hXnonpos : ∀ n R, ∀ᵐ a ∂μ, X n R a ≤ 0)
    (hZint : ∀ n R, Integrable (Z n R) μ)
    (A C : ℝ)
    (hZmean : ∀ n, ∀ᶠ R : ℕ in atTop, (∫ a, Z n R a ∂μ) ≤ C)
    (hgrowth : ∀ n R, ∀ᵐ a ∂μ,
      (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a) - Z n R a - Real.log 2 ≤
          X n R a - X 0 R a) :
    (∫ a, c 0 a ∂μ) ≤ 0 := by
  have hcj (j : ℕ) : Integrable (c j) μ := (hcid j).integrable_iff.mpr hcint
  have hhj (j : ℕ) : Integrable (fun a => Real.log (1 + h j a)) μ :=
    ((hhid j).comp (Real.measurable_log.comp (measurable_const.add measurable_id))).integrable_iff.mpr hhint
  have hsumint (n : ℕ) : Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
    integrable_log_sum μ hh (fun j => (hhid j).aemeasurable_fst) hhj n
  have hbound (n : ℕ) : (n : ℝ) * (∫ a, c 0 a ∂μ) ≤
      A * (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) + C + Real.log 2 := by
    obtain ⟨R, hR⟩ := (hZmean n).exists
    have hcs : Integrable (fun a => ∑ j ∈ Finset.range n, c j a) μ :=
      integrable_finsetSum _ (fun j _ => hcj j)
    have h1 : Integrable (fun a => (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      hcs.sub ((hsumint n).const_mul A)
    have h2 : Integrable (fun a => (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a) - Z n R a) μ :=
      h1.sub (hZint n R)
    have h3 : Integrable (fun a => A * Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      (hsumint n).const_mul A
    have hG := h2.sub (integrable_const (Real.log 2))
    have hle := integral_le_zero_of_identDistrib_lower_bound μ (hXid n R)
      (hXnonpos 0 R) (hXnonpos n R) hG (hgrowth n R)
    simp only [Pi.sub_apply] at hle
    rw [integral_sub h2 (integrable_const (Real.log 2)),
      integral_sub h1 (hZint n R), integral_sub hcs h3, integral_const_mul,
      integral_finsetSum _ (fun j _ => hcj j)] at hle
    simp only [(hcid _).integral_eq, integral_const, probReal_univ, smul_eq_mul,
      one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    linarith
  have hlim :=
    ((integral_log_sum_div_tendsto_zero μ hh hhid hhint).const_mul A).add
      (tendsto_const_div_atTop_nhds_zero_nat (C + Real.log 2))
  simp only [mul_zero, add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← mul_div_assoc, ← add_div]
  apply (le_div_iff₀ hnpos).mpr
  nlinarith [hbound n]

lemma wordWeight_lower {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (x : Lattice d) (w : List (Direction d)) :
    (κ : ℝ) ^ w.length ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    simp only [List.length_cons, pow_succ', wordWeight]
    exact mul_le_mul (by exact_mod_cast hκ x e) (ih _)
      (pow_nonneg κ.coe_nonneg _) (NNReal.coe_nonneg _)

lemma wordPath_replicate {d : ℕ} (x : Lattice d) (e : Direction d) (N : ℕ) :
    wordPath x (List.replicate N e) N = x + N • step e := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    simp only [List.replicate_succ, wordPath, ih, succ_nsmul]
    abel

lemma stayUntil_split {d : ℕ} (S : Set (Lattice d)) (n m : ℕ) :
    StayUntil S (n + m) = StayUntil S n ∩ FutureEvent (fun _ => StayUntil S m) n := by
  ext X
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), fun j hj => h (n + j) (by omega)⟩
  · rintro ⟨h, h'⟩ i hi
    by_cases hin : i ≤ n
    · exact h i hin
    · have he : n + (i - n) = i := by omega
      simpa only [he] using h' (i - n) (by omega)

lemma quenched_stayUntil_add {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (n m : ℕ) :
    quenchedKernel (ω, x) (StayUntil S (n + m)) =
      ∫⁻ X in StayUntil S n, quenchedKernel (ω, X n) (StayUntil S m)
        ∂quenchedKernel (ω, x) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = StayUntil S n := by
    ext X
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h i
      exact h i (Finset.mem_Iic.mp i.2)
  rw [stayUntil_split, ← hA]
  exact quenched_past_future ω x n A (fun _ => StayUntil S m)
    (fun _ => measurableSet_stayUntil S m)

lemma quenched_stayUntil_block_bound {d : ℕ} (ω : Environment d)
    (S : Set (Lattice d)) (N : ℕ) (c : ℝ≥0∞)
    (hc : ∀ y, quenchedKernel (ω, y) (StayUntil S N) ≤ c)
    (x : Lattice d) (k : ℕ) :
    quenchedKernel (ω, x) (StayUntil S (k * N)) ≤ c ^ k := by
  induction k with
  | zero => simpa using (prob_le_one (μ := quenchedKernel (ω, x)) (s := StayUntil S 0))
  | succ k ih =>
    rw [Nat.succ_mul, quenched_stayUntil_add]
    calc
      _ ≤ ∫⁻ _ in StayUntil S (k * N), c ∂quenchedKernel (ω, x) :=
        lintegral_mono fun X => hc (X (k * N))
      _ = c * quenchedKernel (ω, x) (StayUntil S (k * N)) := by simp
      _ ≤ c * c ^ k := mul_le_mul' le_rfl ih
      _ = c ^ (k + 1) := (pow_succ' c k).symm

def CoordinateStrip {d : ℕ} (i : Fin d) (b : ℤ) (H : ℕ) : Set (Lattice d) :=
  {x | b ≤ x i ∧ x i < b + (H : ℤ)}

lemma wordCylinder_up_disjoint_stay {d : ℕ} (i : Fin d) (b : ℤ) (H : ℕ)
    (x : Lattice d) :
    Disjoint (wordCylinder x (List.replicate H (i, true)))
      (StayUntil (CoordinateStrip i b H) H) := by
  apply Set.disjoint_left.mpr
  intro X hw hS
  have hx : b ≤ x i := by
    have h := (hS 0 (Nat.zero_le H)).1
    simpa only [hw 0 (by simp), wordPath_zero] using h
  have hend := (hS H le_rfl).2
  have hp := hw H (by simp)
  rw [wordPath_replicate] at hp
  rw [hp] at hend
  simp [step] at hend
  omega

lemma quenched_strip_block {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (i : Fin d) (b : ℤ) (H : ℕ) (x : Lattice d) :
    quenchedKernel (ω, x) (StayUntil (CoordinateStrip i b H) H) ≤
      1 - (κ : ℝ≥0∞) ^ H := by
  have hsub : StayUntil (CoordinateStrip i b H) H ⊆
      (wordCylinder x (List.replicate H (i, true)))ᶜ :=
    (wordCylinder_up_disjoint_stay i b H x).subset_compl_left
  calc
    _ ≤ quenchedKernel (ω, x) (wordCylinder x (List.replicate H (i, true)))ᶜ :=
      measure_mono hsub
    _ = 1 - ENNReal.ofReal (wordWeight ω x (List.replicate H (i, true))) := by
      rw [measure_compl (measurableSet_wordCylinder _ _) (measure_ne_top _ _),
        measure_univ, quenched_wordCylinder]
    _ ≤ 1 - (κ : ℝ≥0∞) ^ H := by
      apply tsub_le_tsub_left
      have hs := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hκ x
        (List.replicate H (i, true)))
      simpa only [List.length_replicate, ENNReal.ofReal_pow κ.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using hs

lemma quenched_strip_geometric {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (i : Fin d) (b : ℤ) (H k : ℕ) (x : Lattice d) :
    quenchedKernel (ω, x) (StayUntil (CoordinateStrip i b H) (k * H)) ≤
      (1 - (κ : ℝ≥0∞) ^ H) ^ k :=
  quenched_stayUntil_block_bound ω (CoordinateStrip i b H) H _
    (quenched_strip_block ω hκ i b H) x k

def HitThrough {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  ⋃ k ≤ n, HitAt S T k

lemma measurableSet_hitThrough {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    MeasurableSet (HitThrough S T n) :=
  MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => measurableSet_hitAt S T k

lemma hitThrough_subset_hit {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    HitThrough S T n ⊆ Hit S T := by
  intro X h
  obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.mp h
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

lemma hit_subset_hitThrough_union_stayUntil {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    Hit S T ⊆ HitThrough S T n ∪ StayUntil S n := by
  intro X h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  by_cases hkn : k ≤ n
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hkn, hk⟩)
  · exact Or.inr (fun j hj => hk.2 j (by omega))

lemma quenched_hit_truncation {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) :
    quenchedKernel (ω, x) (Hit S T) ≤
      quenchedKernel (ω, x) (HitThrough S T n) +
        quenchedKernel (ω, x) (StayUntil S n) :=
  (measure_mono (hit_subset_hitThrough_union_stayUntil S T n)).trans (measure_union_le _ _)

lemma quenched_strip_hit_truncation {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (i : Fin d) (b : ℤ) (H k : ℕ)
    (x : Lattice d) (T : Set (Lattice d)) :
    quenchedKernel (ω, x) (Hit (CoordinateStrip i b H) T) ≤
      quenchedKernel (ω, x) (HitThrough (CoordinateStrip i b H) T (k * H)) +
        (1 - (κ : ℝ≥0∞) ^ H) ^ k :=
  (quenched_hit_truncation ω x _ _ _).trans
    (add_le_add le_rfl (quenched_strip_geometric ω hκ i b H k x))

def LatticeBall {d : ℕ} (x : Lattice d) (n : ℕ) : Set (Lattice d) :=
  {y | ∀ i, |y i - x i| ≤ (n : ℤ)}

lemma latticeBall_finite {d : ℕ} (x : Lattice d) (n : ℕ) :
    (LatticeBall x n).Finite := by
  have he : LatticeBall x n = Set.Icc (x - fun _ => (n : ℤ)) (x + fun _ => (n : ℤ)) := by
    ext y
    simp only [LatticeBall, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def,
      Pi.sub_apply, Pi.add_apply]
    constructor
    · intro h
      exact ⟨fun i => by have := (abs_le.mp (h i)).1; omega,
        fun i => by have := (abs_le.mp (h i)).2; omega⟩
    · rintro ⟨h, h'⟩ i
      exact abs_le.mpr ⟨by have := h i; omega, by have := h' i; omega⟩
  rw [he]
  exact Set.finite_Icc _ _

lemma abs_step_le_one {d : ℕ} (e : Direction d) (i : Fin d) :
    |step e i| ≤ (1 : ℤ) := by
  simp only [step]
  split_ifs <;> norm_num

def NearestNeighborPrefix {d : ℕ} (f : Path d) (n : ℕ) : Prop :=
  ∀ k < n, ∃ e : Direction d, f (k + 1) = f k + step e

lemma nearestNeighborPrefix_bound {d : ℕ} (f : Path d) (n : ℕ)
    (hf : NearestNeighborPrefix f n) {k : ℕ} (hk : k ≤ n) :
    f k ∈ LatticeBall (f 0) k := by
  induction k with
  | zero => simp [LatticeBall]
  | succ k ih =>
    obtain ⟨e, he⟩ := hf k (by omega)
    intro i
    rw [he]
    have hb := ih (by omega) i
    change |f k i + step e i - f 0 i| ≤ ((k + 1 : ℕ) : ℤ)
    calc
      _ = |(f k i - f 0 i) + step e i| := by congr 1; ring
      _ ≤ |f k i - f 0 i| + |step e i| := abs_add_le _ _
      _ ≤ (k : ℤ) + 1 := add_le_add hb (abs_step_le_one e i)
      _ = _ := by norm_cast

lemma edgeWeight_eq_zero_of_not_neighbor {d : ℕ} (ω : Environment d) (x y : Lattice d)
    (h : ¬ ∃ e : Direction d, y = x + step e) : edgeWeight ω x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  exact ite_eq_right (fun he => h ⟨e, he⟩)

lemma quenched_pathCylinder_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) (f : Path d) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      quenchedKernel (η, x) (pathCylinder f n) := by
  classical
  by_cases hstart : f 0 = x
  · rw [quenched_pathCylinder _ _ _ hstart, quenched_pathCylinder _ _ _ hstart]
    by_cases hpath : NearestNeighborPrefix f n
    · apply Finset.prod_congr rfl
      intro k hk
      have hn := (Finset.mem_range.mp hk).le
      have hb := nearestNeighborPrefix_bound f n hpath hn
      have hmem : f k ∈ LatticeBall x n := by
        intro i
        have h := hb i
        rw [hstart] at h
        exact h.trans (by exact_mod_cast hn)
      simp only [edgeWeight, hωη hmem]
    · unfold NearestNeighborPrefix at hpath
      push Not at hpath
      obtain ⟨k, hk, hbad⟩ := hpath
      have hbad' : ¬ ∃ e : Direction d, f (k + 1) = f k + step e := by
        simpa using hbad
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor ω _ _ hbad'),
        Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor η _ _ hbad')]
  · rw [quenched_pathCylinder_zero _ _ _ hstart, quenched_pathCylinder_zero _ _ _ hstart]

lemma quenched_prefix_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n))
    (C : Set ((i : Finset.Iic n) → Lattice d)) :
    quenchedKernel (ω, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) =
      quenchedKernel (η, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) := by
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ C) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← tsum_measure_preimage_singleton C.to_countable hm,
    ← tsum_measure_preimage_singleton C.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  exact quenched_pathCylinder_locality ω η x n hωη _

lemma quenched_hitThrough_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) :
    quenchedKernel (ω, x) (HitThrough S T n) =
      quenchedKernel (η, x) (HitThrough S T n) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | ∃ (k : ℕ) (hk : k ≤ n), f ⟨k, Finset.mem_Iic.mpr hk⟩ ∈ T ∧
      ∀ (j : ℕ) (hj : j < k), f ⟨j, Finset.mem_Iic.mpr (hj.le.trans hk)⟩ ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = HitThrough S T n := by
    ext X
    constructor
    · rintro ⟨k, hk, hT, hS⟩
      exact Set.mem_iUnion₂.mpr ⟨k, hk, hT, hS⟩
    · intro h
      obtain ⟨k, hk, hT, hS⟩ := Set.mem_iUnion₂.mp h
      exact ⟨k, hk, hT, hS⟩
  rw [← hC]
  exact quenched_prefix_locality ω η x n hωη C

lemma quenched_strip_compare {d : ℕ} (ω η : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (i : Fin d) (b : ℤ) (H k : ℕ)
    (x : Lattice d) (T : Set (Lattice d))
    (hωη : Set.EqOn ω η (LatticeBall x (k * H))) :
    quenchedKernel (ω, x) (Hit (CoordinateStrip i b H) T) ≤
      quenchedKernel (η, x) (Hit (CoordinateStrip i b H) T) +
        (1 - (κ : ℝ≥0∞) ^ H) ^ k := by
  have ht := quenched_strip_hit_truncation ω hκ i b H k x T
  rw [quenched_hitThrough_locality ω η x _ _ _ hωη] at ht
  exact ht.trans (add_le_add (measure_mono (hitThrough_subset_hit _ _ _)) le_rfl)

lemma quenched_strip_uniform_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (H : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (ω η : Environment d),
      (∀ y e, κ ≤ (ω y).1 e) → (∀ y e, κ ≤ (η y).1 e) →
      ∀ (x : Lattice d) (i : Fin d) (b : ℤ) (T : Set (Lattice d)),
      Set.EqOn ω η (LatticeBall x n) →
      quenchedKernel (ω, x) (Hit (CoordinateStrip i b H) T) ≤
        quenchedKernel (η, x) (Hit (CoordinateStrip i b H) T) + ε ∧
      quenchedKernel (η, x) (Hit (CoordinateStrip i b H) T) ≤
        quenchedKernel (ω, x) (Hit (CoordinateStrip i b H) T) + ε := by
  have hc : 1 - (κ : ℝ≥0∞) ^ H < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero _ (by exact_mod_cast hκ.ne'))
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc).eventually_lt_const hε).exists
  refine ⟨k * H, fun ω η hω hη x i b T he => ?_⟩
  exact ⟨(quenched_strip_compare ω η hω i b H k x T he).trans (add_le_add le_rfl hk.le),
    (quenched_strip_compare η ω hη i b H k x T he.symm).trans (add_le_add le_rfl hk.le)⟩

lemma measurable_of_row_locality {d : ℕ} {α : Type*} [MeasurableSpace α]
    (f : Environment d → α) (hf : Measurable f) (S : Set (Lattice d))
    (x : Lattice d) (hx : x ∈ S)
    (hloc : ∀ ω η, Set.EqOn ω η S → f ω = f η) :
    @Measurable _ _ (rowSigma S) _ f := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have he : f = f ∘ patch := by
    funext ω
    exact hloc ω (patch ω) (fun y hy => by simp [patch, hy])
  rw [he]
  exact hf.comp hp

lemma measurable_hitThrough_ball {d : ℕ} (x : Lattice d) (S T : Set (Lattice d)) (n : ℕ) :
    @Measurable _ _ (rowSigma (LatticeBall x n)) _
      (fun ω : Environment d => quenchedKernel (ω, x) (HitThrough S T n)) := by
  apply measurable_of_row_locality _
    ((Kernel.measurable_coe _ (measurableSet_hitThrough S T n)).comp
      (measurable_id.prodMk measurable_const)) _ x
    (by simp [LatticeBall])
  intro ω η h
  exact quenched_hitThrough_locality ω η x S T n h

noncomputable def noDropFinite {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ)
    (ω : Environment d) : ℝ≥0∞ :=
  quenchedKernel (ω, x) (StayUntil {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} n)

lemma noDropFinite_measurable {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    Measurable (noDropFinite ℓ x n) :=
  (Kernel.measurable_coe _ (measurableSet_stayUntil _ n)).comp
    (measurable_id.prodMk measurable_const)

end DirectionalTransience
end
end

end OAI
