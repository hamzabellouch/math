import Mathlib
import OAI.Probability.Ballisticity.Walk.StateTrajectory

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma fresh_rows_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    {f g : Environment d → ℝ}
    (hf : @Measurable _ _ (rowSigma S) _ f)
    (hg : @Measurable _ _ (rowSigma T) _ g) :
    (∫ ω, f ω * g ω ∂environmentLaw ν) =
      (∫ ω, f ω ∂environmentLaw ν) * (∫ ω, g ω ∂environmentLaw ν) := by
  have hi : IndepFun f g (environmentLaw ν) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    exact (Indep_iff _ _ _).mp (environment_indep_rows ν hST) _ _ (hf hs) (hg ht)
  exact hi.integral_fun_mul_eq_mul_integral
    (hf.mono (rowSigma_le S) le_rfl).aestronglyMeasurable
    (hg.mono (rowSigma_le T) le_rfl).aestronglyMeasurable

def wordDepartures {d : ℕ} (x : Lattice d) : List (Direction d) → Finset (Lattice d)
  | [] => ∅
  | e :: w => insert x (wordDepartures (x + step e) w)

noncomputable def wordWeight {d : ℕ} (ω : Environment d) (x : Lattice d) :
    List (Direction d) → ℝ
  | [] => 1
  | e :: w => ((ω x).1 e : ℝ) * wordWeight ω (x + step e) w

lemma wordWeight_nonneg {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) : 0 ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih => exact mul_nonneg (NNReal.coe_nonneg _) (ih _)

lemma wordWeight_le_one {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) : wordWeight ω x w ≤ 1 := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    exact (mul_le_of_le_one_left (wordWeight_nonneg ω _ w)
      (by exact_mod_cast row_entry_le_one (ω x) e)).trans (ih _)

lemma measurable_wordWeight_on {d : ℕ} {S : Set (Lattice d)} (x : Lattice d)
    (w : List (Direction d)) (hS : ∀ y ∈ wordDepartures x w, y ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => wordWeight ω x w) := by
  induction w generalizing x with
  | nil => exact measurable_const
  | cons e w ih =>
    have hx : x ∈ S := hS x (Finset.mem_insert_self _ _)
    have he : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => ((ω x).1 e : ℝ)) :=
      ((measurable_pi_apply e).comp
        (measurable_subtype_coe.comp (measurable_row_on hx))).coe_nnreal_real
    exact he.mul (ih _ (fun y hy => hS y (Finset.mem_insert_of_mem hy)))

lemma measurable_wordWeight {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    Measurable (fun ω : Environment d => wordWeight ω x w) :=
  (measurable_wordWeight_on (S := Set.univ) x w (by simp)).mono
    (rowSigma_le _) le_rfl

lemma integrable_wordWeight {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) (w : List (Direction d)) :
    Integrable (fun ω => wordWeight ω x w) (environmentLaw ν) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_wordWeight x w).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (wordWeight_nonneg ω x w)]
    exact wordWeight_le_one ω x w

lemma wordWeight_fresh_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) (w : List (Direction d)) {g : Environment d → ℝ}
    (hg : @Measurable _ _ (rowSigma (wordDepartures x w : Set (Lattice d))ᶜ) _ g) :
    (∫ ω, wordWeight ω x w * g ω ∂environmentLaw ν) =
    (∫ ω, wordWeight ω x w ∂environmentLaw ν) * (∫ ω, g ω ∂environmentLaw ν) := by
  exact fresh_rows_factor ν disjoint_compl_right
    (measurable_wordWeight_on x w (by simp)) hg

def wordPath {d : ℕ} (x : Lattice d) : List (Direction d) → Path d
  | [], _ => x
  | _ :: _, 0 => x
  | e :: w, n + 1 => wordPath (x + step e) w n

@[simp] lemma wordPath_zero {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    wordPath x w 0 = x := by cases w <;> rfl

def wordCylinder {d : ℕ} (x : Lattice d) (w : List (Direction d)) : Set (Path d) :=
  {X | ∀ i ≤ w.length, X i = wordPath x w i}

lemma measurableSet_wordCylinder {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    MeasurableSet (wordCylinder x w) := by
  simp only [wordCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : Path d => X i))
      measurable_const

lemma wordPath_transition_product {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) :
    (∏ i ∈ Finset.range w.length,
      transition (ω, wordPath x w i) {(ω, wordPath x w (i + 1))}) =
    ENNReal.ofReal (wordWeight ω x w) := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [wordPath, wordPath_zero]
    rw [ih, transition_singleton_step, wordWeight, ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    simp [mul_comm]

lemma quenched_wordCylinder {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) :
    quenchedKernel (ω, x) (wordCylinder x w) = ENNReal.ofReal (wordWeight ω x w) := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_apply hm (measurableSet_wordCylinder x w)]
  have he : (fun z : ℕ → State d => fun n => (z n).2) ⁻¹' wordCylinder x w
      =ᵐ[stateTrajectory (ω, x)] stateCylinder (fun n => (ω, wordPath x w n)) w.length := by
    filter_upwards [stateTrajectory_environment (ω, x)] with X hX
    apply propext
    change (∀ i ≤ w.length, (X i).2 = wordPath x w i) ↔
      (∀ i ≤ w.length, X i = (ω, wordPath x w i))
    constructor
    · intro hh n hn
      exact Prod.ext (hX n) (hh n hn)
    · intro hh n hn
      exact congrArg Prod.snd (hh n hn)
  rw [measure_congr he, stateTrajectory_cylinder _ _ (by simp), wordPath_transition_product]

lemma annealed_wordCylinder {d : ℕ} (ν : Measure (Row d)) (w : List (Direction d)) :
    annealedLaw ν (wordCylinder 0 w) =
      ∫⁻ ω, ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν := by
  rw [annealed_apply ν (measurableSet_wordCylinder 0 w)]
  congr 1
  funext ω
  exact quenched_wordCylinder ω 0 w

def pathCylinder {d : ℕ} (f : Path d) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma measurableSet_pathCylinder {d : ℕ} (f : Path d) (n : ℕ) :
    MeasurableSet (pathCylinder f n) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : Path d => X i))
      measurable_const

lemma pathMeasure_ext {d : ℕ} (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ f n, μ (pathCylinder f n) = ν (pathCylinder f n)) : μ = ν := by
  let P : (I : Finset ℕ) → Measure ((i : I) → Lattice d) :=
    fun I => μ.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ : ℕ => Lattice d) P := by
    exact isProjectiveMeasureFamily_map_restrict (P := μ) (X := fun n (X : Path d) => X n)
      (fun n => (measurable_pi_apply n).aemeasurable)
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => Lattice d) μ P := by
    intro I
    rfl
  apply hμ.unique
  apply (isProjectiveLimit_nat_iff hp ν).mpr
  intro n
  apply Measure.ext_of_singleton
  intro f
  have hf : MeasurableSet ({f} : Set ((i : Finset.Iic n) → Lattice d)) :=
    measurableSet_singleton _
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  change _ = μ.map (Preorder.frestrictLe n) {f}
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  let g : Path d := fun i => if hi : i ≤ n then f ⟨i, Finset.mem_Iic.mpr hi⟩ else 0
  have he : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f} = pathCylinder g n := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hh i hi
      simpa [g, hi] using congrFun hh ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro hh
      funext i
      simpa [g, Finset.mem_Iic.mp i.2] using hh i (Finset.mem_Iic.mp i.2)
  rw [he, h]

noncomputable def edgeWeight {d : ℕ} (ω : Environment d) (x y : Lattice d) : ℝ≥0∞ :=
  ∑ e : Direction d, if y = x + step e then ((ω x).1 e : ℝ≥0∞) else 0

lemma transition_singleton {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    transition (ω, x) {(ω, y)} = edgeWeight ω x y := by
  classical
  change (∑ e : Direction d, ((ω x).1 e : ℝ≥0∞) •
    Measure.dirac (ω, x + step e)) {(ω, y)} = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, edgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : y = x + step e
  · simp [he]
  · simp [he, Ne.symm he]

lemma quenched_pathCylinder {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      ∏ i ∈ Finset.range n, edgeWeight ω (f i) (f (i + 1)) := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_apply hm (measurableSet_pathCylinder f n)]
  have he : (fun z : ℕ → State d => fun n => (z n).2) ⁻¹' pathCylinder f n
      =ᵐ[stateTrajectory (ω, x)] stateCylinder (fun i => (ω, f i)) n := by
    filter_upwards [stateTrajectory_environment (ω, x)] with X hX
    apply propext
    change (∀ i ≤ n, (X i).2 = f i) ↔ (∀ i ≤ n, X i = (ω, f i))
    constructor
    · intro hh i hi
      exact Prod.ext (hX i) (hh i hi)
    · intro hh i hi
      exact congrArg Prod.snd (hh i hi)
  rw [measure_congr he, stateTrajectory_cylinder _ _ (by simp [hf])]
  simp only [transition_singleton]

lemma quenched_pathCylinder_zero {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 ≠ x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) = 0 := by
  have hsub : pathCylinder f n ⊆ {X | X 0 ≠ x} := by
    intro X hX
    change X 0 ≠ x
    rw [hX 0 (Nat.zero_le n)]
    exact hf
  exact measure_mono_null hsub ((ae_iff).mp (quenched_initial_ae (ω, x)))

lemma edgeWeight_translation {d : ℕ} (ω : Environment d) (z x y : Lattice d) :
    edgeWeight (fun a => ω (z + a)) x y = edgeWeight ω (z + x) (z + y) := by
  classical
  simp only [edgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simp only [add_assoc, add_right_inj]

lemma quenched_translation {d : ℕ} (ω : Environment d) (z x : Lattice d) :
    (quenchedKernel (ω, z + x)).map (fun X n => X n - z) =
      quenchedKernel ((fun a => ω (z + a)), x) := by
  have hm : Measurable (fun X : Path d => fun n => X n - z) := by fun_prop
  apply pathMeasure_ext
  intro f n
  rw [Measure.map_apply hm (measurableSet_pathCylinder f n)]
  have he : (fun X : Path d => fun i => X i - z) ⁻¹' pathCylinder f n =
      pathCylinder (fun i => z + f i) n := by
    ext X
    simp only [pathCylinder, Set.mem_preimage, Set.mem_ofPred_eq, sub_eq_iff_eq_add, add_comm]
  rw [he]
  by_cases hf : f 0 = x
  · rw [quenched_pathCylinder _ _ _ (by simp [hf]), quenched_pathCylinder _ _ _ hf]
    simp only [edgeWeight_translation]
  · rw [quenched_pathCylinder_zero _ _ _ (by simpa using hf),
      quenched_pathCylinder_zero _ _ _ hf]

def splicePath {d : ℕ} (f g : Path d) (n : ℕ) : Path d :=
  fun i => if i < n then f i else g (i - n)

lemma splicePath_left {d : ℕ} (f g : Path d) {n i : ℕ}
    (hg : g 0 = f n) (hi : i ≤ n) : splicePath f g n i = f i := by
  rcases lt_or_eq_of_le hi with hi | rfl
  · simp [splicePath, hi]
  · simp [splicePath, hg]

lemma splicePath_right {d : ℕ} (f g : Path d) (n i : ℕ) :
    splicePath f g n (n + i) = g i := by
  simp [splicePath]

lemma pathCylinder_splice {d : ℕ} (f g : Path d) (n k : ℕ) (hg : g 0 = f n) :
    (fun X : Path d => fun i => X (n + i)) ⁻¹' pathCylinder g k ∩ pathCylinder f n =
      pathCylinder (splicePath f g n) (n + k) := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_preimage, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hin : i ≤ n
    · rw [splicePath_left f g hg hin]
      exact h₂ i hin
    · have hn : n ≤ i := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [splicePath_right]
      exact h₁ j (by omega)
  · intro hX
    constructor
    · intro i hi
      simpa only [splicePath_right] using hX (n + i) (by omega)
    · intro i hi
      simpa only [splicePath_left f g hg hi] using hX i (by omega)

lemma splicePath_weight {d : ℕ} (ω : Environment d) (f g : Path d) (n k : ℕ)
    (hg : g 0 = f n) :
    (∏ i ∈ Finset.range (n + k),
      edgeWeight ω (splicePath f g n i) (splicePath f g n (i + 1))) =
      (∏ i ∈ Finset.range n, edgeWeight ω (f i) (f (i + 1))) *
      ∏ i ∈ Finset.range k, edgeWeight ω (g i) (g (i + 1)) := by
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [splicePath_left f g hg (by omega), splicePath_left f g hg (by omega)]
  · apply Finset.prod_congr rfl
    intro i _
    rw [splicePath_right, show n + i + 1 = n + (i + 1) by omega, splicePath_right]

lemma quenched_prefix_markov {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) :
    ((quenchedKernel (ω, x)).restrict (pathCylinder f n)).map
        (fun X i => X (n + i)) =
      (quenchedKernel (ω, x) (pathCylinder f n)) • quenchedKernel (ω, f n) := by
  have hm : Measurable (fun X : Path d => fun i => X (n + i)) := by fun_prop
  apply pathMeasure_ext
  intro g k
  rw [Measure.map_apply hm (measurableSet_pathCylinder g k),
    Measure.restrict_apply (hm (measurableSet_pathCylinder g k)), Measure.smul_apply, smul_eq_mul]
  by_cases hg : g 0 = f n
  · rw [pathCylinder_splice f g n k hg,
      quenched_pathCylinder _ _ _ ((splicePath_left f g hg (Nat.zero_le n)).trans hf),
      quenched_pathCylinder _ _ _ hf, quenched_pathCylinder _ _ _ hg,
      splicePath_weight ω f g n k hg]
  · rw [quenched_pathCylinder_zero _ _ _ hg, mul_zero]
    have he : (fun X : Path d => fun i => X (n + i)) ⁻¹' pathCylinder g k ∩
        pathCylinder f n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨h₁, h₂⟩
      have h₁' := h₁ 0 (Nat.zero_le k)
      have h₂' := h₂ n le_rfl
      apply hg
      simpa using h₁'.symm.trans (by simpa using h₂')
    rw [he, measure_empty]

lemma quenched_prefix_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) {A : Set (Path d)} (hA : MeasurableSet A) :
    quenchedKernel (ω, x)
      ((fun X : Path d => fun i => X (n + i)) ⁻¹' A ∩ pathCylinder f n) =
      quenchedKernel (ω, x) (pathCylinder f n) * quenchedKernel (ω, f n) A := by
  have h := congrArg (fun μ : Measure (Path d) => μ A) (quenched_prefix_markov ω x f hf n)
  rw [Measure.map_apply (by fun_prop) hA, Measure.restrict_apply ((by fun_prop : Measurable (fun X : Path d => fun i => X (n + i))) hA),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

def NoDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Set (Path d) :=
  {X | ∀ n, dot (realPosition x) ℓ ≤ dot (realPosition (X n)) ℓ}

lemma measurableSet_noDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    MeasurableSet (NoDrop ℓ x) := by
  simp only [NoDrop, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le measurable_const
    ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply n))

lemma dot_realPosition_add {d : ℕ} (x y : Lattice d) (ℓ : Vector d) :
    dot (realPosition (x + y)) ℓ = dot (realPosition x) ℓ + dot (realPosition y) ℓ := by
  simp [dot, realPosition, add_mul, Finset.sum_add_distrib]

lemma dot_realPosition_sub {d : ℕ} (x y : Lattice d) (ℓ : Vector d) :
    dot (realPosition (x - y)) ℓ = dot (realPosition x) ℓ - dot (realPosition y) ℓ := by
  simp [dot, realPosition, sub_mul, Finset.sum_sub_distrib]

lemma noDrop_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) :
    (fun X : Path d => fun n => X n - z) ⁻¹' NoDrop ℓ x = NoDrop ℓ (z + x) := by
  ext X
  simp only [NoDrop, Set.mem_preimage, Set.mem_ofPred_eq, dot_realPosition_add,
    dot_realPosition_sub]
  apply forall_congr'
  intro n
  constructor <;> intro h <;> linarith

noncomputable def noDropQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : ℝ≥0∞ := quenchedKernel (ω, x) (NoDrop ℓ x)

lemma measurable_noDropQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    Measurable (noDropQuenched ℓ x) :=
  (Kernel.measurable_coe _ (measurableSet_noDrop ℓ x)).comp
    (measurable_id.prodMk measurable_const)

lemma noDropQuenched_translation {d : ℕ} (ℓ : Vector d) (ω : Environment d) (x : Lattice d) :
    noDropQuenched ℓ x ω = noDropQuenched ℓ 0 (fun a => ω (x + a)) := by
  have h := congrArg (fun μ : Measure (Path d) => μ (NoDrop ℓ 0))
    (quenched_translation ω x 0)
  rw [Measure.map_apply (by fun_prop) (measurableSet_noDrop ℓ 0), noDrop_translation] at h
  simpa [noDropQuenched] using h

lemma annealed_noDrop_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    (∫⁻ ω, noDropQuenched ℓ x ω ∂environmentLaw ν) = annealedLaw ν (NoDrop ℓ 0) := by
  simp_rw [noDropQuenched_translation ℓ _ x]
  rw [← lintegral_map (measurable_noDropQuenched ℓ 0) (by fun_prop),
    environment_translation, annealed_apply ν (measurableSet_noDrop ℓ 0)]
  rfl

def FutureNoDrop {d : ℕ} (ℓ : Vector d) (n : ℕ) : Set (Path d) :=
  {X | ∀ i, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + i))) ℓ}

lemma measurableSet_futureNoDrop {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet (FutureNoDrop ℓ n) := by
  simp only [FutureNoDrop, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    ((measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply n))
    ((measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply (n + i)))

lemma tendsto_atTop_has_minimum (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    ∃ n, ∀ j, a n ≤ a j := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.eventually (eventually_ge_atTop (a 0)))
  obtain ⟨n, hn, hmin⟩ := Finset.exists_min_image (Finset.range (N + 1)) a
    ⟨0, by simp⟩
  refine ⟨n, fun j => ?_⟩
  by_cases hj : N ≤ j
  · exact (hmin 0 (by simp)).trans (hN j hj)
  · exact hmin j (Finset.mem_range.mpr (by omega))

def extendPrefix {d : ℕ} (n : ℕ) (f : (i : Finset.Iic n) → Lattice d) : Path d :=
  fun i => if hi : i ≤ n then f ⟨i, Finset.mem_Iic.mpr hi⟩ else 0

lemma extendPrefix_apply {d : ℕ} (n : ℕ) (f : (i : Finset.Iic n) → Lattice d)
    (i : ℕ) (hi : i ≤ n) :
    extendPrefix n f i = f ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp [extendPrefix, hi]

end DirectionalTransience
end
end

end OAI
