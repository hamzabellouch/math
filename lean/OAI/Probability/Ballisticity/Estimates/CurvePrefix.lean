import Mathlib
import OAI.Probability.Ballisticity.Coupling.QuenchedPrefixDeterminedFuture

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

def CurvePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : Set (Path d) :=
  HitAt (Strip ℓ x s) (Upper ℓ x s) n ∩
    {X | ∀ j ≤ s, ∃ a ≤ n,
      (fun k => X k-x) ∈ RecordOrZeroPrefix ℓ j a ∧
      |signedCoordinate f (X a-x)-b j| ≤ z}

lemma measurableSet_curvePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : MeasurableSet (CurvePrefixAt ℓ f x b z s n) := by
  apply (measurableSet_hitAt _ _ n).inter
  simp only [Set.ofPred_forall,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iUnion; intro a
  refine (MeasurableSet.const (a ≤ n)).inter ?_
  have hm : Measurable (fun X : Path d => fun k => X k-x) := by fun_prop
  have hc : Measurable (fun X : Path d => signedCoordinate f (X a-x)) :=
    (measurable_of_countable (signedCoordinate f)).comp
      ((measurable_pi_apply a : Measurable (fun X : Path d => X a)).sub_const x)
  exact ((measurableSet_recordOrZeroPrefix ℓ j a).preimage hm).inter
    (measurableSet_le ((hc.sub_const (b j)).abs) measurable_const)

lemma curvePrefixAt_prefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : PrefixDetermined n (CurvePrefixAt ℓ f x b z s n) := by
  have hdir (X Y : Path d) (hXY : ∀ j ≤ n, X j=Y j)
      (hX : X ∈ CurvePrefixAt ℓ f x b z s n) : Y ∈ CurvePrefixAt ℓ f x b z s n := by
    refine ⟨⟨by simpa only [← hXY n le_rfl] using hX.1.1,
      fun j hj => by simpa only [← hXY j hj.le] using hX.1.2 j hj⟩,?_⟩
    intro j hj
    obtain ⟨a,ha,hrec,hgood⟩ := hX.2 j hj
    refine ⟨a,ha,(recordOrZeroPrefix_prefix ℓ j a _ _
      (fun k hk => by rw [hXY k (hk.trans ha)])).mp hrec,?_⟩
    simpa only [← hXY a ha] using hgood
  intro X Y h
  exact ⟨hdir X Y h,hdir Y X (fun j hj => (h j hj).symm)⟩

def CurvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) : Set (Path d) := ⋃ n, CurvePrefixAt ℓ f x b z s n

lemma measurableSet_curvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) : MeasurableSet (CurvePrefix ℓ f x b z s) :=
  MeasurableSet.iUnion (measurableSet_curvePrefixAt ℓ f x b z s)

lemma curvePrefixAt_disjoint {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) : Pairwise (fun n m =>
      Disjoint (CurvePrefixAt ℓ f x b z s n) (CurvePrefixAt ℓ f x b z s m)) := by
  intro n m hnm
  exact (hitAt_pairwise_disjoint (disjoint_strip_upper ℓ x s) hnm).mono
    Set.inter_subset_left Set.inter_subset_left

lemma quenched_curvePrefix_congr {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω η : Environment d) (hωη : Set.EqOn ω η (Strip ℓ x s)) :
    quenchedKernel (ω,x) (CurvePrefix ℓ f x b z s) =
      quenchedKernel (η,x) (CurvePrefix ℓ f x b z s) := by
  rw [CurvePrefix,measure_iUnion (curvePrefixAt_disjoint ℓ f x b z s)
    (measurableSet_curvePrefixAt ℓ f x b z s),measure_iUnion (curvePrefixAt_disjoint ℓ f x b z s)
    (measurableSet_curvePrefixAt ℓ f x b z s)]
  exact tsum_congr fun n => quenched_prefix_event_congr (Strip ℓ x s) ω η hωη x n _
    (curvePrefixAt_prefix ℓ f x b z s n) (fun _ hX => hX.1.2)

lemma measurable_quenched_curvePrefix_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (z : ℝ) {s : ℕ} (hs : 0 < s) :
    @Measurable _ _ (rowSigma (Strip ℓ x s)) _
      (fun ω : Environment d => quenchedKernel (ω,x) (CurvePrefix ℓ f x b z s)) := by
  apply measurable_of_row_locality _
    ((Kernel.measurable_coe _ (measurableSet_curvePrefix ℓ f x b z s)).comp
      (measurable_id.prodMk measurable_const)) (Strip ℓ x s) x
      (show x ∈ Strip ℓ x s from ⟨le_rfl,by exact lt_add_of_pos_right _ (by exact_mod_cast hs)⟩)
  intro ω η h
  exact quenched_curvePrefix_congr ℓ f x b z s ω η h

noncomputable def curveEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  Measure.sum fun n => ((quenchedKernel (ω,x)).restrict (CurvePrefixAt ℓ f x b z s n)).map (fun X => X n)

lemma curveEndpoint_apply {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) (U : Set (Lattice d)) :
    curveEndpoint ℓ f x b z s ω U = ∑' n, quenchedKernel (ω,x)
      ((fun X => X n) ⁻¹' U ∩ CurvePrefixAt ℓ f x b z s n) := by
  rw [curveEndpoint,Measure.sum_apply _ U.to_countable.measurableSet]
  apply tsum_congr; intro n
  rw [Measure.map_apply (measurable_pi_apply n) U.to_countable.measurableSet,
    Measure.restrict_apply ((measurable_pi_apply n) U.to_countable.measurableSet)]

lemma curveEndpoint_total {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) :
    curveEndpoint ℓ f x b z s ω Set.univ = quenchedKernel (ω,x) (CurvePrefix ℓ f x b z s) := by
  rw [curveEndpoint_apply,CurvePrefix,measure_iUnion (curvePrefixAt_disjoint ℓ f x b z s)
    (measurableSet_curvePrefixAt ℓ f x b z s)]
  simp only [Set.preimage_univ,Set.univ_inter]

instance curveEndpoint_finite {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) : IsFiniteMeasure (curveEndpoint ℓ f x b z s ω) :=
  ⟨by rw [curveEndpoint_total]; exact measure_lt_top _ _⟩

lemma curveEndpoint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) {s : ℕ} (hs : 0 < s) :
    @Measurable _ _ (rowSigma (Strip ℓ x s)) _ (curveEndpoint ℓ f x b z s) := by
  let : MeasurableSpace (Environment d) := rowSigma (Strip ℓ x s)
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp_rw [curveEndpoint_apply]
  apply Measurable.tsum; intro n
  apply measurable_quenched_prefix_event_rows (Strip ℓ x s) x
    (show x ∈ Strip ℓ x s from ⟨le_rfl,lt_add_of_pos_right _ (by exact_mod_cast hs)⟩) n
  · exact ((measurable_pi_apply n) U.to_countable.measurableSet).inter (measurableSet_curvePrefixAt ℓ f x b z s n)
  · intro X Y hXY
    exact and_congr (by rw [Set.mem_preimage,Set.mem_preimage,hXY n le_rfl])
      (curvePrefixAt_prefix ℓ f x b z s n X Y hXY)
  · exact fun _ hX => hX.2.1.2

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma curveEndpoint_future {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    (∫⁻ y, quenchedKernel (ω,y) (B y) ∂curveEndpoint ℓ f x b z s ω) =
      quenchedKernel (ω,x) (⋃ n, CurvePrefixAt ℓ f x b z s n ∩ FutureEvent B n) := by
  rw [curveEndpoint,lintegral_sum_measure]
  rw [measure_iUnion (fun n m hnm => (curvePrefixAt_disjoint ℓ f x b z s hnm).mono
    Set.inter_subset_left Set.inter_subset_left)
    (fun n => (measurableSet_curvePrefixAt ℓ f x b z s n).inter (measurableSet_futureEvent B hB n))]
  apply tsum_congr; intro n
  rw [lintegral_map (measurable_of_countable _) (measurable_pi_apply n)]
  exact (quenched_prefixDetermined_future ω x n _ (curvePrefixAt_prefix ℓ f x b z s n) B hB).symm

noncomputable def curveWordEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) : Lattice d → List (Lattice d) → Set (Path d)
  | _, [] => Set.univ
  | x, u::w => ⋃ n, CurvePrefixAt ℓ f x b B H n ∩
      FutureEvent (fun y => if y=x+u then curveWordEvent ℓ f b B H y w else ∅) n

lemma measurableSet_curveWordEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x : Lattice d) (w : List (Lattice d)) :
    MeasurableSet (curveWordEvent ℓ f b B H x w) := by
  induction w generalizing x with
  | nil => exact MeasurableSet.univ
  | cons u w ih =>
    apply MeasurableSet.iUnion; intro n
    exact (measurableSet_curvePrefixAt ℓ f x b B H n).inter
      (measurableSet_futureEvent _ (fun y => by split_ifs; exact ih y; exact MeasurableSet.empty) n)

lemma curveWordEvent_cons_mass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) (x u : Lattice d) (w : List (Lattice d)) :
    quenchedKernel (ω,x) (curveWordEvent ℓ f b B H x (u::w)) =
      curveEndpoint ℓ f x b B H ω {x+u} *
        quenchedKernel (ω,x+u) (curveWordEvent ℓ f b B H (x+u) w) := by
  rw [curveWordEvent,← curveEndpoint_future ℓ f x b B H ω _
    (fun y => by split_ifs; exact measurableSet_curveWordEvent ℓ f b B H y w; exact MeasurableSet.empty)]
  have he : (fun y => quenchedKernel (ω,y)
      (if y=x+u then curveWordEvent ℓ f b B H y w else ∅)) =
      ({x+u} : Set (Lattice d)).indicator
        (fun _ => quenchedKernel (ω,x+u) (curveWordEvent ℓ f b B H (x+u) w)) := by
    funext y
    by_cases hy : y=x+u
    · subst y; simp
    · simp [hy,Set.indicator_of_notMem]
  rw [he,lintegral_indicator (measurableSet_singleton _),lintegral_const,Measure.restrict_apply_univ]
  exact mul_comm _ _

end DirectionalTransience

end

end

end OAI
