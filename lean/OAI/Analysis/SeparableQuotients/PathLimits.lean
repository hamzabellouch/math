import OAI.Analysis.SeparableQuotients.BoundedCompleteness

namespace OAI

noncomputable section

namespace SeparableQuotient.PathLimits
open Filter
open scoped Topology
universe u
variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma unit_bound (f : StrongDual ℝ Z) (hf : ‖f‖ ≤ 1) (x : Z) : ‖f x‖ ≤ ‖x‖ :=
  (f.le_opNorm x).trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hf (norm_nonneg x))

lemma cauchy_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) (x : Z) :
    CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hD x) (ε/4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h y hy) (ε/4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmxy : dist (f m x) (f m y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f m) (hf m) (x-y)
  have hnxy : dist (f n y) (f n x) ≤ dist x y := by
    rw [dist_comm (f n y)]
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f n) (hf n) (x-y)
  have ht := calc
    dist (f m x) (f n x) ≤ dist (f m x) (f m y) + dist (f m y) (f n x) := dist_triangle _ _ _
    _ ≤ dist (f m x) (f m y) + (dist (f m y) (f n y) + dist (f n y) (f n x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
  have := hN m hm n hn
  have hd : dist x y < ε/4 := by simpa only [dist_comm] using hxy
  linarith

/-- Bounded pointwise convergence on a dense set determines an actual bounded
functional on the completed space; no weak-star sequential compactness is used. -/
lemma exists_limit_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) :
    ∃ P : StrongDual ℝ Z, ‖P‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (P x)) := by
  choose g hg using (fun x => cauchySeq_tendsto_of_complete (cauchy_of_dense f hf D hD h x))
  have hb : Bornology.IsBounded (Set.range f) := isBounded_iff_forall_norm_le.mpr
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hf n⟩
  let P : StrongDual ℝ Z := ContinuousLinearMap.ofTendstoOfBoundedRange g f
    (tendsto_pi_nhds.mpr hg) hb
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
    intro x
    simpa only [P, ContinuousLinearMap.ofTendstoOfBoundedRange_apply, one_mul] using le_of_tendsto (hg x).norm
      (Filter.Eventually.of_forall (fun n => unit_bound (f n) (hf n) x))
  exact ⟨P, hP, hg⟩

end SeparableQuotient.PathLimits

namespace SeparableQuotient.Norming
open scoped Classical
open PathCoding

def Family.base : Family → Set Array
  | .pure k => pureBase k
  | .mixed => ⋃ k, Pure k

def Family.norming (f : Family) : Set Array := ⋃ n, stage f.base f n

lemma Family.norming_subset_full (f : Family) : f.norming ⊆ Full := by
  cases f with
  | pure k => exact pure_subset_full k
  | mixed => exact Set.Subset.rfl

lemma common_stage {f : Family} {ι : Type*} [Fintype ι] (x : ι → Array)
    (hx : ∀ i, x i ∈ f.norming) : ∃ n, ∀ i, x i ∈ stage f.base f n := by
  have hh : ∀ i, ∃ n, x i ∈ stage f.base f n := fun i => Set.mem_iUnion.mp (hx i)
  choose n hn using hh
  exact ⟨Finset.univ.sup n, fun i => stage_mono _ _ (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

lemma TypeI.mem_family {f : Family} (e : TypeI f)
    (h : ∀ i, e.child i ∈ f.norming) : e.value ∈ f.norming := by
  obtain ⟨n, hn⟩ := common_stage e.child h
  exact Set.mem_iUnion.mpr ⟨n+1, Or.inl (Or.inr ⟨e, rfl, hn⟩)⟩

lemma TypeII.mem_family {f : Family} (e : TypeII f)
    (h : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) : e.value ∈ f.norming := by
  let ι := Σ b : Fin e.length, Σ i : Fin (e.path b).length, Fin ((e.path b).piece i).length
  obtain ⟨n, hn⟩ := common_stage (fun a : ι => ((e.path a.1).piece a.2.1).child a.2.2)
    (fun a => h a.1 a.2.1 a.2.2)
  exact Set.mem_iUnion.mpr ⟨n+1, Or.inr ⟨e, rfl, fun b i j => hn ⟨b,i,j⟩⟩⟩

lemma admissible_prefix {P : RawPath} (h : P.Admissible) (n : ℕ) : PrefixValid P n where
  successive := fun i j hij _ => h.successive i j hij
  metadata_strict := fun _i _j hij _ => h.metadata_strict hij
  metadata_pos := fun i _ => h.metadata_pos i
  weight_pos := fun i _ => h.weight_pos i
  weight_le_metadata := fun i _ => h.weight_le_metadata i
  rho_bound := fun i _ => h.rho_bound i
  rule := fun i _ => h.rule i

/-- Actual infinite paths retain all original Type I expressions, weights, and
uncropped metadata. No completion of the coding tree is inserted as a path. -/
structure InfinitePath (f : Family) where
  raw : RawPath
  admissible : raw.Admissible
  piece : ℕ → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  successive : ∀ i j, i < j → Successive f (raw.piece i) (raw.piece j)
  children_mem : ∀ i j, (piece i).child j ∈ f.norming

def InfinitePath.prefix {f : Family} (P : InfinitePath f) (n : ℕ) : FinitePath f where
  raw := P.raw
  length := n+1
  length_pos := by omega
  valid := admissible_prefix P.admissible (n+1)
  piece := fun i => P.piece i
  value_eq := fun i => P.value_eq i
  weight_eq := fun i => P.weight_eq i
  mixed_successive := fun i j hij => P.successive i j hij

def FinitePath.oneTerm {f : Family} (P : FinitePath f) (A : Crop) : TypeII f where
  length := 1
  path := fun _ => P
  crop := fun _ => A
  coefficient := fun _ => 1
  bound := by simp
  disjoint_active := fun b c hbc => (hbc (Subsingleton.elim _ _)).elim

@[simp] lemma FinitePath.oneTerm_value {f : Family} (P : FinitePath f) (A : Crop) :
    (P.oneTerm A).value = restrict (A.set f) P.value := by
  change (∑ _b : Fin 1, (1 : ℚ) • restrict (A.set f) P.value) = _
  simp

lemma InfinitePath.prefix_crop_mem {f : Family} (P : InfinitePath f) (n : ℕ) (A : Crop) :
    restrict (A.set f) (P.prefix n).value ∈ f.norming := by
  rw [← FinitePath.oneTerm_value]
  exact TypeII.mem_family _ (fun _ i j => P.children_mem i j)

lemma InfinitePath.prefix_mem {f : Family} (P : InfinitePath f) (n : ℕ) :
    (P.prefix n).value ∈ Full := by
  apply f.norming_subset_full
  simpa only [Crop.all_set, restrict_univ] using P.prefix_crop_mem n Crop.all

lemma InfinitePath.piece_coefficient_unique {f : Family} (P : InfinitePath f)
    {i j : ℕ} {a : Γ} (hi : P.raw.piece i a ≠ 0) (hj : P.raw.piece j a ≠ 0) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := P.admissible.successive i j h a (Finsupp.mem_support_iff.mpr hi)
      a (Finsupp.mem_support_iff.mpr hj)
    exact (lt_irrefl a) this
  · have := P.admissible.successive j i h a (Finsupp.mem_support_iff.mpr hj)
      a (Finsupp.mem_support_iff.mpr hi)
    exact (lt_irrefl a) this

lemma InfinitePath.prefix_at_hit {f : Family} (P : InfinitePath f) (a : Γ) (i n : ℕ)
    (hi : P.raw.piece i a ≠ 0) (hin : i ≤ n) :
    (P.prefix n).value a = P.raw.piece i a := by
  change (∑ j : Fin (n+1), P.raw.piece j) a = _
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (n+1))]
  · intro j _ hji
    by_contra hn
    exact hji (Fin.ext (P.piece_coefficient_unique hn hi))
  · simp

lemma InfinitePath.prefix_coordinate_eventually_constant {f : Family} (P : InfinitePath f)
    (a : Γ) : ∃ q : ℚ, ∀ᶠ n in Filter.atTop, (P.prefix n).value a = q := by
  by_cases h : ∃ i, P.raw.piece i a ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact ⟨P.raw.piece i a, (Filter.eventually_ge_atTop i).mono (fun n hn => P.prefix_at_hit a i n hi hn)⟩
  · push Not at h
    refine ⟨0, Filter.Eventually.of_forall (fun n => ?_)⟩
    change (∑ j : Fin (n+1), P.raw.piece j) a = 0
    simp only [Finsupp.finsetSum_apply, h, Finset.sum_const_zero]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup8 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace8 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

def pathPartial {f : Family} (P : InfinitePath f) (n : ℕ) : StrongDual ℝ E :=
  norming.functional ⟨(P.prefix n).value, P.prefix_mem n⟩

lemma pathPartial_bound {f : Family} (P : InfinitePath f) (n : ℕ) : ‖pathPartial P n‖ ≤ 1 :=
  norming.norm_functional_le _

lemma pathPartial_finite_cauchy {f : Family} (P : InfinitePath f) (x : Γ →₀ ℝ) :
    CauchySeq (fun n => pathPartial P n (norming.includeFinite x)) := by
  choose q hq using P.prefix_coordinate_eventually_constant
  have he : ∀ᶠ n in atTop, pathPartial P n (norming.includeFinite x) =
      x.sum (fun a t => t * (q a : ℝ)) := by
    filter_upwards [(Filter.eventually_all_finset x.support).mpr (fun a _ => hq a)] with n hn
    rw [pathPartial, norming.functional_includeFinite]
    apply Finset.sum_congr rfl
    intro a ha
    change x a * ((P.prefix n).value a : ℝ) = x a * (q a : ℝ)
    rw [hn a ha]
  exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).cauchySeq

lemma exists_pathFunctional {f : Family} (P : InfinitePath f) :
    ∃ F : StrongDual ℝ E, ‖F‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => pathPartial P n x) atTop (𝓝 (F x)) := by
  apply PathLimits.exists_limit_of_dense _ (pathPartial_bound P) _ norming.denseRange_includeFinite
  rintro _ ⟨x, rfl⟩
  exact pathPartial_finite_cauchy P x

/-- Path partial sums are bounded and converge pointwise. -/
def pathFunctional {f : Family} (P : InfinitePath f) : StrongDual ℝ E :=
  (exists_pathFunctional P).choose

lemma norm_pathFunctional_le {f : Family} (P : InfinitePath f) : ‖pathFunctional P‖ ≤ 1 :=
  (exists_pathFunctional P).choose_spec.1

lemma pathPartial_tendsto {f : Family} (P : InfinitePath f) (x : E) :
    Tendsto (fun n => pathPartial P n x) atTop (𝓝 (pathFunctional P x)) :=
  (exists_pathFunctional P).choose_spec.2 x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def InfinitePath.tailCrop {f : Family} (P : InfinitePath f) (N : ℕ) : Crop where
  ordinal := Set.Ioi (P.raw.endpoint N)
  ordinal_convex := Set.ordConnected_Ioi
  colors := Set.univ
  colors_convex := Set.ordConnected_univ

@[simp] lemma InfinitePath.tailCrop_set {f g : Family} (P : InfinitePath f) (N : ℕ) :
    (P.tailCrop N).set g = Set.Ioi (P.raw.endpoint N) := by
  cases g <;> simp [Crop.set, InfinitePath.tailCrop]

lemma InfinitePath.before_endpoint {f : Family} (P : InfinitePath f)
    {N i : ℕ} (hi : i ≤ N) {a : Γ} (ha : a ∈ (P.raw.piece i).support) :
    a ≤ P.raw.endpoint N := P.raw.le_endpoint (P.raw.piece_support_subset hi ha)

lemma InfinitePath.after_endpoint {f : Family} (P : InfinitePath f)
    {N i : ℕ} (hi : N < i) {a : Γ} (ha : a ∈ (P.raw.piece i).support) :
    P.raw.endpoint N < a := by
  obtain ⟨j, hj, he⟩ := (P.raw.mem_support_iff N _).mp (P.raw.endpoint_mem N)
  exact P.admissible.successive j i (hj.trans_lt hi) _ he a ha

lemma InfinitePath.tail_piece {f : Family} (P : InfinitePath f) (N i : ℕ) :
    restrict ((P.tailCrop N).set f) (P.raw.piece i) = if N < i then P.raw.piece i else 0 := by
  ext a
  rw [restrict_apply, tailCrop_set]
  by_cases hai : P.raw.piece i a = 0
  · by_cases hi : N < i <;> simp [hi, hai]
  · have ha := Finsupp.mem_support_iff.mpr hai
    by_cases hi : N < i
    · simp [hi, P.after_endpoint hi ha]
    · have hnot : ¬ P.raw.endpoint N < a := not_lt_of_ge (P.before_endpoint (Nat.le_of_not_gt hi) ha)
      simp [hi, hnot]

lemma InfinitePath.tail_active_subset {f : Family} (P : InfinitePath f) (N n : ℕ) :
    ↑((P.prefix n).active (P.tailCrop N)) ⊆ Set.range (fun i => P.raw.weight (i+N+1)) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  have hi' := (Finset.mem_filter.mp hi).2
  change restrict ((P.tailCrop N).set f) (P.raw.piece i) ≠ 0 at hi'
  rw [P.tail_piece] at hi'
  have hNi : N < (i : ℕ) := by
    by_contra hn
    exact hi' (ite_eq_right hn)
  refine ⟨(i : ℕ)-N-1, ?_⟩
  change P.raw.weight (((i : ℕ)-N-1)+N+1) = P.raw.weight i
  congr 1
  omega

lemma InfinitePath.tail_prefix_coeff {f : Family} (P : InfinitePath f) (N n : ℕ)
    (hn : N ≤ n) :
    restrict ((P.tailCrop N).set f) (P.prefix n).value =
      (P.prefix n).value - (P.prefix N).value := by
  ext a
  rw [restrict_apply, tailCrop_set, Finsupp.sub_apply, Set.mem_Ioi]
  by_cases ha : P.raw.endpoint N < a
  · rw [ite_eq_left ha]
    have hz : (P.prefix N).value a = 0 := by
      change (∑ i : Fin (N+1), P.raw.piece i) a = 0
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_contra h
      exact (not_le_of_gt ha) (P.before_endpoint (by omega) (Finsupp.mem_support_iff.mpr h))
    simp [hz]
  · rw [ite_eq_right ha]
    by_cases hz : (P.prefix n).value a = 0
    · have hzN : (P.prefix N).value a = 0 := by
        by_contra hzN
        have hit := (P.prefix N).value_at_hit a
        change (P.prefix N).value a = P.raw.piece ((P.prefix N).hitIndex a) a at hit
        have hh : P.raw.piece ((P.prefix N).hitIndex a) a ≠ 0 := by rwa [← hit]
        have he := P.prefix_at_hit a ((P.prefix N).hitIndex a) n hh
          (by have := ((P.prefix N).hitIndex a).isLt; change _ < N+1 at this; omega)
        exact hh (he.symm.trans hz)
      simp [hz, hzN]
    · have hit := (P.prefix n).value_at_hit a
      change (P.prefix n).value a = P.raw.piece ((P.prefix n).hitIndex a) a at hit
      have hh : P.raw.piece ((P.prefix n).hitIndex a) a ≠ 0 := by rwa [← hit]
      have hi : ((P.prefix n).hitIndex a : ℕ) ≤ N := by
        by_contra hi
        exact ha (P.after_endpoint (Nat.lt_of_not_ge hi) (Finsupp.mem_support_iff.mpr hh))
      rw [P.prefix_at_hit a _ N hh hi, hit, sub_self]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup9 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace9 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

lemma pathPartial_crop_apply {f : Family} (P : InfinitePath f) (N n : ℕ) (x : E) :
    pathPartial P n (projection (P.tailCrop N) x) =
      norming.evaluateArray x (restrict ((P.tailCrop N).set f) (P.prefix n).value) := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray (norming.projection _ _ x) _ = _
  rw [norming.evaluateArray_projection]
  simp only [InfinitePath.tailCrop_set, restrict]

def pathTail {f : Family} (P : InfinitePath f) (N : ℕ) : StrongDual ℝ E :=
  (pathFunctional P).comp (projection (P.tailCrop N))

lemma pathTail_complement {f : Family} (P : InfinitePath f) (N : ℕ) :
    pathFunctional P - pathTail P N = (norming.rationalPredual (P.prefix N).value).val := by
  ext x
  have ht := (pathPartial_tendsto P x).sub
    (pathPartial_tendsto P (projection (P.tailCrop N) x))
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [pathPartial_crop_apply, P.tail_prefix_coeff N n hn, map_sub]
  rw [norming.evaluateArray_eq_functional x ⟨(P.prefix n).value, P.prefix_mem n⟩]
  change norming.evaluateArray x (P.prefix N).value = _
  simp only [pathPartial]
  ring

lemma pathTail_complement_mem {f : Family} (P : InfinitePath f) (N : ℕ) :
    pathFunctional P - pathTail P N ∈ X₀ := by
  rw [pathTail_complement]
  exact (norming.rationalPredual (P.prefix N).value).property

/-- The exact original coding is retained in all finite tails. -/
lemma rational_tail_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).raw.weight (n+N+1)))
      (Set.range (fun n => (P j).raw.weight (n+N+1)))))
    (c : Fin h → ℚ) (hc : ∑ i, |(c i : ℝ)| ^ f.q ≤ 1) :
    ‖∑ i, (c i : ℝ) • pathTail (P i) N‖ ≤ 1 := by
  let e : ℕ → TypeII f := fun n => {
    length := h
    path := fun i => (P i).prefix n
    crop := fun i => (P i).tailCrop N
    coefficient := c
    bound := hc
    disjoint_active := fun i j hij => Finset.disjoint_left.mpr (fun w hw hw' =>
      Set.disjoint_left.mp (hdis hij) ((P i).tail_active_subset N n hw)
        ((P j).tail_active_subset N n hw')) }
  have he : ∀ n, (e n).value ∈ Full := fun n => f.norming_subset_full
    ((e n).mem_family (fun i j k => (P i).children_mem j k))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ht : Tendsto (fun n => ∑ i, (c i : ℝ) * pathPartial (P i) n
      (projection ((P i).tailCrop N) x)) atTop
      (𝓝 (∑ i, (c i : ℝ) * pathTail (P i) N x)) := by
    apply tendsto_finsetSum _
    intro i _
    exact tendsto_const_nhds.mul (pathPartial_tendsto (P i) _)
  have hb : ∀ n, ‖∑ i, (c i : ℝ) * pathPartial (P i) n
      (projection ((P i).tailCrop N) x)‖ ≤ ‖x‖ := by
    intro n
    have heq : norming.evaluateArray x (e n).value = ∑ i, (c i : ℝ) *
        pathPartial (P i) n (projection ((P i).tailCrop N) x) := by
      simp only [e, TypeII.value, map_sum, map_rat_smul, Rat.smul_def,
        pathPartial_crop_apply]
    rw [← heq, norming.evaluateArray_eq_functional x ⟨(e n).value, he n⟩]
    exact PathLimits.unit_bound _ (norming.norm_functional_le _) x
  simpa only [sum_apply, smul_apply,
    smul_eq_mul, one_mul] using le_of_tendsto ht.norm (Eventually.of_forall hb)

end SeparableQuotient.ActualSpace

end

end OAI
