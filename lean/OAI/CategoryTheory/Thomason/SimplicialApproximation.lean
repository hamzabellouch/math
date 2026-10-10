import Mathlib
import OAI.CategoryTheory.Thomason.BarycentricMesh
import OAI.CategoryTheory.Thomason.CoherentGluing

namespace OAI

/-! Simplicial Approximation. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
local instance polyMapsDecEqP : DecidableEq P := Classical.decEq P
local instance polyMapsDecEqQ : DecidableEq Q := Classical.decEq Q

def vertex (p : P) : PolyPoint P where
  weights := Finsupp.single p 1
  nonneg q := by simp [Finsupp.single_apply]; positivity
  total := by simp
  chain := by simp

@[simp] lemma vertex_weights (p q : P) : (vertex p).weights q = if p = q then 1 else 0 := by
  simp [vertex, Finsupp.single_apply]

@[simp] lemma vertex_support (p : P) : (vertex p).weights.support = {p} := by
  simp [vertex]

@[simp] lemma barycenter_support (s : NonemptyFiniteChains P) :
    (barycenter s).weights.support = s.finset := by
  ext p
  rw [Finsupp.mem_support_iff, barycenter_apply]
  split_ifs with hp
  · simp only [hp, iff_true]
    exact inv_ne_zero (by exact_mod_cast Finset.card_ne_zero.mpr s.nonempty)
  · simp [hp]

def PreservesChains (f : P → Q) : Prop :=
  ∀ s : NonemptyFiniteChains P, IsChain (· ≤ ·) ((s.finset.image f : Finset Q) : Set Q)

lemma preservesChains_monotone (f : P →o Q) : PreservesChains f := by
  intro s a ha b hb hab
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hb
  exact (s.comparable ⟨p,hp⟩ ⟨q,hq⟩).imp
    (fun h => f.monotone (show p ≤ q from h))
    (fun h => f.monotone (show q ≤ p from h))

def map (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) : PolyPoint Q where
  weights := x.weights.mapDomain f
  nonneg q := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    apply Finset.sum_nonneg
    intro p hp
    simp only [Finsupp.single_apply]
    split_ifs <;> first | exact x.nonneg p | exact le_rfl
  total := by
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact x.total
  chain := by
    exact IsChain.mono Finsupp.mapDomain_support
      (hf ⟨x.weights.support, (supportIndex x).nonempty,
        fun p q => x.chain.total p.property q.property⟩)

lemma map_support (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) :
    (map f hf x).weights.support ⊆ x.weights.support.image f := Finsupp.mapDomain_support

lemma map_apply (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) (q : Q) :
    (map f hf x).weights q = x.weights.sum (fun p r => if f p = q then r else 0) := by
  simp only [map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]

lemma continuous_map (f : P → Q) (hf : PreservesChains f) : Continuous (map f hf) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  apply continuous_of_finite_carrier
    (fun x : Face s.carrier => map f hf x.val) (s.carrier.image f)
  · intro x q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (map_support f hf x.val hq)
    exact Finset.mem_image.mpr ⟨p,x.property hp,rfl⟩
  · intro q
    have he (x : Face s.carrier) : (map f hf x.val).weights q =
        ∑ p ∈ s.carrier, if f p = q then x.val.weights p else 0 := by
      rw [map_apply]
      exact Finsupp.sum_of_support_subset _ x.property _ (by simp)
    apply Continuous.congr _ (fun x => (he x).symm)
    apply continuous_finsetSum
    intro p hp
    by_cases h : f p = q
    · simpa only [h, ite_true, Function.comp_def] using
        ((continuous_apply p).comp continuous_induced_dom :
          Continuous (fun x : Face s.carrier => x.val.weights p))
    · simp only [h, ite_false]
      exact continuous_const

@[simp] lemma map_vertex (f : P → Q) (hf : PreservesChains f) (p : P) :
    map f hf (vertex p) = vertex (f p) := by
  apply PolyPoint.ext
  simp [map,vertex]

def segment (x y : PolyPoint P)
    (h : IsChain (· ≤ ·) ((x.weights.support ∪ y.weights.support : Finset P) : Set P))
    (t : unitInterval) : PolyPoint P where
  weights := (1 - t.val) • x.weights + t.val • y.weights
  nonneg p := by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (x.nonneg p))
      (mul_nonneg t.property.1 (y.nonneg p))
  total := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_smul_index (fun _ => rfl), Finsupp.sum_smul_index (fun _ => rfl)]
    have hx : ∑ p ∈ x.weights.support, x.weights p = 1 := x.total
    have hy : ∑ p ∈ y.weights.support, y.weights p = 1 := y.total
    change (∑ p ∈ x.weights.support, (1 - t.val) * x.weights p) +
      (∑ p ∈ y.weights.support, t.val * y.weights p) = 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
    ring
  chain := IsChain.mono (by
    intro p hp
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
    · exact Finset.mem_union_left _ (Finsupp.support_smul hp)
    · exact Finset.mem_union_right _ (Finsupp.support_smul hp)) h

@[simp] lemma segment_zero (x y : PolyPoint P) (h) : segment x y h 0 = x := by
  apply PolyPoint.ext
  simp [segment]

@[simp] lemma segment_one (x y : PolyPoint P) (h) : segment x y h 1 = y := by
  apply PolyPoint.ext
  simp [segment]

lemma segment_support (x y : PolyPoint P) (h) (t : unitInterval) :
    (segment x y h t).weights.support ⊆ x.weights.support ∪ y.weights.support := by
  intro p hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
  · exact Finset.mem_union_left _ (Finsupp.support_smul hp)
  · exact Finset.mem_union_right _ (Finsupp.support_smul hp)

lemma segment_self (x : PolyPoint P) (h) (t : unitInterval) : segment x x h t = x := by
  apply PolyPoint.ext
  change (1 - t.val) • x.weights + t.val • x.weights = x.weights
  rw [← add_smul]
  simp

lemma exists_greatest (s : NonemptyFiniteChains P) :
    ∃ p ∈ s.finset, ∀ q ∈ s.finset, q ≤ p := by
  obtain ⟨p,hp,hm⟩ := s.finset.exists_maximal s.nonempty
  refine ⟨p,hp,fun q hq => ?_⟩
  rcases s.comparable ⟨q,hq⟩ ⟨p,hp⟩ with h | h
  · exact h
  · exact hm hq h

def greatest (s : NonemptyFiniteChains P) : P := (exists_greatest s).choose

lemma greatest_mem (s : NonemptyFiniteChains P) : greatest s ∈ s.finset :=
  (exists_greatest s).choose_spec.1

lemma le_greatest (s : NonemptyFiniteChains P) (p : P) (hp : p ∈ s.finset) :
    p ≤ greatest s := (exists_greatest s).choose_spec.2 p hp

lemma greatest_mono {s t : NonemptyFiniteChains P} (h : s ≤ t) :
    greatest s ≤ greatest t := le_greatest t _ (h (greatest_mem s))

def imageChain (f : P → Q) (hf : PreservesChains f) (s : NonemptyFiniteChains P) :
    NonemptyFiniteChains Q where
  finset := s.finset.image f
  nonempty := s.nonempty.image f
  comparable a b := (hf s).total a.property b.property

def orientedMap (f : P → Q) (hf : PreservesChains f) : NonemptyFiniteChains P →o Q where
  toFun s := greatest (imageChain f hf s)
  monotone' _ _ h := greatest_mono (Finset.image_subset_image h)

lemma orientedMap_mem (f : P → Q) (hf : PreservesChains f) (s : NonemptyFiniteChains P) :
    ∃ p ∈ s.finset, orientedMap f hf s = f p := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (greatest_mem (imageChain f hf s))
  exact ⟨p,hp,he.symm⟩

lemma oriented_support (f : P → Q) (hf : PreservesChains f)
    (x : PolyPoint (NonemptyFiniteChains P)) :
    (map (orientedMap f hf) (preservesChains_monotone _) x).weights.support ⊆
      (subdivide x).weights.support.image f := by
  intro q hq
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (map_support _ _ x hq)
  obtain ⟨p,hp,he⟩ := orientedMap_mem f hf s
  apply Finset.mem_image.mpr
  refine ⟨p,?_,he.symm⟩
  change p ∈ (barycentricLinear x.weights).support
  rw [barycentricLinear_support_eq x.weights x.nonneg]
  exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩

def carrierHomotopy {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f g : C(A, PolyPoint P))
    (h : ∀ a, IsChain (· ≤ ·) (((f a).weights.support ∪ (g a).weights.support : Finset P) : Set P)) :
    f.Homotopy g where
  toFun z := segment (f z.2) (g z.2) (h z.2) z.1
  continuous_toFun := by
    obtain ⟨s,hs⟩ := compact_finite_carrier (isCompact_range f.continuous)
    obtain ⟨t,ht⟩ := compact_finite_carrier (isCompact_range g.continuous)
    apply continuous_of_finite_carrier _ (s ∪ t)
    · intro z p hp
      rcases Finset.mem_union.mp (segment_support _ _ _ _ hp) with hp | hp
      · exact Finset.mem_union_left _ (hs _ ⟨z.2,rfl⟩ hp)
      · exact Finset.mem_union_right _ (ht _ ⟨z.2,rfl⟩ hp)
    · intro p
      have ht : Continuous (fun z : unitInterval × A => (z.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub ht).mul ((continuous_weights p).comp
        (f.continuous.comp continuous_snd))).add
        (ht.mul ((continuous_weights p).comp (g.continuous.comp continuous_snd)))
  map_zero_left a := segment_zero _ _ _
  map_one_left a := segment_one _ _ _

lemma carrierHomotopy_fixed {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f g : C(A, PolyPoint P)) (h) (a : A) (ha : f a = g a) (t : unitInterval) :
    carrierHomotopy f g h (t,a) = f a := by
  change segment (f a) (g a) (h a) t = f a
  apply PolyPoint.ext
  change (1 - t.val) • (f a).weights + t.val • (g a).weights = (f a).weights
  rw [← ha, ← add_smul]
  simp

lemma eq_vertex_of_support_subset (x : PolyPoint P) (p : P)
    (h : x.weights.support ⊆ {p}) : x = vertex p := by
  have ht : x.weights p = 1 := by
    calc
      x.weights p = x.weights.sum (fun _ r => r) := by
        symm
        convert Finsupp.sum_of_support_subset x.weights h (fun _ r => r) (by simp) using 1
        simp
      _ = 1 := x.total
  apply PolyPoint.ext
  ext q
  by_cases hpq : p = q
  · subst q
    simpa only [vertex_weights, ite_true] using ht
  · have hq : q ∉ x.weights.support := fun hq => hpq (Finset.mem_singleton.mp (h hq)).symm
    simpa only [vertex_weights, ite_eq_right hpq] using Finsupp.notMem_support_iff.mp hq

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Approximation
open PolyPoint Mesh
variable {P : Type u} [PartialOrder P]
local instance approximationDecEqP : DecidableEq P := Classical.decEq P

def coordinateVertex (p : P) : P → ℝ := fun q => if p = q then 1 else 0

lemma evaluate_coordinates [Fintype P] (x : PolyPoint P) :
    evaluate coordinateVertex x = fun p => x.weights p := by
  classical
  funext p
  rw [evaluate_eq_sum, Finset.sum_apply]
  simp [coordinateVertex, smul_eq_mul, mul_ite]
  exact fun h => h.symm

lemma evaluate_vertex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : P → V) (p : P) : evaluate v (vertex p) = v p := by
  simp [evaluate,vertex]

omit [PartialOrder P] in
lemma norm_coordinateVertex_le [Fintype P] (p : P) : ‖coordinateVertex p‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro q
  simp only [coordinateVertex]
  split_ifs <;> norm_num

lemma bound_coordinates [Fintype P] : Bound (@coordinateVertex P) 2 := by
  intro p q hpq
  exact (norm_sub_le _ _).trans (by linarith [norm_coordinateVertex_le p, norm_coordinateVertex_le q])

lemma coordinate_level (P : PartOrd.{u}) [Fintype P] (n : ℕ)
    (x : PolyPoint (level P n)) :
    (fun p => (levelHomeomorph P n x).weights p) = evaluate (levelVertices P coordinateVertex n) x := by
  rw [← evaluate_coordinates, evaluate_levelHomeomorph]

lemma coordinate_level_vertex (P : PartOrd.{u}) [Fintype P] (n : ℕ) (p : level P n) :
    (fun q => (levelHomeomorph P n (vertex p)).weights q) = levelVertices P coordinateVertex n p := by
  rw [coordinate_level, evaluate_vertex]

theorem exists_star_labels (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ labels : level P n → Q,
      ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        labels p ∈ (f (levelHomeomorph P n x)).weights.support := by
  let : MetricSpace (PolyPoint P) :=
    embedding_weights.comapMetricSpace (fun x : PolyPoint P => (fun p => x.weights p))
  let U (q : Q) : Set (PolyPoint P) := {x | 0 < (f x).weights q}
  have hU (q : Q) : IsOpen (U q) := isOpen_lt continuous_const
    ((continuous_weights q).comp f.continuous)
  have hcover : (Set.univ : Set (PolyPoint P)) ⊆ ⋃ q, U q := by
    intro x hx
    obtain ⟨q,hq⟩ := (supportIndex (f x)).nonempty
    refine Set.mem_iUnion.mpr ⟨q,?_⟩
    exact lt_of_le_of_ne ((f x).nonneg q) (Ne.symm (Finsupp.mem_support_iff.mp hq))
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  have hdim : ChainBound P (Fintype.card P + 1) := by
    intro s
    exact (Finset.card_le_univ s.finset).trans (Nat.le_succ _)
  obtain ⟨n,e,he0,heδ,he⟩ := exists_small_mesh P coordinateVertex 2 (by norm_num)
    bound_coordinates (Nat.succ_pos _) hdim hδ
  have hv (p : level P n) : ∃ q, Metric.ball (levelHomeomorph P n (vertex p)) δ ⊆ U q :=
    hLeb _ (Set.mem_univ _)
  choose labels hlabels using hv
  refine ⟨n,labels,fun x p hp => ?_⟩
  have hball : levelHomeomorph P n x ∈ Metric.ball (levelHomeomorph P n (vertex p)) δ := by
    change dist (fun q => (levelHomeomorph P n x).weights q)
      (fun q => (levelHomeomorph P n (vertex p)).weights q) < δ
    rw [dist_eq_norm, coordinate_level, coordinate_level_vertex]
    exact (norm_evaluate_sub_le _ x _ e (fun q hq => he q p (x.chain.total hq hp))).trans_lt heδ
  exact Finsupp.mem_support_iff.mpr (ne_of_gt (hlabels p hball))

lemma labels_preserve_chains (P : PartOrd.{u}) {Q : Type v} [PartialOrder Q]
    (f : PolyPoint P → PolyPoint Q) (n : ℕ) (labels : level P n → Q)
    (hlabels : ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
      labels p ∈ (f (levelHomeomorph P n x)).weights.support) : PreservesChains labels := by
  classical
  intro s q hq r hr hqr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hr
  apply (f (levelHomeomorph P n (barycenter s))).chain.total
  · exact hlabels _ p (by simpa only [barycenter_support] using hp)
  · exact hlabels _ p' (by simpa only [barycenter_support] using hp')

theorem exists_oriented_approximation (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∀ x : PolyPoint (level P n),
        (PolyPoint.map a (preservesChains_monotone a) x).weights.support ⊆
          (f (levelHomeomorph P n x)).weights.support := by
  obtain ⟨n,labels,hlabels⟩ := exists_star_labels P f
  let ha := labels_preserve_chains P f n labels hlabels
  refine ⟨n+1, orientedMap labels ha, fun x q hq => ?_⟩
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (oriented_support labels ha x hq)
  exact hlabels (subdivide x) p hp

def affineMap {A : Type*} [PartialOrder A] {Q : Type*} [PartialOrder Q]
    (a : A →o Q) : C(PolyPoint A, PolyPoint Q) :=
  ⟨PolyPoint.map a (preservesChains_monotone a), continuous_map _ _⟩

theorem relative_approximation (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f : C(PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∃ H : (affineMap a).Homotopy (f.comp ⟨levelHomeomorph P n, (levelHomeomorph P n).continuous⟩),
        (∀ x, (affineMap a x).weights.support ⊆ (f (levelHomeomorph P n x)).weights.support) ∧
        (∀ x q, f (levelHomeomorph P n x) = vertex q →
          ∀ t : unitInterval, H (t,x) = vertex q) := by
  obtain ⟨n,a,ha⟩ := exists_oriented_approximation P f
  let g := f.comp ⟨levelHomeomorph P n, (levelHomeomorph P n).continuous⟩
  have hc (x : PolyPoint (level P n)) :
      IsChain (· ≤ ·) (((affineMap a x).weights.support ∪ (g x).weights.support : Finset Q) : Set Q) := by
    change IsChain (· ≤ ·) (((PolyPoint.map a (preservesChains_monotone a) x).weights.support ∪
      (f (levelHomeomorph P n x)).weights.support : Finset Q) : Set Q)
    rw [Finset.union_eq_right.mpr (ha x)]
    exact (g x).chain
  let H := carrierHomotopy (affineMap a) g hc
  refine ⟨n,a,H,ha,fun x q hx t => ?_⟩
  have he : affineMap a x = vertex q := eq_vertex_of_support_subset _ q (by
    have hh := ha x
    rw [hx, vertex_support] at hh
    exact hh)
  exact (carrierHomotopy_fixed (affineMap a) g hc x (he.trans hx.symm) t).trans he
end Approximation
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
local instance : DecidableEq Q := Classical.decEq Q

structure ChainMap (P : Type u) (Q : Type v) [PartialOrder P] [PartialOrder Q] where
  toFun : P → Q
  chains : PreservesChains toFun
instance : CoeFun (ChainMap P Q) (fun _ => P → Q) := ⟨ChainMap.toFun⟩

def Contiguous (f g : ChainMap P Q) : Prop :=
  ∀ s : NonemptyFiniteChains P,
    IsChain (· ≤ ·) (((s.finset.image f.toFun ∪ s.finset.image g.toFun : Finset Q)) : Set Q)

def Related (f g : ChainMap P Q) : Prop := Relation.EqvGen Contiguous f g

def chainMapSetoid (P : Type u) (Q : Type v) [PartialOrder P] [PartialOrder Q] :
    Setoid (ChainMap P Q) where
  r := Related
  iseqv := ⟨fun _ => Relation.EqvGen.refl _,fun h => Relation.EqvGen.symm _ _ h,
    fun h h' => Relation.EqvGen.trans _ _ _ h h'⟩

lemma contiguous_of_carrier (f g : ChainMap P Q) (h : PolyPoint P → PolyPoint Q)
    (hf : ∀ x, ∀ p ∈ x.weights.support, f p ∈ (h x).weights.support)
    (hg : ∀ x, ∀ p ∈ x.weights.support, g p ∈ (h x).weights.support) :
    Contiguous f g := by
  classical
  intro s
  apply IsChain.mono (t := ((h (barycenter s)).weights.support : Set Q)) _
    (h (barycenter s)).chain
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hf _ p (by simpa only [barycenter_support] using hp)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hg _ p (by simpa only [barycenter_support] using hp)

theorem homotopy_star_labels (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (H : C(unitInterval × PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ labels : unitInterval → level P n → Q,
      ∀ t s : unitInterval, dist t s < δ →
        ∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
          labels s p ∈ (H (t,levelHomeomorph P n x)).weights.support := by
  let : MetricSpace (PolyPoint P) := embedding_weights.comapMetricSpace
    (fun x : PolyPoint P => (fun p => x.weights p))
  let U (q : Q) : Set (unitInterval × PolyPoint P) := {x | 0 < (H x).weights q}
  have hU (q : Q) : IsOpen (U q) := isOpen_lt continuous_const
    ((continuous_weights q).comp H.continuous)
  have hcover : (Set.univ : Set (unitInterval × PolyPoint P)) ⊆ ⋃ q, U q := by
    intro x hx
    obtain ⟨q,hq⟩ := (supportIndex (H x)).nonempty
    exact Set.mem_iUnion.mpr ⟨q,lt_of_le_of_ne ((H x).nonneg q)
      (Ne.symm (Finsupp.mem_support_iff.mp hq))⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  have hdim : ChainBound P (Fintype.card P + 1) := fun s =>
    (Finset.card_le_univ s.finset).trans (Nat.le_succ _)
  obtain ⟨n,e,he0,heδ,he⟩ := exists_small_mesh P coordinateVertex 2 (by norm_num)
    bound_coordinates (Nat.succ_pos _) hdim hδ
  have hv (t : unitInterval) (p : level P n) : ∃ q,
      Metric.ball (t,levelHomeomorph P n (vertex p)) δ ⊆ U q :=
    hLeb _ (Set.mem_univ _)
  choose labels hlabels using hv
  refine ⟨n,δ,hδ,labels,fun t s hts x p hp => ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply ne_of_gt
  apply hlabels s p
  change max (dist t s) (dist (fun q => (levelHomeomorph P n x).weights q)
    (fun q => (levelHomeomorph P n (vertex p)).weights q)) < δ
  apply max_lt hts
  rw [dist_eq_norm,coordinate_level,coordinate_level_vertex]
  exact (norm_evaluate_sub_le _ x _ e (fun q hq => he q p
    (x.chain.total hq hp))).trans_lt heδ

theorem homotopy_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (H : C(unitInterval × PolyPoint P, PolyPoint Q)) :
    ∃ n : ℕ, ∃ f g : ChainMap (level P n) Q,
      Related f g ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        f p ∈ (H (0,levelHomeomorph P n x)).weights.support) ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        g p ∈ (H (1,levelHomeomorph P n x)).weights.support) := by
  obtain ⟨n,δ,hδ,labels,hl⟩ := homotopy_star_labels P H
  have hs (t : unitInterval) := hl t t (by simpa using hδ)
  let f (t : unitInterval) : ChainMap (level P n) Q :=
    ⟨labels t,labels_preserve_chains P (fun x => H (t,x)) n (labels t) (hs t)⟩
  let F (t : unitInterval) : Quotient (chainMapSetoid (level P n) Q) := Quotient.mk _ (f t)
  have hF : IsLocallyConstant F := by
    intro A
    rw [Metric.isOpen_iff]
    intro t ht
    refine ⟨δ,hδ,fun s hst => ?_⟩
    have he : F s = F t := Quotient.sound (Relation.EqvGen.rel _ _
      (contiguous_of_carrier (f s) (f t) (fun x => H (t,levelHomeomorph P n x))
        (hl t s (by simpa only [Metric.mem_ball,dist_comm] using hst)) (hs t)))
    change F s ∈ A
    rw [he]
    exact ht
  have h01 : F 0 = F 1 := by
    exact congrFun (hF.eq_const 1) 0
  exact ⟨n,f 0,f 1,show Related (f 0) (f 1) from Quotient.exact h01,hs 0,hs 1⟩

def last (P : PartOrd.{u}) : (n : ℕ) → level P n →o P
  | 0 => OrderHom.id
  | n+1 => (last P n).comp ⟨greatest,fun _ _ h => greatest_mono h⟩

lemma last_support (P : PartOrd.{u}) (n : ℕ) (x : PolyPoint (level P n))
    (p : level P n) (hp : p ∈ x.weights.support) :
    last P n p ∈ (levelHomeomorph P n x).weights.support := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    apply ih (subdivide x) (greatest p)
    change greatest p ∈ (barycentricLinear x.weights).support
    rw [barycentricLinear_support_eq x.weights x.nonneg]
    exact Finset.mem_biUnion.mpr ⟨p,hp,greatest_mem p⟩

lemma map_support_image (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P)
    (p : P) (hp : p ∈ x.weights.support) : f p ∈ (PolyPoint.map f hf x).weights.support := by
  classical
  apply Finsupp.mem_support_iff.mpr
  apply ne_of_gt
  rw [map_apply]
  have ht : 0 < x.weights p := lt_of_le_of_ne (x.nonneg p)
    (Ne.symm (Finsupp.mem_support_iff.mp hp))
  apply lt_of_lt_of_le ht
  change x.weights p ≤ ∑ q ∈ x.weights.support, if f q = f p then x.weights q else 0
  calc
    _ = if f p = f p then x.weights p else 0 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun q : P => if f q = f p then x.weights q else 0) (fun q hq => by
      split_ifs
      · exact x.nonneg q
      · exact le_rfl) hp

def toChainMap (f : P →o Q) : ChainMap P Q := ⟨f,preservesChains_monotone f⟩

theorem homotopy_subdivision_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f g : P →o Q)
    (H : (affineMap f).Homotopy (affineMap g)) :
    ∃ n : ℕ, Related (toChainMap (f.comp (last P n)))
      (toChainMap (g.comp (last P n))) := by
  obtain ⟨n,a,b,hab,ha,hb⟩ := homotopy_contiguity P H.toContinuousMap
  have hf (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (f.comp (last P n)) p ∈
        (H (0,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_zero]
    exact map_support_image f (preservesChains_monotone f) _ _ (last_support P n x p hp)
  have hg (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (g.comp (last P n)) p ∈
        (H (1,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_one]
    exact map_support_image g (preservesChains_monotone g) _ _ (last_support P n x p hp)
  refine ⟨n,Relation.EqvGen.trans _ a _ ?_ (Relation.EqvGen.trans _ b _ hab ?_)⟩
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier _ a _ hf ha)
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier b _ _ hb hg)
end Contiguity
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
local instance : DecidableEq Q := Classical.decEq Q

def unionChain (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    NonemptyFiniteChains Q where
  finset := s.finset.image f.toFun ∪ s.finset.image g.toFun
  nonempty := (s.nonempty.image f.toFun).mono Finset.subset_union_left
  comparable a b := (h s).total a.property b.property

def upperMap (f g : ChainMap P Q) (h : Contiguous f g) : NonemptyFiniteChains P →o Q where
  toFun s := greatest (unionChain f g h s)
  monotone' _ _ hst := greatest_mono (Finset.union_subset_union
    (Finset.image_subset_image hst) (Finset.image_subset_image hst))

lemma left_le_upper (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    orientedMap f.toFun f.chains s ≤ upperMap f g h s := by
  exact le_greatest (unionChain f g h s) _
    (Finset.mem_union_left _ (greatest_mem (imageChain f.toFun f.chains s)))
lemma right_le_upper (f g : ChainMap P Q) (h : Contiguous f g) (s : NonemptyFiniteChains P) :
    orientedMap g.toFun g.chains s ≤ upperMap f g h s := by
  exact le_greatest (unionChain f g h s) _
    (Finset.mem_union_right _ (greatest_mem (imageChain g.toFun g.chains s)))

lemma contiguous_nerve (f g : ChainMap P Q) (h : Contiguous f g) :
    LastVertexProof.Homotopic
      (nerveMap (orientedMap f.toFun f.chains).toFunctor)
      (nerveMap (orientedMap g.toFun g.chains).toFunctor) := by
  apply LastVertexProof.homotopic_trans
    (LastVertexProof.homotopic_of_homotopy
      (HornSubdivision.orderHomotopy _ _ (left_le_upper f g h)))
  exact LastVertexProof.homotopic_symm (LastVertexProof.homotopic_of_homotopy
    (HornSubdivision.orderHomotopy _ _ (right_le_upper f g h)))

lemma related_nerve (f g : ChainMap P Q) (h : Related f g) :
    LastVertexProof.Homotopic
      (nerveMap (orientedMap f.toFun f.chains).toFunctor)
      (nerveMap (orientedMap g.toFun g.chains).toFunctor) := by
  induction h with
  | rel f g h => exact contiguous_nerve f g h
  | refl f => exact LastVertexProof.homotopic_refl _
  | symm f g h ih => exact LastVertexProof.homotopic_symm ih
  | trans f g h hfg hgh ih ih' => exact LastVertexProof.homotopic_trans ih ih'

lemma orientedMap_monotone (f : P →o Q) (s : NonemptyFiniteChains P) :
    orientedMap f (preservesChains_monotone f) s = f (greatest s) := by
  apply le_antisymm
  · obtain ⟨p,hp,he⟩ := orientedMap_mem f (preservesChains_monotone f) s
    rw [he]
    exact f.monotone (le_greatest s p hp)
  · exact le_greatest (imageChain f (preservesChains_monotone f) s) _
      (Finset.mem_image.mpr ⟨greatest s,greatest_mem s,rfl⟩)

theorem geometric_homotopy_detected (P : PartOrd.{u}) [Fintype P]
    {Q : Type u} [PartialOrder Q] (f g : P →o Q)
    (H : (affineMap f).Homotopy (affineMap g)) :
    ∃ n : ℕ, LastVertexProof.Homotopic (nerveMap (f.comp (last P n)).toFunctor)
      (nerveMap (g.comp (last P n)).toFunctor) := by
  obtain ⟨n,hn⟩ := homotopy_subdivision_contiguity P f g H
  have hh := related_nerve _ _ hn
  have hf : orientedMap (toChainMap (f.comp (last P n))).toFun
      (toChainMap (f.comp (last P n))).chains = f.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (f.comp (last P n)) s
  have hg : orientedMap (toChainMap (g.comp (last P n))).toFun
      (toChainMap (g.comp (last P n))).chains = g.comp (last P (n+1)) := by
    ext s
    exact orientedMap_monotone (g.comp (last P n)) s
  exact ⟨n+1,by rwa [hf,hg] at hh⟩
end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

namespace Thomason.TopologicalHorn

lemma anodyne_realization_retract {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    ∃ r : SSet.toTop.obj B ⟶ SSet.toTop.obj A,
      SSet.toTop.map i ≫ r = 𝟙 _ ∧
      (SSet.toTop.map i ≫ r ≫ SSet.toTop.map i).hom = (SSet.toTop.map i).hom ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((SSet.toTop.map i).hom.comp r.hom) (ContinuousMap.id _)
        (Set.range (SSet.toTop.map i))) := by
  let j := SSet.toTop.map i
  obtain ⟨r,hr⟩ := anodyne_top_extension i hi (SSet.toTop.obj A) (𝟙 _)
  have hre (a : SSet.toTop.obj A) : r (j a) = a := ConcreteCategory.congr_hom hr a
  let f : SSet.toTop.obj A ⟶ PathSpace (SSet.toTop.obj B) :=
    TopCat.ofHom (ContinuousMap.const'.comp j.hom)
  let g : SSet.toTop.obj B ⟶ EndpointSpace (SSet.toTop.obj B) :=
    TopCat.ofHom ⟨fun b => (j (r b),b), (j.hom.continuous.comp r.hom.continuous).prodMk continuous_id⟩
  have sq : CommSq f j (pathEndpoints (SSet.toTop.obj B)) g := by
    constructor
    apply ConcreteCategory.hom_ext
    intro a
    change (j a,j a) = (j (r (j a)),j a)
    rw [hre]
  let : HasLiftingProperty j (pathEndpoints (SSet.toTop.obj B)) :=
    (sSetTopAdj.hasLiftingProperty_iff i _).mpr (hi _ (singular_path_fibration _))
  have hzero (b : SSet.toTop.obj B) : sq.lift b 0 = j (r b) :=
    congrArg Prod.fst (ConcreteCategory.congr_hom sq.fac_right b)
  have hone (b : SSet.toTop.obj B) : sq.lift b 1 = b :=
    congrArg Prod.snd (ConcreteCategory.congr_hom sq.fac_right b)
  have hfixed (a : SSet.toTop.obj A) (t : I) : sq.lift (j a) t = j a :=
    congrArg (fun γ : C(I,SSet.toTop.obj B) => γ t) (ConcreteCategory.congr_hom sq.fac_left a)
  refine ⟨r,hr,by simp only [← Category.assoc,hr,Category.id_comp],?_⟩
  refine ⟨{ toHomotopy :=
    { toFun := fun q => sq.lift q.2 q.1
      continuous_toFun := ?_
      map_zero_left := hzero
      map_one_left := hone }
            prop' := ?_ }⟩
  · exact continuous_eval.comp ((sq.lift.hom.continuous.comp continuous_snd).prodMk continuous_fst)
  · rintro t b ⟨a,rfl⟩
    change sq.lift (j a) t = j (r (j a))
    rw [hre]
    exact hfixed a t

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal

lemma homotopic_sections {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (u₀ u₁ : C(X,Y)) (p r : C(Y,X))
    (h₀ : p.comp u₀ = ContinuousMap.id _) (h₁ : p.comp u₁ = ContinuousMap.id _)
    (H : (u₀.comp r).Homotopic (ContinuousMap.id _)) : u₀.Homotopic u₁ := by
  have h : (u₀.comp (r.comp u₁)).Homotopic u₁ := H.comp (.refl u₁)
  have hh := ContinuousMap.Homotopic.comp (.refl p) h
  simp only [← ContinuousMap.comp_assoc,h₀,h₁,ContinuousMap.id_comp] at hh
  exact (ContinuousMap.Homotopic.comp (.refl u₀) hh).symm.trans h

lemma realization_endpoints_homotopic (A : SSet.{u}) :
    ContinuousMap.Homotopic (SSet.toTop.map (SSet.ι₀ (X := A))).hom
      (SSet.toTop.map (SSet.ι₁ (X := A))).hom := by
  obtain ⟨r,hr,_,⟨H⟩⟩ := TopologicalHorn.anodyne_realization_retract
    (SSet.ι₀ (X := A)) (SimplicialCylinder.endpoint_anodyne A).1
  apply homotopic_sections _ _ (SSet.toTop.map (fst A Δ[1])).hom r.hom
    _ _ ⟨H.toHomotopy⟩
  · change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map (fst A Δ[1])).hom = _
    rw [← Functor.map_comp,SSet.ι₀_fst,CategoryTheory.Functor.map_id]
    rfl
  · change (SSet.toTop.map SSet.ι₁ ≫ SSet.toTop.map (fst A Δ[1])).hom = _
    rw [← Functor.map_comp,SSet.ι₁_fst,CategoryTheory.Functor.map_id]
    rfl

lemma realization_homotopic {A B : SSet.{u}} {f g : A ⟶ B}
    (H : Homotopic f g) :
    ContinuousMap.Homotopic (SSet.toTop.map f).hom (SSet.toTop.map g).hom := by
  induction H with
  | rel f g H =>
    obtain ⟨H⟩ := H
    have h := ContinuousMap.Homotopic.comp (.refl (SSet.toTop.map H.h).hom)
      (realization_endpoints_homotopic A)
    have h₀ : (SSet.toTop.map H.h).hom.comp (SSet.toTop.map SSet.ι₀).hom =
        (SSet.toTop.map f).hom := by
      change (SSet.toTop.map SSet.ι₀ ≫ SSet.toTop.map H.h).hom = _
      rw [← Functor.map_comp,H.h₀]
    have h₁ : (SSet.toTop.map H.h).hom.comp (SSet.toTop.map SSet.ι₁).hom =
        (SSet.toTop.map g).hom := by
      change (SSet.toTop.map SSet.ι₁ ≫ SSet.toTop.map H.h).hom = _
      rw [← Functor.map_comp,H.h₁]
    rwa [h₀,h₁] at h
  | refl f => exact .refl _
  | symm f g H ih => exact ih.symm
  | trans f g h H H' ih ih' => exact ih.trans ih'

lemma adjunct_homotopic {A : SSet.{u}} {T : TopCat.{u}}
    {f g : A ⟶ TopCat.toSSet.obj T} (H : Homotopic f g) :
    ContinuousMap.Homotopic ((sSetTopAdj.homEquiv A T).symm f).hom
      ((sSetTopAdj.homEquiv A T).symm g).hom := by
  exact ContinuousMap.Homotopic.comp (.refl (sSetTopAdj.counit.app T).hom)
    (realization_homotopic H)

lemma local_realization_heq {A B : SSet.{u}} (f : A ⟶ B) (hf : Local f) :
    ∃ r : SSet.toTop.obj B ⟶ SSet.toTop.obj A,
      ContinuousMap.Homotopic ((SSet.toTop.map f ≫ r).hom) (ContinuousMap.id _) ∧
      ContinuousMap.Homotopic ((r ≫ SSet.toTop.map f).hom) (ContinuousMap.id _) := by
  let : SSet.KanComplex ((SSet.toTop ⋙ TopCat.toSSet).obj A) :=
    TopologicalHorn.singular_kan (SSet.toTop.obj A)
  let : SSet.KanComplex ((SSet.toTop ⋙ TopCat.toSSet).obj B) :=
    TopologicalHorn.singular_kan (SSet.toTop.obj B)
  let : SSet.KanComplex (TopCat.toSSet.obj (SSet.toTop.obj B)) :=
    TopologicalHorn.singular_kan (SSet.toTop.obj B)
  obtain ⟨g,hg⟩ := precomp_surjective f hf (sSetTopAdj.unit.app A)
  let r := (sSetTopAdj.homEquiv B (SSet.toTop.obj A)).symm g
  have hh := homotopic_post hg (TopCat.toSSet.map (SSet.toTop.map f))
  have hn : sSetTopAdj.unit.app A ≫ TopCat.toSSet.map (SSet.toTop.map f) =
      f ≫ sSetTopAdj.unit.app B := (sSetTopAdj.unit.naturality f).symm
  rw [hn] at hh
  have hh' := precomp_injective f hf (g ≫ TopCat.toSSet.map (SSet.toTop.map f))
    (sSetTopAdj.unit.app B) (by simpa only [Category.assoc] using hh)
  refine ⟨r,?_,?_⟩
  · have h := adjunct_homotopic hg
    change ContinuousMap.Homotopic
      (SSet.toTop.map f ≫ SSet.toTop.map g ≫ sSetTopAdj.counit.app _).hom
      (TopCat.Hom.hom (𝟙 (SSet.toTop.obj A)))
    simpa only [Adjunction.homEquiv_counit,Functor.map_comp,Category.assoc,
      Adjunction.left_triangle_components] using h
  · have h := adjunct_homotopic hh'
    change ContinuousMap.Homotopic
      ((SSet.toTop.map g ≫ sSetTopAdj.counit.app _) ≫ SSet.toTop.map f).hom
      (TopCat.Hom.hom (𝟙 (SSet.toTop.obj B)))
    simp only [Adjunction.homEquiv_counit,Functor.map_comp,Category.assoc,
      Adjunction.left_triangle_components] at h
    have hn : SSet.toTop.map (TopCat.toSSet.map (SSet.toTop.map f)) ≫
        sSetTopAdj.counit.app (SSet.toTop.obj B) =
        sSetTopAdj.counit.app (SSet.toTop.obj A) ≫ SSet.toTop.map f :=
      sSetTopAdj.counit.naturality (SSet.toTop.map f)
    rwa [hn,← Category.assoc] at h
end Thomason.GeometricRecognition

end

end OAI
