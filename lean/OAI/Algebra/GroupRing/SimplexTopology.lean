import Mathlib

namespace OAI

noncomputable section

namespace GroupRingTopology

def simplexSet (Scalar : Type*) (Vertex : Type*) [Semiring Scalar] [PartialOrder Scalar]
    [Fintype Vertex] : Set (Vertex → Scalar) :=
  {coordinates | (∀ vertex, 0 ≤ coordinates vertex) ∧ ∑ vertex, coordinates vertex = 1}

instance (Vertex : Type*) [Fintype Vertex] : CompactSpace (simplexSet ℝ Vertex) := by
  apply isCompact_iff_compactSpace.mp
  have range_eq : Set.range (fun point : Convexity.StdSimplex ℝ Vertex =>
      (point.weights : Vertex → ℝ)) = simplexSet ℝ Vertex := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext coordinates
    simp [simplexSet]
  rw [← range_eq]
  exact isCompact_range (continuous_pi fun vertex =>
    Convexity.StdSimplex.continuous_weights_apply ℝ vertex)

end GroupRingTopology

open Set Metric Topology BigOperators
namespace GroupRingTopology.SimplexDisk

def Truncated (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
def Positive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i
@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma truncated_closed (n : ℕ) : IsClosed (Truncated n) := by
  have h : Truncated n = (⋂ i, {x | (0:ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Truncated]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma positive_open (n : ℕ) : IsOpen (Positive n) := by
  have h : Positive n = (⋂ i, {x | (0:ℝ) < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [Positive]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma interior_truncated (n : ℕ) : interior (Truncated n) = Positive n := by
  apply Subset.antisymm
  · intro x hx
    have hc : ∀ i, 0 < x i := by
      intro i
      have hh := interior_mono (show Truncated n ⊆ (Function.eval i) ⁻¹' Ici (0:ℝ) from fun _ h => h.1 i) hx
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),interior_Ici] at hh
      exact hh
    refine ⟨hc,?_⟩
    cases n with
    | zero => simp
    | succ n =>
      have hs : Function.Surjective (sumCLM (n+1)) := by
        intro r
        refine ⟨Pi.single 0 r,?_⟩
        simp
      have hh := interior_mono (show Truncated (n+1) ⊆ (sumCLM (n+1)) ⁻¹' Iic (1:ℝ) from fun _ h => by simpa using h.2) hx
      rw [← ((sumCLM (n+1)).isOpenMap hs).preimage_interior_eq_interior_preimage (sumCLM (n+1)).continuous,interior_Iic] at hh
      simpa only [mem_preimage,mem_Iio,sumCLM_apply] using hh
  · apply (positive_open n).subset_interior_iff.mpr
    exact fun _ h => ⟨fun i => (h.1 i).le,h.2.le⟩

lemma truncated_convex (n : ℕ) : Convex ℝ (Truncated n) := by
  have h : Truncated n = (⋂ i, ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Ici 0)) ∩
      (sumCLM n) ⁻¹' Iic 1 := by ext x; simp [Truncated]
  rw [h]
  exact (convex_iInter fun i => (convex_Ici (0:ℝ)).linear_preimage (LinearMap.proj i)).inter
    ((convex_Iic (1:ℝ)).linear_preimage (sumCLM n).toLinearMap)

lemma truncated_bounded (n : ℕ) : Bornology.IsBounded (Truncated n) := by
  apply (isBounded_Icc (a := (0 : Fin n → ℝ)) (b := 1)).subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma positive_nonempty (n : ℕ) : (Positive n).Nonempty := by
  refine ⟨fun _ => 1 / (n+1 : ℝ),fun _ => by positivity,?_⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (0:ℝ) < n+1 := by positivity
  rw [mul_one_div,div_lt_one hn]
  linarith

noncomputable def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))

lemma ambient_positive (n : ℕ) : ambient n '' Positive n = ball 0 1 := by
  simpa only [ambient,interior_truncated] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).1
lemma ambient_truncated (n : ℕ) : ambient n '' Truncated n = closedBall 0 1 := by
  simpa only [ambient,(truncated_closed n).closure_eq] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).2.1

noncomputable def truncatedDisk (n : ℕ) : Truncated n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  ((ambient n).image (Truncated n)).trans (Homeomorph.setCongr (ambient_truncated n))

noncomputable def simplexTruncated (n : ℕ) : simplexSet ℝ (Fin (n+1)) ≃ₜ Truncated n where
  toFun x := ⟨fun i => x.1 i.succ,fun i => x.2.1 _,by
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    linarith [x.2.1 0]⟩
  invFun x := ⟨Fin.cons (1 - ∑ i, x.1 i) x.1,by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.2.2
      · exact x.2.1 j
    · simp [Fin.sum_univ_succ]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    change 1 - ∑ i : Fin n, x.1 i.succ = x.1 0
    linarith
  right_inv x := by rfl
  continuous_toFun := (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val)
    · exact (continuous_apply j).comp continuous_subtype_val

noncomputable def simplexDisk (n : ℕ) : simplexSet ℝ (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (simplexTruncated n).trans (truncatedDisk n)

lemma simplexTruncated_positive (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexTruncated n x).1 ∈ Positive n ↔ ∀ i, 0 < x.1 i := by
  have h := x.2.2
  rw [Fin.sum_univ_succ] at h
  constructor
  · rintro ⟨hc,hs⟩ i
    refine Fin.cases ?_ (fun j => hc j) i
    change ∑ i : Fin n, x.1 i.succ < 1 at hs
    linarith
  · intro hc
    refine ⟨fun j => hc _,?_⟩
    change ∑ i : Fin n, x.1 i.succ < 1
    linarith [hc 0]

lemma simplexDisk_open (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexDisk n x).1 ∈ ball 0 1 ↔ ∀ i, 0 < x.1 i := by
  rw [← simplexTruncated_positive]
  change ambient n (simplexTruncated n x).1 ∈ ball 0 1 ↔ _
  rw [← ambient_positive]
  exact (ambient n).injective.mem_set_image

lemma simplexDisk_boundary (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexDisk n x).1 ∈ sphere 0 1 ↔ ∃ i, x.1 i = 0 := by
  have h := (simplexDisk n x).2
  rw [mem_sphere,mem_closedBall] at *
  have ho := simplexDisk_open n x
  simp only [mem_ball] at ho
  constructor
  · intro he
    have hn : ¬ ∀ i, 0 < x.1 i := by rw [←ho,he]; exact lt_irrefl _
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,le_antisymm hi (x.2.1 i)⟩
  · rintro ⟨i,hi⟩
    apply le_antisymm h
    by_contra hn
    have hp := ho.mp (lt_of_not_ge hn)
    linarith [hp i]

noncomputable def reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    simplexSet ℝ A ≃ₜ simplexSet ℝ B where
  toFun x := ⟨fun b => x.1 (e.symm b),fun b => x.2.1 _,(e.symm.sum_comp x.1).trans x.2.2⟩
  invFun x := ⟨fun a => x.1 (e a),fun a => x.2.1 _,(e.sum_comp x.1).trans x.2.2⟩
  left_inv x := by ext a; simp
  right_inv x := by ext b; simp
  continuous_toFun := (continuous_pi fun b => ((continuous_apply (e.symm b)).comp continuous_subtype_val : Continuous (fun x : simplexSet ℝ A => x.1 (e.symm b)))).subtype_mk _
  continuous_invFun := (continuous_pi fun a => ((continuous_apply (e a)).comp continuous_subtype_val : Continuous (fun x : simplexSet ℝ B => x.1 (e a)))).subtype_mk _

lemma reindex_positive {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (x : simplexSet ℝ A) :
    (∀ b, 0 < (reindex e x).1 b) ↔ ∀ a, 0 < x.1 a := by
  constructor
  · intro h a
    change ∀ b, 0 < x.1 (e.symm b) at h
    simpa only [e.symm_apply_apply] using h (e a)
  · intro h b
    change 0 < x.1 (e.symm b)
    exact h _

end GroupRingTopology.SimplexDisk
open Set Metric Topology BigOperators
namespace GroupRingTopology.Simplicial

section
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

/-- Finitely supported probability weights on a face, with the weak topology. -/
def Space := {w : V →₀ ℝ | (∀ v, 0 ≤ w v) ∧ w.sum (fun _ r => r) = 1 ∧ w.support ∈ K}
abbrev Face := {s : Finset V // s ∈ K}

lemma support_nonempty {w : V →₀ ℝ} (h : w.sum (fun _ r => r) = 1) : w.support.Nonempty := by
  classical
  by_contra hn
  have hz : w = 0 := by
    apply Finsupp.support_eq_empty.mp
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  simp [hz] at h

lemma face_nonempty (s : Face K) : s.1.Nonempty := (K.isRelLowerSet_faces s.2).1

noncomputable def weight (s : Finset V) (x : simplexSet ℝ s) : V →₀ ℝ :=
  Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) (Finsupp.equivFunOnFinite.symm x.1)

lemma weight_apply (s : Finset V) (x : simplexSet ℝ s) (v : s) :
    weight s x v = x.1 v := by
  exact Finsupp.embDomain_apply_self _ _ _

lemma weight_apply_not (s : Finset V) (x : simplexSet ℝ s) {v : V} (hv : v ∉ s) :
    weight s x v = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨w,hw⟩
  exact hv (hw ▸ w.2)

lemma weight_nonneg (s : Finset V) (x : simplexSet ℝ s) (v : V) : 0 ≤ weight s x v := by
  classical
  by_cases hv : v ∈ s
  · exact (weight_apply s x ⟨v,hv⟩) ▸ x.2.1 ⟨v,hv⟩
  · rw [weight_apply_not _ _ hv]

lemma weight_sum (s : Finset V) (x : simplexSet ℝ s) : (weight s x).sum (fun _ r => r) = 1 := by
  rw [weight,Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact x.2.2

lemma weight_support_subset (s : Finset V) (x : simplexSet ℝ s) : (weight s x).support ⊆ s := by
  classical
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (weight_apply_not _ _ hn)

noncomputable def faceMap (s : Face K) (x : simplexSet ℝ s.1) : Space K :=
  ⟨weight s.1 x,weight_nonneg _ _,weight_sum _ _,
    K.isRelLowerSet_faces.mem_of_le s.2 (weight_support_subset _ _) (support_nonempty (weight_sum _ _))⟩

noncomputable def quotient (x : Σ s : Face K, simplexSet ℝ s.1) : Space K := faceMap K x.1 x.2

instance : TopologicalSpace (Space K) := TopologicalSpace.coinduced (quotient K) inferInstance

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (f : Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (f ∘ faceMap K s) := by
  rw [continuous_coinduced_dom]
  exact continuous_sigma_iff

lemma continuous_faceMap (s : Face K) : Continuous (faceMap K s) :=
  (continuous_coinduced_rng : Continuous (quotient K)).comp (continuous_sigmaMk (i := s))

lemma continuous_eval (v : V) : Continuous (fun x : Space K => x.1 v) := by
  classical
  rw [continuous_iff]
  intro s
  by_cases hv : v ∈ s.1
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun x : simplexSet ℝ s.1 => x.1 ⟨v,hv⟩) := by
      funext x
      exact weight_apply s.1 x ⟨v,hv⟩
    rw [he]
    exact (continuous_apply (⟨v,hv⟩ : s.1)).comp continuous_subtype_val
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun _ => (0:ℝ)) := by
      funext x
      exact weight_apply_not _ _ hv
    rw [he]
    exact continuous_const

instance : T2Space (Space K) :=
  T2Space.of_injective_continuous (f := fun x : Space K => (x.1 : V → ℝ))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun v => congrFun h v))
    (continuous_pi fun v => continuous_eval K v)

lemma faceMap_injective (s : Face K) : Function.Injective (faceMap K s) := by
  intro x y h
  apply Subtype.ext
  funext v
  have hh := congrArg (fun p : Space K => p.1 v) h
  exact (weight_apply _ _ _).symm.trans (hh.trans (weight_apply _ _ _))

lemma faceMap_closedEmbedding (s : Face K) : IsClosedEmbedding (faceMap K s) :=
  (continuous_faceMap K s).isClosedEmbedding (faceMap_injective K s)

noncomputable def coordinates (s : Finset V) (x : Space K) (h : x.1.support ⊆ s) : simplexSet ℝ s := by
  refine ⟨fun v => x.1 v,fun v => x.2.1 _,?_⟩
  rw [Finset.sum_coe_sort]
  exact (x.1.sum_of_support_subset h _ (fun _ _ => rfl)).symm.trans x.2.2.1

lemma faceMap_coordinates (s : Face K) (x : Space K) (h : x.1.support ⊆ s.1) :
    faceMap K s (coordinates K s.1 x h) = x := by
  classical
  apply Subtype.ext
  ext v
  by_cases hv : v ∈ s.1
  · exact weight_apply _ _ ⟨v,hv⟩
  · change weight s.1 _ v = x.1 v
    rw [weight_apply_not _ _ hv,Finsupp.notMem_support_iff.mp (fun hh => hv (h hh))]

lemma range_faceMap (s : Face K) : Set.range (faceMap K s) = {x | x.1.support ⊆ s.1} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact weight_support_subset _ _
  · intro h
    exact ⟨coordinates K s.1 x h,faceMap_coordinates K s x h⟩

lemma quotient_surjective : Function.Surjective (quotient K) := by
  intro x
  exact ⟨⟨⟨x.1.support,x.2.2.2⟩,coordinates K x.1.support x (subset_refl _)⟩,
    faceMap_coordinates K ⟨x.1.support,x.2.2.2⟩ x (subset_refl _)⟩

lemma isClosed_iff (A : Set (Space K)) :
    IsClosed A ↔ ∀ s : Face K, IsClosed ((faceMap K s) ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

lemma support_eq_iff (s : Face K) (x : simplexSet ℝ s.1) :
    (faceMap K s x).1.support = s.1 ↔ ∀ v, 0 < x.1 v := by
  classical
  constructor
  · intro he v
    have hn : weight s.1 x v ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      change v.1 ∈ (faceMap K s x).1.support
      rw [he]
      exact v.2
    rw [weight_apply] at hn
    exact lt_of_le_of_ne (x.2.1 v) (Ne.symm hn)
  · intro hp
    apply Finset.Subset.antisymm (weight_support_subset _ _)
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    rw [weight_apply _ _ ⟨v,hv⟩]
    exact ne_of_gt (hp ⟨v,hv⟩)

end

open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

lemma continuous_of_support_subset [TopologicalSpace T] (f : T → Space K) (s : Face K)
    (hs : ∀ x, (f x).1.support ⊆ s.1) (hc : ∀ v, Continuous fun x => (f x).1 v) : Continuous f := by
  let c : T → simplexSet ℝ s.1 := fun x => coordinates K s.1 (f x) (hs x)
  have hcc : Continuous c := (continuous_pi fun v : s.1 => hc v.1).subtype_mk _
  have he : f = (faceMap K s) ∘ c := by
    funext x
    exact (faceMap_coordinates K s (f x) (hs x)).symm
  rw [he]
  exact (continuous_faceMap K s).comp hcc

lemma push_apply (f : V → W) (w : V →₀ ℝ) (s : Finset V) (hs : w.support ⊆ s) (b : W) :
    (w.mapDomain f) b = ∑ a ∈ s, if f a = b then w a else 0 := by
  classical
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [w.sum_of_support_subset hs]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finsupp.single_apply]
  · intro a _
    simp

lemma push_nonneg (f : V → W) (w : V →₀ ℝ) (hw : ∀ v, 0 ≤ w v) (b : W) :
    0 ≤ (w.mapDomain f) b := by
  classical
  rw [push_apply f w w.support (Finset.Subset.refl _) b]
  exact Finset.sum_nonneg fun a _ => by split; exact hw a; exact le_rfl

lemma push_sum (f : V → W) (w : V →₀ ℝ) :
    (w.mapDomain f).sum (fun _ r => r) = w.sum (fun _ r => r) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

def map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) : Space L := by
  classical
  refine ⟨x.1.mapDomain f,push_nonneg f x.1 x.2.1,?_,?_⟩
  · rw [push_sum]; exact x.2.2.1
  · exact L.isRelLowerSet_faces.mem_of_le (hf ⟨x.1.support,x.2.2.2⟩) Finsupp.mapDomain_support
      (support_nonempty (by rw [push_sum]; exact x.2.2.1))

lemma map_support (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) :
    (map K L f hf x).1.support ⊆ x.1.support.image f := by
  classical
  exact Finsupp.mapDomain_support

lemma continuous_map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : Continuous (map K L f hf) := by
  classical
  rw [continuous_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f,hf s⟩
  · intro x
    exact (map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _))
  · intro b
    have he : (fun x : simplexSet ℝ s.1 => ((map K L f hf ∘ faceMap K s) x).1 b) =
        fun x => ∑ a : s.1, if f a.1 = b then x.1 a else 0 := by
      funext x
      change (Finsupp.mapDomain f (weight s.1 x)) b = _
      rw [push_apply f _ s.1 (weight_support_subset _ _) b,← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    split_ifs
    · exact (continuous_apply a).comp continuous_subtype_val
    · exact continuous_const

def mapC (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : C(Space K,Space L) :=
  ⟨map K L f hf,continuous_map K L f hf⟩

lemma map_id (hf : ∀ s : Face K, s.1.image id ∈ K) (x : Space K) : map K K id hf x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_comp {U : Type*} (M : PreAbstractSimplicialComplex U)
    (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L)
    (g : W → U) (hg : ∀ s : Face L, s.1.image g ∈ M)
    (hgf : ∀ s : Face K, s.1.image (g ∘ f) ∈ M) (x : Space K) :
    map L M g hg (map K L f hf x) = map K M (g ∘ f) hgf x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

lemma quotient_quotientMap : IsQuotientMap (quotient K) :=
  ⟨⟨rfl⟩,quotient_surjective K⟩

lemma continuous_prod_iff [TopologicalSpace T] [LocallyCompactSpace T]
    {Y : Type*} [TopologicalSpace Y] (f : T × Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (fun p : T × simplexSet ℝ s.1 => f (p.1,faceMap K s p.2)) := by
  constructor
  · intro hf s
    exact hf.comp (continuous_fst.prodMk ((continuous_faceMap K s).comp continuous_snd))
  · intro hf
    apply (quotient_quotientMap K).continuous_lift_prod_right
    rw [continuous_def]
    intro O hO
    have hp : (fun p : T × (Σ s : Face K, simplexSet ℝ s.1) => f (p.1,quotient K p.2)) ⁻¹' O =
      ⋃ s : Face K, (fun p : T × simplexSet ℝ s.1 => (p.1,⟨s,p.2⟩)) ''
        ((fun p : T × simplexSet ℝ s.1 => f (p.1,faceMap K s p.2)) ⁻¹' O) := by
      ext p
      simp only [mem_preimage,mem_iUnion,mem_image]
      constructor
      · intro h
        exact ⟨p.2.1,⟨p.1,p.2.2⟩,h,rfl⟩
      · rintro ⟨s,p,h,rfl⟩
        exact h
    rw [hp]
    apply isOpen_iUnion
    intro s
    exact (IsOpenMap.id.prodMap isOpenMap_sigmaMk) _ ((hf s).isOpen_preimage O hO)

end GroupRingTopology.Simplicial

end

end OAI
