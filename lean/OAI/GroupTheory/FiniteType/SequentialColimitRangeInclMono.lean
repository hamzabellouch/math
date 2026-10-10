import Mathlib
import OAI.GroupTheory.FiniteType.SequentialColimit

namespace OAI

noncomputable section
namespace SequentialColimit
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

lemma range_incl_mono {i j : ℕ} (h : i ≤ j) : range (incl X f i) ⊆ range (incl X f j) := by
  rintro _ ⟨x,rfl⟩
  exact ⟨f i j h x,incl_map X f i j h x⟩

lemma finite_subset_stage {K : Set (Space X f)} (hK : K.Finite) :
    ∃ n, K ⊆ range (incl X f n) := by
  induction K,hK using Set.Finite.induction_on with
  | empty => exact ⟨0,empty_subset _⟩
  | @insert x S hx hS ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,y,rfl⟩ := DirectLimit.exists_eq_mk f x
    refine ⟨max m n,?_⟩
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact range_incl_mono X f (le_max_left _ _) (mem_range_self y)
    · exact range_incl_mono X f (le_max_right _ _) (hn hz)

lemma isClosed_iff_stages (S : Set (Space X f)) :
    IsClosed S ↔ ∀ n, IsClosed (incl X f n ⁻¹' S) := by
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage,isClosed_sigma_iff]
  rfl

variable [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

lemma compact_subset_stage (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)]
    (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    {K : Set (Space X f)} (hK : IsCompact K) :
    ∃ n, K ⊆ range (incl X f n) := by
  classical
  let := hausdorff X f hf
  by_contra hbound
  have hex (n : ℕ) : ∃ z, z ∈ K ∧ z ∉ range (incl X f n) := by
    by_contra h
    apply hbound
    refine ⟨n,?_⟩
    intro z hz
    by_contra hn
    exact h ⟨z,hz,hn⟩
  choose z hzK hzN using hex
  have hc (T : Set (Space X f)) (hT : T ⊆ range z) : IsClosed T := by
    apply (isClosed_iff_stages X f T).mpr
    intro n
    apply Set.Finite.isClosed
    apply (Set.Finite.preimage (incl_injective X f (fun i j h => (hf i j h).injective) n).injOn
      ((finite_Iio n).image z)).subset
    intro x hx
    obtain ⟨m,hm⟩ := hT hx
    refine ⟨m,?_,hm⟩
    change m < n
    by_contra hmn
    exact hzN m (range_incl_mono X f (le_of_not_gt hmn) (hm ▸ mem_range_self x))
  have hd : IsDiscrete (range z) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T,hc T hT,inter_eq_left.mpr hT⟩
  have hkr : IsCompact (range z) := hK.of_isClosed_subset (hc _ Subset.rfl) (by
    rintro _ ⟨n,rfl⟩
    exact hzK n)
  obtain ⟨n,hn⟩ := finite_subset_stage X f (hkr.finite hd)
  exact hzN n (hn (mem_range_self n))

include hf in
lemma compact_map_factors [∀ n, CompactSpace (X n)] {A : Type v}
    [TopologicalSpace A] [CompactSpace A] (g : C(A,Space X f)) :
    ∃ (n : ℕ) (h : C(A,X n)), ∀ a, incl X f n (h a) = g a := by
  obtain ⟨n,hn⟩ := compact_subset_stage X f hf (isCompact_range g.continuous)
  let e := (incl_isClosedEmbedding X f hf n).isEmbedding.toHomeomorph
  let h : C(A,X n) := ⟨fun a => e.symm ⟨g a,hn (mem_range_self a)⟩,
    e.symm.continuous.comp (g.continuous.subtype_mk _)⟩
  exact ⟨n,h,fun a => congrArg Subtype.val (e.apply_symm_apply ⟨g a,hn (mem_range_self a)⟩)⟩

end SequentialColimit

namespace SequentialCoreTower
open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)
  [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in

lemma compact_map_factors_above {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (g : C(A,(core X f I δ Z pot hBase hPot hCoord).TotalSpace)) (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ ∃ h : C(A,(Z n).TotalSpace),
      ∀ a, coverIncl X f I δ Z pot hBase hPot hCoord n (h a) = g a := by
  let p := core X f I δ Z pot hBase hPot hCoord
  obtain ⟨m,hm⟩ := SequentialColimit.compact_subset_stage X f hf
    (isCompact_range (p.continuous_proj.comp g.continuous))
  let n := max m N
  have hn (a : A) : g a ∈ range (coverIncl X f I δ Z pot hBase hPot hCoord n) := by
    rw [coverIncl_range]
    exact SequentialColimit.range_incl_mono X f (le_max_left _ _) (hm (mem_range_self a))
  let e := (coverIncl_isClosedEmbedding X f I δ Z pot hBase hPot hCoord hf n).isEmbedding.toHomeomorph
  let h : C(A,(Z n).TotalSpace) := ⟨fun a => e.symm ⟨g a,hn a⟩,
    e.symm.continuous.comp (g.continuous.subtype_mk hn)⟩
  exact ⟨n,le_max_right _ _,h,fun a => congrArg Subtype.val (e.apply_symm_apply ⟨g a,hn a⟩)⟩

end SequentialCoreTower

namespace SequentialCW
open Set Topology Metric
universe u
variable (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
  [∀ i, CWComplex (univ : Set (X i))]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
abbrev Cell (i n : ℕ) := RelCWComplex.cell (univ : Set (X i)) n
variable (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
  [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
  (hδ : ∀ i j h n (c : Cell X i n) v, v ∈ closedBall (0 : Fin n → ℝ) 1 →
    f i j h (RelCWComplex.map n c v) = RelCWComplex.map n (δ i j h n c) v)

abbrev Space := SequentialColimit.Space X f
abbrev FinalCell (n : ℕ) := DirectLimit (fun i => Cell X i n) (fun i j h => δ i j h n)
def cellMk (i n : ℕ) (c : Cell X i n) : FinalCell X δ n := ⟦⟨i,c⟩⟧
def repr (n : ℕ) (c : FinalCell X δ n) : Σ i, Cell X i n :=
  ⟨(DirectLimit.exists_eq_mk _ c).choose,(DirectLimit.exists_eq_mk _ c).choose_spec.choose⟩
lemma repr_eq (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, CWComplex (univ : Set (X i))]
    (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
    [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
    (n : ℕ) (c : FinalCell X δ n) :
    cellMk X δ (repr X δ n c).1 n (repr X δ n c).2 = c :=
  (DirectLimit.exists_eq_mk _ c).choose_spec.choose_spec.symm

def stageChart (i n : ℕ) (c : Cell X i n) : PartialEquiv (Fin n → ℝ) (Space X f) :=
  (RelCWComplex.map n c).trans
    ((SequentialColimit.incl_isClosedEmbedding X f hf i).isEmbedding.toPartialHomeomorph
      (SequentialColimit.incl X f i)).toPartialEquiv

@[simp] lemma stageChart_apply (i n : ℕ) (c : Cell X i n) (v : Fin n → ℝ) :
    stageChart X f hf i n c v = SequentialColimit.incl X f i (RelCWComplex.map n c v) := rfl
@[simp] lemma stageChart_source (i n : ℕ) (c : Cell X i n) :
    (stageChart X f hf i n c).source = ball 0 1 := by
  simp [stageChart,PartialEquiv.trans_source,RelCWComplex.source_eq]
lemma stageChart_continuousOn (i n : ℕ) (c : Cell X i n) :
    ContinuousOn (stageChart X f hf i n c) (closedBall 0 1) :=
  (SequentialColimit.incl X f i).continuous.comp_continuousOn (RelCWComplex.continuousOn n c)
lemma stageChart_continuousOn_symm (i n : ℕ) (c : Cell X i n) :
    ContinuousOn (stageChart X f hf i n c).symm (stageChart X f hf i n c).target := by
  let e := (SequentialColimit.incl_isClosedEmbedding X f hf i).isEmbedding.toPartialHomeomorph
    (SequentialColimit.incl X f i)
  exact (RelCWComplex.continuousOn_symm n c).comp
    (e.continuousOn_symm.mono inter_subset_left) (fun _ h => h.2)

include hδ in
lemma stageChart_eq {i j n : ℕ} (c : Cell X i n) (d : Cell X j n)
    (he : cellMk X δ i n c = cellMk X δ j n d) (v : Fin n → ℝ)
    (hv : v ∈ closedBall 0 1) : stageChart X f hf i n c v = stageChart X f hf j n d v := by
  obtain ⟨k,hik,hjk,hcd⟩ := Quotient.eq.mp he
  simp only [stageChart_apply]
  rw [← SequentialColimit.incl_map X f i k hik,← SequentialColimit.incl_map X f j k hjk,
    hδ i k hik n c v hv,hδ j k hjk n d v hv,hcd]

def chart (n : ℕ) (c : FinalCell X δ n) : PartialEquiv (Fin n → ℝ) (Space X f) :=
  stageChart X f hf (repr X δ n c).1 n (repr X δ n c).2

include hδ in
lemma chart_mk (i n : ℕ) (c : Cell X i n) (v : Fin n → ℝ) (hv : v ∈ closedBall 0 1) :
    chart X f hf δ n (cellMk X δ i n c) v = SequentialColimit.incl X f i (RelCWComplex.map n c v) :=
  stageChart_eq X f hf δ hδ _ c (repr_eq X δ n _) v hv

lemma chart_source (n : ℕ) (c : FinalCell X δ n) : (chart X f hf δ n c).source = ball 0 1 :=
  stageChart_source X f hf _ _ _
lemma chart_continuousOn (n : ℕ) (c : FinalCell X δ n) :
    ContinuousOn (chart X f hf δ n c) (closedBall 0 1) := stageChart_continuousOn X f hf _ _ _
lemma chart_continuousOn_symm (n : ℕ) (c : FinalCell X δ n) :
    ContinuousOn (chart X f hf δ n c).symm (chart X f hf δ n c).target :=
  stageChart_continuousOn_symm X f hf _ _ _

include hδ in
lemma chart_union : (⋃ (n : ℕ) (c : FinalCell X δ n), chart X f hf δ n c '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell X i n), RelCWComplex.map n c '' closedBall 0 1 := by
    change x ∈ ⋃ (n : ℕ) (c : Cell X i n), RelCWComplex.closedCell n c
    rw [CWComplex.union]; trivial
  simp only [mem_iUnion,mem_image] at hx
  obtain ⟨n,c,v,hv,rfl⟩ := hx
  exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨cellMk X δ i n c,⟨v,hv,chart_mk X f hf δ hδ i n c v hv⟩⟩⟩

@[simp] lemma cellMk_map (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, CWComplex (univ : Set (X i))]
    (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
    [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
    (i j : ℕ) (h : i ≤ j) (n : ℕ) (c : Cell X i n) :
    cellMk X δ j n (δ i j h n c) = cellMk X δ i n c := by
  unfold cellMk
  exact DirectLimit.mk_apply (f:=fun i j h => δ i j h n) i j c h

include hδ in
lemma chart_cell_eq {n m : ℕ} (c : FinalCell X δ n) (d : FinalCell X δ m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : chart X f hf δ n c v = chart X f hf δ m d w) :
    (⟨n,c⟩ : Σ n, FinalCell X δ n) = ⟨m,d⟩ := by
  classical
  induction c using Quotient.inductionOn with
  | h c =>
    rcases c with ⟨i,c⟩
    induction d using Quotient.inductionOn with
    | h d =>
      rcases d with ⟨j,d⟩
      change chart X f hf δ n (cellMk X δ i n c) v = chart X f hf δ m (cellMk X δ j m d) w at he
      rw [chart_mk X f hf δ hδ _ _ _ _ (ball_subset_closedBall hv),
        chart_mk X f hf δ hδ _ _ _ _ (ball_subset_closedBall hw),
        ← SequentialColimit.incl_map X f i (max i j) (le_max_left _ _),
        ← SequentialColimit.incl_map X f j (max i j) (le_max_right _ _),
        hδ i (max i j) (le_max_left _ _) n c v (ball_subset_closedBall hv),
        hδ j (max i j) (le_max_right _ _) m d w (ball_subset_closedBall hw)] at he
      have he' := (SequentialColimit.incl_isClosedEmbedding X f hf (max i j)).injective he
      have hn : (⟨n,δ i (max i j) (le_max_left _ _) n c⟩ : Σ n, Cell X (max i j) n) =
          ⟨m,δ j (max i j) (le_max_right _ _) m d⟩ := by
        by_contra hn
        exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hn)
          ⟨v,hv,rfl⟩ ⟨w,hw,he'.symm⟩
      have hz := congrArg (fun a : Σ n, Cell X (max i j) n =>
        (⟨a.1,cellMk X δ (max i j) a.1 a.2⟩ : Σ n, FinalCell X δ n)) hn
      change (⟨n,cellMk X δ i n c⟩ : Σ n, FinalCell X δ n) = ⟨m,cellMk X δ j m d⟩
      simpa only [cellMk_map] using hz

include hδ in
lemma chart_pairwiseDisjoint :
    (univ : Set (Σ n, FinalCell X δ n)).PairwiseDisjoint
      (fun c => chart X f hf δ c.1 c.2 '' ball 0 1) := by
  intro c _ d _ hcd
  apply Set.disjoint_left.mpr
  rintro z ⟨v,hv,rfl⟩ ⟨w,hw,he⟩
  exact hcd (chart_cell_eq X f hf δ hδ c.2 d.2 hv hw he.symm)

include hδ in
lemma chart_mapsTo (n : ℕ) (c : FinalCell X δ n) :
    ∃ I : ∀ m, Finset (FinalCell X δ m),
      MapsTo (chart X f hf δ n c) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), chart X f hf δ m j '' closedBall 0 1) := by
  classical
  induction c using Quotient.inductionOn with
  | h c =>
    rcases c with ⟨i,c⟩
    obtain ⟨I,hI⟩ := CWComplex.mapsTo n c
    refine ⟨fun m => (I m).image (cellMk X δ i m),?_⟩
    intro v hv
    obtain ⟨m,hm,j,hj,w,hw,he⟩ := by
      simpa only [mem_iUnion,mem_image] using hI hv
    simp only [mem_iUnion,mem_image]
    refine ⟨m,hm,cellMk X δ i m j,Finset.mem_image_of_mem _ hj,w,hw,?_⟩
    change chart X f hf δ m (cellMk X δ i m j) w = chart X f hf δ n (cellMk X δ i n c) v
    rw [chart_mk X f hf δ hδ i m j w hw,
      chart_mk X f hf δ hδ i n c v (sphere_subset_closedBall hv)]
    exact congrArg (SequentialColimit.incl X f i) he

include hδ in
lemma chart_image (i n : ℕ) (c : Cell X i n) :
    chart X f hf δ n (cellMk X δ i n c) '' closedBall 0 1 =
      SequentialColimit.incl X f i '' RelCWComplex.closedCell n c := by
  rw [RelCWComplex.closedCell,← image_comp]
  exact image_congr (fun v hv => chart_mk X f hf δ hδ i n c v hv)

include hδ in
lemma chart_closed (A : Set (Space X f))
    (hA : ∀ n (c : FinalCell X δ n), IsClosed (A ∩ chart X f hf δ n c '' closedBall 0 1)) :
    IsClosed A := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  apply isClosed_sigma_iff.mpr
  intro i
  change IsClosed (SequentialColimit.incl X f i ⁻¹' A)
  apply (CWComplex.closed (univ : Set (X i)) _ (subset_univ _)).mpr
  intro n c
  have hc := (hA n (cellMk X δ i n c)).preimage (SequentialColimit.incl X f i).continuous
  rw [chart_image X f hf δ hδ i n c,preimage_inter,
    (SequentialColimit.incl_isClosedEmbedding X f hf i).injective.preimage_image] at hc
  exact hc

@[instance_reducible] def cwComplex : CWComplex (univ : Set (Space X f)) where
  cell := FinalCell X δ
  map := chart X f hf δ
  source_eq := chart_source X f hf δ
  continuousOn := chart_continuousOn X f hf δ
  continuousOn_symm := chart_continuousOn_symm X f hf δ
  pairwiseDisjoint' := chart_pairwiseDisjoint X f hf δ hδ
  mapsTo' := chart_mapsTo X f hf δ hδ
  closed' A _ := chart_closed X f hf δ hδ A
  union' := chart_union X f hf δ hδ

lemma cellMk_surjective (n N : ℕ)
    (hst : ∀ i (h : N ≤ i), Function.Surjective (δ N i h n)) :
    Function.Surjective (cellMk X δ N n) := by
  intro c
  obtain ⟨i,c,rfl⟩ := DirectLimit.exists_eq_mk (fun i j h => δ i j h n) c
  by_cases hi : i ≤ N
  · exact ⟨δ i N hi n c,cellMk_map X δ i N hi n c⟩
  · obtain ⟨c,rfl⟩ := hst i (by omega) c
    exact ⟨c,(cellMk_map X δ N i (by omega) n c).symm⟩

lemma finiteType [∀ i, RelCWComplex.FiniteType (univ : Set (X i))]
    (hst : ∀ n, ∃ N, ∀ i (h : N ≤ i), Function.Surjective (δ N i h n)) :
    letI := cwComplex X f hf δ hδ
    RelCWComplex.FiniteType (univ : Set (Space X f)) := by
  let := cwComplex X f hf δ hδ
  constructor
  intro n
  obtain ⟨N,hN⟩ := hst n
  let : Finite (Cell X N n) := RelCWComplex.FiniteType.finite_cell n
  exact Finite.of_surjective (cellMk X δ N n) (cellMk_surjective X δ n N hN)

end SequentialCW

end

end OAI
