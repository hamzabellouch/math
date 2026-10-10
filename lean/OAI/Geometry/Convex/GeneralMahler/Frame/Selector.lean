import Mathlib

namespace OAI
/-! Borel selection for a closed relation into a compact metric space. -/
noncomputable section
open Set Filter Metric Real MeasureTheory
open scoped Topology NNReal ENNReal
namespace GeneralMahler.Select
section
variable {X Y:Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Nonempty Y]
variable (F:Set (X×Y))
def near (x:X) (y:Y) (r:ℝ) := ∃ v,(x,v)∈F∧dist v y≤r
omit [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y] in
lemma near_m (h:IsClosed F) (y:Y) (r:ℝ) : MeasurableSet {x|near F x y r} := by
  let S := F ∩ Prod.snd ⁻¹' (closedBall y r)
  have hs := isClosedMap_fst_of_compactSpace S (h.inter (isClosed_closedBall.preimage continuous_snd))
  have he : {x|near F x y r}= Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨v,hv,h⟩; exact ⟨(x,v),⟨hv,h⟩,rfl⟩
    rintro ⟨⟨x,v⟩,h,rfl⟩; exact ⟨v,h.1,h.2⟩
  rw [he]; exact hs.measurableSet
def eps (n:ℕ):ℝ := (1/2)^n
omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma dense_approx (y:Y) {r:ℝ} (hr:0<r) :
    ∃ n:ℕ,dist y (TopologicalSpace.denseSeq Y n)<r :=
  (TopologicalSpace.denseRange_denseSeq Y).exists_dist_lt y hr
omit [TopologicalSpace X] [OpensMeasurableSpace X] [BorelSpace Y] in
lemma choose_m {p:X→Y→Prop} (h:∀ x,∃ n:ℕ,p x (TopologicalSpace.denseSeq Y n))
    (hm:∀ n:ℕ,MeasurableSet {x|p x (TopologicalSpace.denseSeq Y n)}) :
    ∃ f:X→Y,Measurable f∧∀ x,p x (f x) := by
  classical
  let f := fun x:X=> Nat.find (h x)
  exact ⟨TopologicalSpace.denseSeq Y ∘ f,(measurable_of_countable _).comp
    (measurable_find h hm),fun x=> Nat.find_spec (h x)⟩

abbrev tag (n:ℕ) := {f:X→Y // Measurable f∧∀ x, near F x (f x) (eps n)}
omit [BorelSpace Y] in
lemma start (he:∀ x:X,∃ y:Y,(x,y)∈F) (hc:IsClosed F) :
    Nonempty (tag F 0) := by
  have h (x:X) : ∃ n:ℕ,near F x (TopologicalSpace.denseSeq Y n) (eps 0) := by
    obtain ⟨y,hy⟩ := he x
    obtain ⟨n,hn⟩ := dense_approx y (r:=eps 0) (by norm_num [eps])
    exact ⟨n,y,hy,hn.le⟩
  obtain ⟨f,hf,hf'⟩ := choose_m (p:=fun x y=> near F x y (eps 0)) h (fun _=> near_m _ hc _ _)
  exact ⟨⟨f,hf,hf'⟩⟩
lemma next (hc:IsClosed F) (n:ℕ) (x:tag F n) :
    ∃ y: tag F (n+1),∀ a,dist (x.val a) (y.val a)≤2*eps n := by
  let p := fun (a:X) (y:Y)=> near F a y (eps (n+1)) ∧ dist (x.val a) y≤2*eps n
  have h (a:X) : ∃ n,p a (TopologicalSpace.denseSeq Y n) := by
    obtain ⟨v,hv,hh⟩ := x.property.2 a
    obtain ⟨w,hw⟩ := dense_approx v (r:=eps (n+1)) (by unfold eps; positivity)
    refine ⟨w,⟨v,hv,hw.le⟩,?_⟩
    apply le_trans (dist_triangle _ v _)
    have hp : 0≤eps n := by unfold eps; positivity
    have he : eps (n+1)=eps n/2 := by unfold eps; rw [pow_succ]; ring
    rw [dist_comm (x.val a)]; linarith
  have hm (i) : MeasurableSet {a|p a (TopologicalSpace.denseSeq Y i)} :=
    (near_m _ hc _ _).inter (measurableSet_le (x.property.1.dist measurable_const) measurable_const)
  obtain ⟨f,hf,h₁⟩ := choose_m h hm
  exact ⟨⟨f,hf,fun x=>(h₁ x).1⟩,fun x=>(h₁ x).2⟩

theorem selector (he:∀ x:X,∃ y:Y,(x,y)∈F) (hc:IsClosed F) :
    ∃ f:X→Y, Measurable f ∧ ∀ x,(x,f x)∈F := by
  classical
  let s (n:ℕ) := Nat.rec (motive:=fun n=> tag F n) (Classical.choice (start F he hc))
    (fun n x=> (next F hc n x).choose) n
  have hn (n a) : dist ((s n).val a) ((s (n+1)).val a) ≤ 2*eps n := (next F hc n (s n)).choose_spec a
  let g := fun n=>(s n).val
  have hh (x:X) : CauchySeq fun n=>g n x :=
    cauchySeq_of_le_geometric _ _ (show (1/2:ℝ)<1 by norm_num) (fun n=>hn n x)
  choose f hf using fun x:X=> cauchySeq_tendsto_of_complete (hh x)
  refine ⟨f,measurable_of_tendsto_metrizable (fun n=>(s n).property.1) (tendsto_pi_nhds.mpr hf),?_⟩
  intro x
  choose y hy h using fun n=> (s n).property.2 x
  have he : Tendsto y atTop (𝓝 (f x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    have h₂ := tendsto_iff_dist_tendsto_zero.mp (hf x)
    refine squeeze_zero (g:=fun n=>eps n+dist (g n x) (f x)) (fun _=>dist_nonneg) (fun n=> ?_) ?_
    · exact le_trans (dist_triangle (y n) (g n x) (f x)) (add_le_add (h n) le_rfl)
    simpa [eps] using h₁.add h₂
  exact hc.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds he) (Eventually.of_forall hy)
end
end GeneralMahler.Select

end

end OAI
