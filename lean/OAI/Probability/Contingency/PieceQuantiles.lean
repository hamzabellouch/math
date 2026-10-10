import Mathlib
import OAI.Probability.Contingency.DenseRegularity

namespace OAI

/-! Piece Quantiles. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Contingency.Interpolation
noncomputable section

 

structure SourcePieces (n : ℕ) where
  lo : Fin n → ℝ
  hi : Fin n → ℝ
  lt : ∀ i,lo i < hi i
  ordered : ∀ i j,i < j → hi i ≤ lo j
  f : Fin n → ℝ → ℝ
  continuous : ∀ i,ContinuousOn (f i) (Icc (lo i) (hi i))
  positive : ∀ i x,x∈Icc (lo i) (hi i) → 0 < f i x

namespace SourcePieces
variable {n : ℕ}

def mass (P : SourcePieces n) (i : Fin n) : ℝ := ∫ x in P.lo i..P.hi i,P.f i x

def total (P : SourcePieces n) : ℝ := totalMass P.mass

theorem mass_pos (P : SourcePieces n) (i : Fin n) : 0 < P.mass i :=
  intervalIntegral.integral_pos (P.lt i) (P.continuous i)
    (fun x hx => (P.positive i x (Ioc_subset_Icc_self hx)).le)
    ⟨P.lo i,left_mem_Icc.mpr (P.lt i).le,P.positive i _ (left_mem_Icc.mpr (P.lt i).le)⟩

theorem total_pos (P : SourcePieces n) (hn : 0 < n) : 0 < P.total := by
  dsimp [total,totalMass]
  apply Finset.sum_pos (fun i _ => P.mass_pos i)
  exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩

def good (P : SourcePieces n) : Set ℝ := ⋃ i,probabilityPiece P.mass i

theorem good_measurable (P : SourcePieces n) : MeasurableSet P.good :=
  MeasurableSet.iUnion fun _ => measurableSet_Ioo

theorem good_subset (P : SourcePieces n) (hn : 0 < n) : P.good ⊆ Ioo 0 1 := by
  intro t ht
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  exact probabilityPiece_subset P.mass (fun i => (P.mass_pos i).le) (P.total_pos hn) i hi

theorem good_volume (P : SourcePieces n) (hn : 0 < n) : volume P.good=1 :=
  probabilityPieces_volume P.mass (fun i => (P.mass_pos i).le) (P.total_pos hn)

theorem good_ae (P : SourcePieces n) (hn : 0 < n) : P.good =ᵐ[volume] Ioo (0:ℝ) 1 := by
  apply ae_eq_of_subset_of_measure_ge (P.good_subset hn)
  · rw [P.good_volume hn]; simp
  · exact P.good_measurable.nullMeasurableSet
  · simp

 
theorem local_quantiles (P : SourcePieces n) (hn : 0 < n) :
    ∃ Q : Fin n → ℝ → ℝ,
      (∀ i,StrictMonoOn (Q i) (probabilityPiece P.mass i)) ∧
      ∀ i t,t∈probabilityPiece P.mass i → Q i t∈Ioo (P.lo i) (P.hi i) ∧
        HasDerivAt (Q i) (P.total/P.f i (Q i t)) t := by
  have hM := P.total_pos hn
  have hq (i) := positive_quantile (P.f i) (P.lo i) (P.hi i) (P.lt i) (P.continuous i) (P.positive i)
  choose hmi Q hmQ himQ hdQ using hq
  let A := fun (i : Fin n) (t : ℝ) => (P.total*t-prefixMass P.mass i)/P.mass i
  have hA (i t) (ht : t∈probabilityPiece P.mass i) : A i t∈Ioo 0 1 := by
    have h1 := (div_lt_iff₀ hM).mp ht.1
    have h2 := (lt_div_iff₀ hM).mp ht.2
    dsimp [A]
    constructor
    · apply div_pos _ (P.mass_pos i); nlinarith only [h1]
    · apply (div_lt_one (P.mass_pos i)).mpr; nlinarith only [h2]
  refine ⟨fun i t => Q i (A i t),fun i => ?_,fun i t ht => ?_⟩
  · intro t ht s hs hts
    apply hmQ i (hA i t ht) (hA i s hs)
    apply (div_lt_div_iff_of_pos_right (P.mass_pos i)).mpr
    have := mul_lt_mul_of_pos_left hts hM
    linarith
  · have hh := hdQ i (A i t) (hA i t ht)
    refine ⟨hh.1,?_⟩
    have hAd : HasDerivAt (A i) (P.total/P.mass i) t := by
      simpa only [A,mul_one,id_eq] using (((hasDerivAt_id t).const_mul P.total).sub_const (prefixMass P.mass i)).div_const (P.mass i)
    have hder := hh.2.comp t hAd
    apply hder.congr_deriv
    change P.mass i / P.f i (Q i (A i t)) * (P.total / P.mass i) = P.total / P.f i (Q i (A i t))
    field_simp [(P.mass_pos i).ne']

 

theorem quantile (P : SourcePieces n) (hn : 0 < n) :
    ∃ Q V : ℝ → ℝ,
      StrictMonoOn Q P.good ∧
      ∀ t∈P.good, 0 < V t ∧ HasDerivAt Q (P.total/V t) t ∧
        ∃ i,Q t∈Ioo (P.lo i) (P.hi i) ∧ V t=P.f i (Q t) := by
  classical
  obtain ⟨qi,hmi,hdi⟩ := P.local_quantiles hn
  let idx := fun t => if h : ∃ i,t∈probabilityPiece P.mass i then h.choose else ⟨0,hn⟩
  let Q := fun t => qi (idx t) t
  let V := fun t => P.f (idx t) (Q t)
  have hind (t i) (ht : t∈probabilityPiece P.mass i) : idx t=i := by
    dsimp [idx]
    have he : ∃ i,t∈probabilityPiece P.mass i := ⟨i,ht⟩
    rw [dite_eq_left he]
    by_contra hne
    have hdis := probabilityPiece_disjoint P.mass (fun i => (P.mass_pos i).le) (P.total_pos hn) hne
    exact disjoint_left.mp hdis he.choose_spec ht
  have hin (t) (ht : t∈P.good) : t∈probabilityPiece P.mass (idx t) := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    rw [hind t i hi]
    exact hi
  have hQ (i t) (ht : t∈probabilityPiece P.mass i) : Q t=qi i t := by
    dsimp [Q]; rw [hind t i ht]
  refine ⟨Q,V,?_,fun t ht => ?_⟩
  · intro t ht s hs hts
    have hit := hin t ht
    have his := hin s hs
    have hti := (hdi _ _ hit).1
    have hsi := (hdi _ _ his).1
    change qi (idx t) t < qi (idx s) s
    rcases lt_trichotomy (idx t) (idx s) with hlt|heq|hgt
    · exact hti.2.trans_le ((P.ordered _ _ hlt).trans hsi.1.le)
    · rw [heq] at hit ⊢
      exact hmi _ hit his hts
    · have hh := div_le_div_of_nonneg_right
        (prefix_next_le P.mass (fun i => (P.mass_pos i).le) (idx s) (idx t) hgt) (P.total_pos hn).le
      exact False.elim (not_lt_of_ge (his.2.le.trans (hh.trans hit.1.le)) hts)
  · have hi := hin t ht
    have hh := hdi _ _ hi
    refine ⟨P.positive _ _ (Ioo_subset_Icc_self hh.1),?_,idx t,hh.1,rfl⟩
    have hevent : Q =ᶠ[𝓝 t] qi (idx t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hi] with u hu
      exact hQ _ _ hu
    exact hh.2.congr_of_eventuallyEq hevent

end SourcePieces
end
end Contingency.Interpolation

 

 

open Set MeasureTheory
namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

theorem slices_constant (S : Finset (OpenBox (q+1))) (l x y : ℝ)
    (hx : x∈Ioo l (nextEndpoint (endpoints S) l))
    (hy : y∈Ioo l (nextEndpoint (endpoints S) l)) : slices S x=slices S y := by
  classical
  unfold slices
  congr 1
  ext B
  simp only [Finset.mem_filter]
  by_cases hB : B∈S
  · have h1 := endpoint_comparisons (endpoints S) l x y (B.lower 0) hx hy (lower_mem_endpoints S B hB)
    have h2 := endpoint_comparisons (endpoints S) l x y (B.upper 0) hx hy (upper_mem_endpoints S B hB)
    simp only [hB,true_and,h1.1,h2.2]
  · simp [hB]

def activeEndpoints (S : Finset (OpenBox (q+1))) : Finset ℝ := by
  classical
  exact (endpoints S).filter fun l =>
    ∃ x∈Ioo l (nextEndpoint (endpoints S) l),(boxUnion (slices S x)).Nonempty

theorem activeEndpoint_mem (S : Finset (OpenBox (q+1))) (l : ℝ) (hl : l∈activeEndpoints S) :
    l∈endpoints S := by
  classical
  exact (Finset.mem_filter.mp hl).1

theorem activeEndpoint_lt (S : Finset (OpenBox (q+1))) (l : ℝ) (hl : l∈activeEndpoints S) :
    l<nextEndpoint (endpoints S) l := by
  classical
  obtain ⟨x,hx,_⟩ := (Finset.mem_filter.mp hl).2
  exact hx.1.trans hx.2

def gridMidpoint (S : Finset (OpenBox (q+1))) (l : ℝ) : ℝ :=
  (l+nextEndpoint (endpoints S) l)/2

theorem midpoint_mem (S : Finset (OpenBox (q+1))) (l : ℝ) (hl : l∈activeEndpoints S) :
    gridMidpoint S l∈Ioo l (nextEndpoint (endpoints S) l) := by
  have hh := activeEndpoint_lt S l hl
  constructor <;> dsimp [gridMidpoint] <;> linarith

theorem activeSlice_nonempty (S : Finset (OpenBox (q+1))) (l : ℝ) (hl : l∈activeEndpoints S) :
    (boxUnion (slices S (gridMidpoint S l))).Nonempty := by
  classical
  obtain ⟨x,hx,hs⟩ := (Finset.mem_filter.mp hl).2
  rw [← slices_constant S l x (gridMidpoint S l) hx (midpoint_mem S l hl)]
  exact hs

def gridLower (S : Finset (OpenBox (q+1))) : Fin (activeEndpoints S).card ↪o ℝ :=
  (activeEndpoints S).orderEmbOfFin rfl

theorem gridLower_mem (S : Finset (OpenBox (q+1))) (i : Fin (activeEndpoints S).card) :
    gridLower S i∈activeEndpoints S := Finset.orderEmbOfFin_mem _ _ _

def boxPieces (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) : SourcePieces (activeEndpoints S).card where
  lo := gridLower S
  hi := fun i => nextEndpoint (endpoints S) (gridLower S i)
  lt := fun i => activeEndpoint_lt S _ (gridLower_mem S i)
  ordered := fun left right hij => nextEndpoint_le (endpoints S) (gridLower S left) (gridLower S right)
    (activeEndpoint_mem S _ (gridLower_mem S right)) ((gridLower S).strictMono hij)
  f := fun i x => ∫ y in boxUnion (slices S (gridMidpoint S (gridLower S i))),F.f (Fin.cons x y)
  continuous := fun index => (F.marginal_continuous (slices S (gridMidpoint S (gridLower S index)))).continuousOn
  positive := fun i x _ => (F.slice x).integral_pos _ (activeSlice_nonempty S _ (gridLower_mem S i))

theorem boxPieces_slice (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1))
    (i : Fin (activeEndpoints S).card) (x : ℝ)
    (hx : x∈Ioo ((boxPieces S F).lo i) ((boxPieces S F).hi i)) :
    (boxPieces S F).f i x=∫ y in boxUnion (slices S x),F.f (Fin.cons x y) := by
  change (∫ y in boxUnion (slices S (gridMidpoint S (gridLower S i))),F.f (Fin.cons x y))=_
  rw [slices_constant S (gridLower S i) _ x (midpoint_mem S _ (gridLower_mem S i)) hx]

theorem boxPieces_cover (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) (x : ℝ)
    (hx : x∉endpoints S) (hs : (boxUnion (slices S x)).Nonempty) :
    ∃ i,x∈Ioo ((boxPieces S F).lo i) ((boxPieces S F).hi i) := by
  classical
  obtain ⟨y,hy⟩ := hs
  obtain ⟨B,hB,hBy⟩ := (mem_boxUnion S (Fin.cons x y)).mp ((mem_slices S x y).mp hy)
  have hxB := hBy 0
  simp only [Fin.cons_zero] at hxB
  obtain ⟨l,hl,hxl⟩ := grid_covers (endpoints S) x _ _
    (lower_mem_endpoints S B hB) (upper_mem_endpoints S B hB) hxB.1 hxB.2 hx
  have hlA : l∈activeEndpoints S := Finset.mem_filter.mpr ⟨hl,x,hxl,y,hy⟩
  have hr : Set.range (gridLower S)=(activeEndpoints S : Set ℝ) := Finset.range_orderEmbOfFin _ _
  have hrl : l∈Set.range (gridLower S) := by rw [hr]; exact hlA
  obtain ⟨i,hi⟩ := hrl
  refine ⟨i,?_⟩
  change x∈Ioo (gridLower S i) (nextEndpoint (endpoints S) (gridLower S i))
  rw [hi]
  exact hxl

end
end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Interpolation.SourcePieces
noncomputable section
variable {n : ℕ}

def source (P : SourcePieces n) (x : ℝ) : ℝ :=
  ∑ i,(Ioo (P.lo i) (P.hi i)).indicator (P.f i) x

theorem support_disjoint (P : SourcePieces n) :
    Pairwise (fun i j => Disjoint (Ioo (P.lo i) (P.hi i)) (Ioo (P.lo j) (P.hi j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hh|hh
  · exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge (hx.2.le.trans (P.ordered i j hh)) hy.1
  · exact Set.disjoint_left.mpr fun x hx hy => not_lt_of_ge (hy.2.le.trans (P.ordered j i hh)) hx.1

theorem source_on (P : SourcePieces n) (i : Fin n) (x : ℝ) (hx : x∈Ioo (P.lo i) (P.hi i)) :
    P.source x=P.f i x := by
  classical
  rw [source,Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact Set.disjoint_left.mp (P.support_disjoint hji) hj hx
  · simp

theorem source_off (P : SourcePieces n) (x : ℝ) (hx : ∀ i,x∉Ioo (P.lo i) (P.hi i)) :
    P.source x=0 := by simp [source,hx]

theorem piece_integrable (P : SourcePieces n) (i : Fin n) :
    IntegrableOn (P.f i) (Ioo (P.lo i) (P.hi i)) :=
  ((P.continuous i).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

theorem source_integrable (P : SourcePieces n) : Integrable P.source :=
  integrable_finsetSum _ fun i _ => (P.piece_integrable i).integrable_indicator measurableSet_Ioo

theorem source_integral (P : SourcePieces n) : (∫ x,P.source x)=P.total := by
  dsimp only [source,total,totalMass]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator measurableSet_Ioo,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (P.lt i).le]
    rfl
  · intro i _
    exact (P.piece_integrable i).integrable_indicator measurableSet_Ioo

end
end Contingency.Interpolation.SourcePieces

 

 

open Set MeasureTheory
namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

 

theorem boxPieces_source_eq (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) (x : ℝ)
    (hx : x∉endpoints S) : (boxPieces S F).source x=marginal S F x := by
  classical
  by_cases hs : (boxUnion (slices S x)).Nonempty
  · obtain ⟨i,hi⟩ := boxPieces_cover S F x hx hs
    rw [(boxPieces S F).source_on i x hi,boxPieces_slice S F i x hi]
    rfl
  · have hzero : marginal S F x=0 := by
      rw [marginal,Set.not_nonempty_iff_eq_empty.mp hs]
      simp
    rw [hzero]
    apply SourcePieces.source_off
    intro i hi
    have hne := activeSlice_nonempty S _ (gridLower_mem S i)
    rw [slices_constant S (gridLower S i) _ x (midpoint_mem S _ (gridLower_mem S i)) hi] at hne
    exact hs hne

theorem boxPieces_source_ae (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) :
    (boxPieces S F).source =ᵐ[volume] marginal S F := by
  filter_upwards [(endpoints S).finite_toSet.countable.ae_notMem volume] with x hx
  exact boxPieces_source_eq S F x hx

 

theorem boxPieces_total (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) :
    (boxPieces S F).total=∫ z in boxUnion S,F.f z := by
  rw [← SourcePieces.source_integral,integral_congr_ae (boxPieces_source_ae S F)]
  exact (marginal_fubini S F).2

theorem activeEndpoints_nonempty (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1))
    (hs : (boxUnion S).Nonempty) : 0 < (activeEndpoints S).card := by
  by_contra hh
  have he : (activeEndpoints S).card=0 := Nat.eq_zero_of_not_pos hh
  have hm : (boxPieces S F).total=0 := by
    dsimp [SourcePieces.total,totalMass]
    have : IsEmpty (Fin (activeEndpoints S).card) := he ▸ inferInstanceAs (IsEmpty (Fin 0))
    exact Finset.sum_eq_zero fun i _ => isEmptyElim i
  rw [boxPieces_total S F] at hm
  exact (F.integral_pos S hs).ne' hm

end
end Contingency.Interpolation

 

 

open Set MeasureTheory Filter
open scoped Topology
namespace Contingency.Interpolation
noncomputable section

 

theorem piece_interpolation {n m : ℕ} (P : SourcePieces n) (Q : SourcePieces m)
    (hn : 0 < n) (hm : 0 < m) (H : ℝ → ℝ) (S : Set ℝ)
    (α β : ℝ) (ha : 0 < α) (hb : 0 < β) (hsum : α+β=1)
    (hS : MeasurableSet S) (hH : IntegrableOn H S) (hpH : ∀ x∈S,0 ≤ H x)
    (hmem : ∀ i x,x∈Ioo (P.lo i) (P.hi i) →
      ∀ j y,y∈Ioo (Q.lo j) (Q.hi j) → α*x+β*y∈S)
    (hcomp : ∀ i x,x∈Ioo (P.lo i) (P.hi i) →
      ∀ j y,y∈Ioo (Q.lo j) (Q.hi j) → P.f i x^α*Q.f j y^β ≤ H (α*x+β*y)) :
    P.total^α*Q.total^β ≤ ∫ x in S,H x := by
  obtain ⟨U,F,hu,hud⟩ := P.quantile hn
  obtain ⟨V,G,hv,hvd⟩ := Q.quantile hm
  let D := P.good ∩ Q.good
  have hD : MeasurableSet D := P.good_measurable.inter Q.good_measurable
  have hdae : D =ᵐ[volume] Ioo (0:ℝ) 1 := by
    filter_upwards [P.good_ae hn,Q.good_ae hm] with x hx hy
    change (x∈P.good) = (x∈Ioo (0:ℝ) 1) at hx
    change (x∈Q.good) = (x∈Ioo (0:ℝ) 1) at hy
    change (x∈P.good ∧ x∈Q.good) = (x∈Ioo (0:ℝ) 1)
    rw [hx,hy]; simp
  have hdvol : volume D=1 := by rw [measure_congr hdae]; simp
  let z := fun t => α*U t+β*V t
  let z' := fun t => α*(P.total/F t)+β*(Q.total/G t)
  have hz : StrictMonoOn z D := by
    intro x hx y hy hxy
    exact add_lt_add (mul_lt_mul_of_pos_left (hu hx.1 hy.1 hxy) ha)
      (mul_lt_mul_of_pos_left (hv hx.2 hy.2 hxy) hb)
  have hzder (t) (ht : t∈D) : HasDerivAt z (z' t) t := by
    exact ((hud t ht.1).2.1.const_mul α).add ((hvd t ht.2).2.1.const_mul β)
  have hzpos (t) (ht : t∈D) : 0 < z' t :=
    add_pos (mul_pos ha (div_pos (P.total_pos hn) (hud t ht.1).1))
      (mul_pos hb (div_pos (Q.total_pos hm) (hvd t ht.2).1))
  have hsub : z '' D ⊆ S := by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨i,hi,_⟩ := (hud t ht.1).2.2
    obtain ⟨j,hj,_⟩ := (hvd t ht.2).2.2
    exact hmem i _ hi j _ hj
  have hzwi (t) (ht : t∈D) : HasDerivWithinAt z (z' t) D t :=
    (hzder t ht).hasDerivWithinAt
  have hjint := (integrableOn_image_iff_integrableOn_abs_deriv_smul hD hzwi hz.injOn H).mp (hH.mono_set hsub)
  have heq := integral_image_eq_integral_abs_deriv_smul hD hzwi hz.injOn H
  have hecomp (t) (ht : t∈D) : P.total^α*Q.total^β ≤ |z' t| • H (z t) := by
    rw [smul_eq_mul,abs_of_pos (hzpos t ht)]
    obtain ⟨i,hi,hFi⟩ := (hud t ht.1).2.2
    obtain ⟨j,hj,hGj⟩ := (hvd t ht.2).2.2
    have h1 := transport_amgm P.total Q.total (F t) (G t) α β
      (P.total_pos hn) (Q.total_pos hm) (hud t ht.1).1 (hvd t ht.2).1 ha.le hb.le hsum
    have h2 := mul_le_mul_of_nonneg_left (hcomp i _ hi j _ hj) (hzpos t ht).le
    rw [← hFi,← hGj] at h2
    dsimp [z,z'] at *
    nlinarith only [h1,h2]
  have hinter : (∫ t in D,P.total^α*Q.total^β) ≤ ∫ t in D,|z' t| • H (z t) := by
    exact setIntegral_mono_on (integrableOn_const (by rw [hdvol]; exact ENNReal.one_ne_top)) hjint hD hecomp
  have hcint : (∫ t in D,P.total^α*Q.total^β)=P.total^α*Q.total^β := by
    simp [Measure.real,hdvol]
  rw [hcint,← heq] at hinter
  exact hinter.trans (setIntegral_mono_set hH (by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact hpH x hx) hsub.eventuallyLE)

end
end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Interpolation
noncomputable section

 
theorem cons_interpolation {q : ℕ} (α β x y : ℝ) (u v : Fin q → ℝ) :
    α • Fin.cons x u+β • Fin.cons y v=Fin.cons (α*x+β*y) (α • u+β • v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

 

theorem good_box_interpolation (q : ℕ) (S₁ S₂ S₀ : Finset (OpenBox q))
    (F₁ F₂ F₀ : GoodWeight q) (α β : ℝ) (ha : 0<α) (hb : 0<β) (hsum : α+β=1)
    (hmem : ∀ x∈boxUnion S₁,∀ y∈boxUnion S₂,α • x+β • y∈boxUnion S₀)
    (hcomp : ∀ x∈boxUnion S₁,∀ y∈boxUnion S₂,F₁.f x^α*F₂.f y^β ≤ F₀.f (α • x+β • y)) :
    (∫ x in boxUnion S₁,F₁.f x)^α*(∫ x in boxUnion S₂,F₂.f x)^β ≤ ∫ x in boxUnion S₀,F₀.f x := by
  induction q with
  | zero =>
    by_cases h₁ : (boxUnion S₁).Nonempty
    · by_cases h₂ : (boxUnion S₂).Nonempty
      · obtain ⟨x,hx⟩ := h₁
        obtain ⟨y,hy⟩ := h₂
        have hint (S : Finset (OpenBox 0)) (F : GoodWeight 0) (z : Fin 0 → ℝ) (hz : z∈boxUnion S) :
            (∫ w in boxUnion S,F.f w)=F.f z := by
          rw [← integral_indicator (boxUnion_measurable S),Measure.volume_pi_eq_dirac z,integral_dirac]
          exact Set.indicator_of_mem hz _
        rw [hint S₁ F₁ x hx,hint S₂ F₂ y hy,hint S₀ F₀ _ (hmem x hx y hy)]
        exact hcomp x hx y hy
      · rw [Set.not_nonempty_iff_eq_empty.mp h₂]
        simp only [setIntegral_empty,Real.zero_rpow hb.ne',mul_zero]
        exact F₀.integral_nonneg S₀
    · rw [Set.not_nonempty_iff_eq_empty.mp h₁]
      simp only [setIntegral_empty,Real.zero_rpow ha.ne',zero_mul]
      exact F₀.integral_nonneg S₀
  | succ q ih =>
    by_cases h₁ : (boxUnion S₁).Nonempty
    · by_cases h₂ : (boxUnion S₂).Nonempty
      · have hinter := piece_interpolation (boxPieces S₁ F₁) (boxPieces S₂ F₂)
          (activeEndpoints_nonempty S₁ F₁ h₁) (activeEndpoints_nonempty S₂ F₂ h₂)
          (marginal S₀ F₀) univ α β ha hb hsum MeasurableSet.univ
          (integrableOn_univ.mpr (marginal_fubini S₀ F₀).1)
          (fun x _ => marginal_nonneg S₀ F₀ x) (fun _ _ _ _ _ _ => mem_univ _) (by
            intro i x hx j y hy
            rw [boxPieces_slice S₁ F₁ i x hx,boxPieces_slice S₂ F₂ j y hy]
            apply ih (slices S₁ x) (slices S₂ y) (slices S₀ (α*x+β*y))
              (F₁.slice x) (F₂.slice y) (F₀.slice (α*x+β*y))
            · intro u hu v hv
              apply (mem_slices S₀ _ _).mpr
              rw [← cons_interpolation]
              exact hmem _ ((mem_slices S₁ x u).mp hu) _ ((mem_slices S₂ y v).mp hv)
            · intro u hu v hv
              have hh := hcomp _ ((mem_slices S₁ x u).mp hu) _ ((mem_slices S₂ y v).mp hv)
              rw [cons_interpolation] at hh
              exact hh)
        simpa only [boxPieces_total,setIntegral_univ,(marginal_fubini S₀ F₀).2] using hinter
      · rw [Set.not_nonempty_iff_eq_empty.mp h₂]
        simp only [setIntegral_empty,Real.zero_rpow hb.ne',mul_zero]
        exact F₀.integral_nonneg S₀
    · rw [Set.not_nonempty_iff_eq_empty.mp h₁]
      simp only [setIntegral_empty,Real.zero_rpow ha.ne',zero_mul]
      exact F₀.integral_nonneg S₀

end
end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

def clampBox (l u x : Fin q → ℝ) : Fin q → ℝ := fun i => max (l i) (min (u i) (x i))

theorem clampBox_mem (l u : Fin q → ℝ) (hle : l ≤ u) (x : Fin q → ℝ) :
    clampBox l u x∈Icc l u := by
  constructor
  · intro i; exact le_max_left _ _
  · intro i; exact max_le (hle i) (min_le_left _ _)

theorem clampBox_eq (l u x : Fin q → ℝ) (hx : x∈Icc l u) : clampBox l u x=x := by
  funext i
  exact (congrArg (max (l i)) (min_eq_right (hx.2 i))).trans (max_eq_right (hx.1 i))

theorem clampBox_continuous (l u : Fin q → ℝ) : Continuous (clampBox l u) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

 

theorem good_extension (l u : Fin q → ℝ) (hle : l ≤ u) (f : (Fin q → ℝ) → ℝ)
    (hc : ContinuousOn f (Icc l u)) (hp : ∀ x∈Icc l u,0<f x) :
    ∃ F : GoodWeight q,∀ x∈Icc l u,F.f x=f x := by
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image (continuous_norm.comp_continuousOn hc)
  refine ⟨⟨fun x => f (clampBox l u x),?_,?_,C,?_⟩,?_⟩
  · exact hc.comp_continuous (clampBox_continuous l u) (clampBox_mem l u hle)
  · intro x; exact hp _ (clampBox_mem l u hle x)
  · intro x; exact hC ⟨clampBox l u x,clampBox_mem l u hle x,rfl⟩
  · intro x hx; exact congrArg f (clampBox_eq l u x hx)

 

theorem finiteBoxInterpolation : FiniteBoxInterpolation := by
  intro q S₁ S₂ S₀ t ht ht1 l u hbox f₁ f₂ f₀ hc₁ hc₂ hc₀ hp hmem hcomp
  have hsub₁ : boxUnion S₁ ⊆ Icc l u := fun x hx => hbox (subset_closure (Or.inl (Or.inl hx)))
  have hsub₂ : boxUnion S₂ ⊆ Icc l u := fun x hx => hbox (subset_closure (Or.inl (Or.inr hx)))
  have hsub₀ : boxUnion S₀ ⊆ Icc l u := fun x hx => hbox (subset_closure (Or.inr hx))
  have hnon : 0 ≤ ∫ x in boxUnion S₀,f₀ x :=
    setIntegral_nonneg (boxUnion_measurable _) (fun x hx => (hp x (hsub₀ hx)).2.2.le)
  by_cases h₁ : (boxUnion S₁).Nonempty
  · by_cases h₂ : (boxUnion S₂).Nonempty
    · obtain ⟨z,hz⟩ := h₁
      have hlu : l ≤ u := (hsub₁ hz).1.trans (hsub₁ hz).2
      obtain ⟨F₁,he₁⟩ := good_extension l u hlu f₁ hc₁ (fun x hx => (hp x hx).1)
      obtain ⟨F₂,he₂⟩ := good_extension l u hlu f₂ hc₂ (fun x hx => (hp x hx).2.1)
      obtain ⟨F₀,he₀⟩ := good_extension l u hlu f₀ hc₀ (fun x hx => (hp x hx).2.2)
      have hinter := good_box_interpolation q S₁ S₂ S₀ F₁ F₂ F₀ (1-t) t (by linarith) ht (by ring) hmem (by
        intro x hx y hy
        rw [he₁ x (hsub₁ hx),he₂ y (hsub₂ hy),he₀ _ (hsub₀ (hmem x hx y hy))]
        exact hcomp x hx y hy)
      have hi₁ : (∫ x in boxUnion S₁,F₁.f x)=∫ x in boxUnion S₁,f₁ x :=
        setIntegral_congr_fun (boxUnion_measurable _) (fun x hx => he₁ x (hsub₁ hx))
      have hi₂ : (∫ x in boxUnion S₂,F₂.f x)=∫ x in boxUnion S₂,f₂ x :=
        setIntegral_congr_fun (boxUnion_measurable _) (fun x hx => he₂ x (hsub₂ hx))
      have hi₀ : (∫ x in boxUnion S₀,F₀.f x)=∫ x in boxUnion S₀,f₀ x :=
        setIntegral_congr_fun (boxUnion_measurable _) (fun x hx => he₀ x (hsub₀ hx))
      rwa [hi₁,hi₂,hi₀] at hinter
    · rw [Set.not_nonempty_iff_eq_empty.mp h₂]
      simpa only [setIntegral_empty,Real.zero_rpow ht.ne',mul_zero] using hnon
  · rw [Set.not_nonempty_iff_eq_empty.mp h₁]
    simpa only [setIntegral_empty,Real.zero_rpow (show 1-t ≠ 0 by linarith),zero_mul] using hnon

end
end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

def OpenBox.proper (B : OpenBox q) : Prop := ∀ i,B.lower i<B.upper i

def OpenBox.mix (B C : OpenBox q) (α β : ℝ) : OpenBox q :=
  ⟨fun i => α*B.lower i+β*C.lower i,fun i => α*B.upper i+β*C.upper i⟩

theorem OpenBox.proper_of_mem (B : OpenBox q) (x : Fin q → ℝ) (hx : x∈B.carrier) : B.proper :=
  fun i => (hx i (mem_univ i)).1.trans (hx i (mem_univ i)).2

theorem interval_mix (l u l' u' z α β : ℝ) (hlu : l<u) (hlu' : l'<u')
    (ha : 0<α) (hb : 0<β) (hz : α*l+β*l'<z ∧ z<α*u+β*u') :
    ∃ x∈Ioo l u,∃ y∈Ioo l' u',α*x+β*y=z := by
  let D := α*(u-l)+β*(u'-l')
  have hD : 0<D := add_pos (mul_pos ha (sub_pos.mpr hlu)) (mul_pos hb (sub_pos.mpr hlu'))
  let s := (z-(α*l+β*l'))/D
  have hs : 0<s := div_pos (sub_pos.mpr hz.1) hD
  have hs1 : s<1 := (div_lt_one hD).mpr (by dsimp [D]; linarith [hz.2])
  refine ⟨l+s*(u-l),⟨?_,?_⟩,l'+s*(u'-l'),⟨?_,?_⟩,?_⟩
  · nlinarith [mul_pos hs (sub_pos.mpr hlu)]
  · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hlu)]
  · nlinarith [mul_pos hs (sub_pos.mpr hlu')]
  · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hlu')]
  · have he : s*D=z-(α*l+β*l') := div_mul_cancel₀ _ hD.ne'
    dsimp [D] at he
    nlinarith only [he]

theorem OpenBox.mem_mix_iff (B C : OpenBox q) (hB : B.proper) (hC : C.proper)
    (α β : ℝ) (ha : 0<α) (hb : 0<β) (z : Fin q → ℝ) :
    z∈(B.mix C α β).carrier ↔ ∃ x∈B.carrier,∃ y∈C.carrier,α • x+β • y=z := by
  constructor
  · intro hz
    have h (i : Fin q) := interval_mix (B.lower i) (B.upper i) (C.lower i) (C.upper i)
      (z i) α β (hB i) (hC i) ha hb (hz i (mem_univ i))
    choose x hx y hy he using h
    exact ⟨x,fun i _ => hx i,y,fun i _ => hy i,funext he⟩
  · rintro ⟨x,hx,y,hy,rfl⟩
    intro i _
    exact ⟨add_lt_add (mul_lt_mul_of_pos_left (hx i (mem_univ i)).1 ha)
        (mul_lt_mul_of_pos_left (hy i (mem_univ i)).1 hb),
      add_lt_add (mul_lt_mul_of_pos_left (hx i (mem_univ i)).2 ha)
        (mul_lt_mul_of_pos_left (hy i (mem_univ i)).2 hb)⟩

def mixBoxes (S T : Finset (OpenBox q)) (α β : ℝ) : Finset (OpenBox q) := by
  classical
  exact ((S.filter OpenBox.proper) ×ˢ (T.filter OpenBox.proper)).image fun p => p.1.mix p.2 α β

theorem mem_mixBoxes (S T : Finset (OpenBox q)) (α β : ℝ) (ha : 0<α) (hb : 0<β) (z : Fin q → ℝ) :
    z∈boxUnion (mixBoxes S T α β) ↔ ∃ x∈boxUnion S,∃ y∈boxUnion T,α • x+β • y=z := by
  classical
  simp only [boxUnion,mem_iUnion,mixBoxes,Finset.mem_image,Finset.mem_product,Finset.mem_filter]
  constructor
  · rintro ⟨B,⟨⟨B₁,B₂⟩,⟨⟨h₁,hp₁⟩,⟨h₂,hp₂⟩⟩,rfl⟩,hz⟩
    obtain ⟨x,hx,y,hy,he⟩ := (B₁.mem_mix_iff B₂ hp₁ hp₂ α β ha hb z).mp hz
    exact ⟨x,⟨B₁,h₁,hx⟩,y,⟨B₂,h₂,hy⟩,he⟩
  · rintro ⟨x,⟨B₁,h₁,hx⟩,y,⟨B₂,h₂,hy⟩,he⟩
    refine ⟨B₁.mix B₂ α β,⟨(B₁,B₂),⟨⟨h₁,B₁.proper_of_mem x hx⟩,⟨h₂,B₂.proper_of_mem y hy⟩⟩,rfl⟩,?_⟩
    exact (B₁.mem_mix_iff B₂ (B₁.proper_of_mem x hx) (B₂.proper_of_mem y hy) α β ha hb z).mpr ⟨x,hx,y,hy,he⟩

 
theorem logconcave_interpolation (S T : Finset (OpenBox q)) (F : GoodWeight q)
    (α β : ℝ) (ha : 0<α) (hb : 0<β) (hab : α+β=1)
    (hc : ∀ x y,F.f x^α*F.f y^β ≤ F.f (α • x+β • y)) :
    (∫ x in boxUnion S,F.f x)^α*(∫ x in boxUnion T,F.f x)^β ≤
      ∫ x in boxUnion (mixBoxes S T α β),F.f x := by
  apply good_box_interpolation q S T (mixBoxes S T α β) F F F α β ha hb hab
  · intro x hx y hy
    exact (mem_mixBoxes S T α β ha hb _).mpr ⟨x,hx,y,hy,rfl⟩
  · intro x _ y _; exact hc x y

end
end Contingency.Interpolation

end

end OAI
