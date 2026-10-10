import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma bounded_first_crossing (f : V → ℝ) (D T : ℝ) (hD : 0≤D)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y|≤D)
    {a b : V} (w : H.Walk a b) (ha : f a<T) (hb : T≤f b) :
    ∃ x, ∃ p : H.Walk a x, p.support⊆w.support ∧
      (∀ v∈p.support, f v≤T+D) ∧ T≤f x := by
  induction w with
  | nil => exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T≤f c
    · refine ⟨c,hac.toWalk,?_,?_,hc⟩
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · exact (_root_.SimpleGraph.Walk.cons hac w).start_mem_support
        · exact List.mem_cons_of_mem a w.start_mem_support
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · linarith
        · have hh := (abs_le.mp (hf hac)).1
          linarith
    · obtain ⟨x,p,hp,hpb,hpx⟩ := ih (lt_of_not_ge hc) hb
      refine ⟨x,_root_.SimpleGraph.Walk.cons hac p,?_,?_,hpx⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons.mpr (Or.inr (hp hv))
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · rw [hv]
          linarith
        · exact hpb v hv

end SimpleGraph.Walk
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def axisExit (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) : Set (Set E) :=
  G.restrictedSeed A {x | L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D ∧
    |u x|≤L+D ∧ |v x|≤W} (G.inducedEdges {x | |u x|≤L+D ∧ |v x|≤W})

lemma axisExit_upper (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    IsUpperSet (G.axisExit u v A L W D b) := G.restrictedSeed_upper _ _ _
lemma axisExit_finiteWitness (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    BernoulliProduct.HasFiniteOpenWitness (G.axisExit u v A L W D b) :=
  G.restrictedSeed_finiteWitness _ _ _
lemma axisExit_measurable [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    MeasurableSet (G.axisExit u v A L W D b) := G.restrictedSeed_measurable _ _ _

lemma axisExit_iff (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) (ω : Set E) :
    ω∈G.axisExit u v A L W D b ↔
      ∃ a∈A, ∃ x, ∃ w : (G.openGraph ω).Walk a x,
        (∀ y∈w.support, |u y|≤L+D ∧ |v y|≤W) ∧
        L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1,hx.2.1⟩
    intro y hy
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hy
    exact G.walk_induced_support w hx.2.2 y hy
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.walk_reachable_induced _ ω w hw,
      hx.1,hx.2,hw x w.end_mem_support⟩

lemma axisExit_of_crossing (u v : V → ℝ) (A : Set V) (L W D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hal : |u a|<L)
    (w : (G.openGraph ω).Walk a x) (hx : L≤|u x|)
    (hv : ∀ y∈w.support, |v y|≤W) :
    ω∈G.axisExit u v A L W D true ∪ G.axisExit u v A L W D false := by
  have hu' : ∀ ⦃x y⦄, (G.openGraph ω).Adj x y → |abs (u x)-abs (u y)|≤D := by
    intro x y hxy
    exact (abs_abs_sub_abs_le _ _).trans (hu (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨y,p,hp,hpb,hpy⟩ := _root_.OAI.SimpleGraph.Walk.bounded_first_crossing (fun x => |u x|) D L hD hu' w hal hx
  have hpath : ∀ z∈p.support, |u z|≤L+D ∧ |v z|≤W :=
    fun z hz => ⟨hpb z hz,hv z (hp hz)⟩
  by_cases hy : 0≤u y
  · apply Or.inl
    apply (G.axisExit_iff u v A L W D true ω).mpr
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpy
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpb y p.end_mem_support
  · apply Or.inr
    apply (G.axisExit_iff u v A L W D false ω).mpr
    have hy' : u y≤0 := (lt_of_not_ge hy).le
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpy
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpb y p.end_mem_support

lemma favored_of_union [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : BernoulliProduct.HasFiniteOpenWitness A)
    (hwB : BernoulliProduct.HasFiniteOpenWitness B)
    (a : ℝ) (ha : 0≤a) (hu : 1-a^2<(BernoulliProduct.law q).real (A∪B)) :
    1-a<(BernoulliProduct.law q).real A ∨ 1-a<(BernoulliProduct.law q).real B := by
  have hH := BernoulliProduct.harris_finiteWitness q A B hA hB hwA hwB
  have hBmeas := BernoulliProduct.measurableSet_finiteWitness B hB hwB
  have hunion := measureReal_union_add_inter (s := A) hBmeas (μ := BernoulliProduct.law q)
    (measure_ne_top _ _) (measure_ne_top _ _)
  have hAl : (BernoulliProduct.law q).real A≤1 := measureReal_le_one
  have hBl : (BernoulliProduct.law q).real B≤1 := measureReal_le_one
  by_contra hn
  push Not at hn
  have hm : a^2≤(1-(BernoulliProduct.law q).real A)*(1-(BernoulliProduct.law q).real B) := by
    nlinarith [mul_le_mul (by linarith : a≤1-(BernoulliProduct.law q).real A)
      (by linarith : a≤1-(BernoulliProduct.law q).real B) ha (by linarith : 0≤1-(BernoulliProduct.law q).real A)]
  nlinarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
