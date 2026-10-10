import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OrderedSubdivision
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierStartGerm

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section OpenAffineCharts
open Classical Set

noncomputable def openSquareChart {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) : Set (ℝ×ℝ) :=
  squareInterior ∩ strictLineCell a (fun l : T => l.val.1)
    (fun l => ordinary l.val.2) (fun l => squareSign l.val p)

theorem openSquareChart_open {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) :
    IsOpen (openSquareChart T p) := by
  apply ((isOpen_Ioo : IsOpen (Ioo (0:ℝ) 1)).prod isOpen_Ioo).inter
  have he : strictLineCell a (fun l : T => l.val.1) (fun l => ordinary l.val.2)
      (fun l => squareSign l.val p)=⋂l : T,{x | if squareSign l.val p then
      cutForm a l.val.1 x < ordinary l.val.2 else ordinary l.val.2 < cutForm a l.val.1 x} := by
    ext x
    simp [strictLineCell]
  rw [he]
  apply isOpen_iInter_of_finite
  intro l
  split_ifs
  · exact isOpen_lt (cutForm_continuous a l.val.1) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a l.val.1)

theorem openSquareChart_convex {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) :
    Convex ℝ (openSquareChart T p) :=
  ((convex_Ioo (0:ℝ) 1).prod (convex_Ioo (0:ℝ) 1)).inter (strictLineCell_convex _ _ _ _)

theorem self_mem_openSquareChart {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) :
    p.val ∈ openSquareChart T p := by
  refine ⟨generic_mem_squareInterior p,?_⟩
  intro l
  by_cases h : cutForm a l.val.1 p.val < ordinary l.val.2
  · simp [squareSign,h]
  · simpa [squareSign,h] using
      lt_of_le_of_ne (le_of_not_gt h) (p.property.2.2 l.val.1 l.val.2).symm

theorem openSquareChart_signs {a : ℕ} {T : Finset PlaneCut} {p : GenericSquare a}
    {x : ℝ×ℝ} (hx : x ∈ openSquareChart T p) {l : PlaneCut} (hl : l ∈ T) :
    cutForm a l.1 x ≠ ordinary l.2 ∧
      (cutForm a l.1 x < ordinary l.2 ↔ cutForm a l.1 p.val < ordinary l.2) := by
  have hh := hx.2 ⟨l,hl⟩
  by_cases h : cutForm a l.1 p.val < ordinary l.2
  · have ht : cutForm a l.1 x < ordinary l.2 := by simpa [squareSign,h] using hh
    exact ⟨ne_of_lt ht,iff_of_true ht h⟩
  · have ht : ordinary l.2 < cutForm a l.1 x := by simpa [squareSign,h] using hh
    exact ⟨ne_of_gt ht,iff_of_false (not_lt_of_gt ht) h⟩

theorem squareArrangement_on_openChart {a : ℕ} {K : Type*}
    (f : GenericSquare a → K) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) → f p=f q)
    (p q : GenericSquare a) (hq : q.val ∈ openSquareChart T p) : f q=f p :=
  hT q p (fun _ hl => decide_eq_decide.mpr (openSquareChart_signs hq hl).2)

theorem open_subset_closed_of_dense {X : Type*} [TopologicalSpace X]
    {D C A : Set X} (hD : Dense D) (hC : IsOpen C) (hA : IsClosed A)
    (h : C ∩ D ⊆ A) : C ⊆ A := by
  intro x hx
  by_contra hn
  have hne : (C ∩ Aᶜ).Nonempty := ⟨x,hx,hn⟩
  obtain ⟨y,hy,hyD⟩ := hD.inter_open_nonempty (C ∩ Aᶜ) (hC.inter hA.isOpen_compl) hne
  exact hy.2 (h ⟨hy.1,hyD⟩)

theorem open_translation_square {a : ℕ} {C : Set (ℝ×ℝ)} (hC : IsOpen C)
    (hCs : C ⊆ squareInterior) (u : CutRing×CutRing)
    (hgen : ∀p : GenericSquare a,p.val ∈ C → p.val+(ordinary u.1,ordinary u.2) ∈ squareInterior) :
    (fun x => x+(ordinary u.1,ordinary u.2)) '' C ⊆ squareInterior := by
  let v := (ordinary u.1,ordinary u.2)
  let W := (fun x => x+v) '' C
  have hW : IsOpen W := (Homeomorph.addRight v).isOpenMap C hC
  have hWclosed : W ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    apply open_subset_closed_of_dense (avoidsCuts_dense a) hW (isClosed_Icc.prod isClosed_Icc)
    rintro y ⟨⟨x,hx,rfl⟩,hy⟩
    have hg : AvoidsCuts a x := by
      have hh := avoidsCuts_translate hy (-u)
      simpa [v,map_neg,←Prod.neg_mk] using hh
    have hp : x.1 ∈ Ico (0:ℝ) 1 ∧ x.2 ∈ Ico (0:ℝ) 1 ∧ AvoidsCuts a x :=
      ⟨⟨(hCs hx).1.1.le,(hCs hx).1.2⟩,⟨(hCs hx).2.1.le,(hCs hx).2.2⟩,hg⟩
    have hi := hgen ⟨x,hp⟩ hx
    exact ⟨⟨hi.1.1.le,hi.1.2.le⟩,⟨hi.2.1.le,hi.2.2.le⟩⟩
  have hh := hW.subset_interior_iff.mpr hWclosed
  simpa only [interior_prod_eq,interior_Icc,squareInterior] using hh

theorem fullGroupAffineChart_square {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a) :
    (fun x => x+(ordinary (fullGroupAffineData g i p).2.1,
      ordinary (fullGroupAffineData g i p).2.2)) '' openSquareChart T p ⊆ squareInterior := by
  apply open_translation_square (openSquareChart_open T p) (fun _ h => h.1)
  intro q hq
  have hf := squareArrangement_on_openChart (fullGroupAffineData g i) T hT p q hq
  have hg := fullGroupSquareShift_spec g i q
  change (g.val (i,q)).2.val=q.val+(ordinary (fullGroupAffineData g i q).2.1,
      ordinary (fullGroupAffineData g i q).2.2) at hg
  rw [hf] at hg
  rw [←hg]
  exact generic_mem_squareInterior _

end OpenAffineCharts

section ChartLineIntervals
open Classical Set

noncomputable def chartCrossingParameter (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut) : ℝ :=
  (ordinary l.2-cutForm a l.1 (barrierLinePoint a j c 0))/cutForm a l.1 (barrierTangent a j)

theorem chartCrossingParameter_spec (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut)
    (hl : cutForm a l.1 (barrierTangent a j) ≠ 0) :
    cutForm a l.1 (barrierLinePoint a j c (chartCrossingParameter a j c l))=ordinary l.2 := by
  rw [barrier_cut_difference a j l.1 c 0]
  simp only [sub_zero,chartCrossingParameter,div_mul_cancel₀ _ hl]
  ring

theorem chartCrossingParameter_unique (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut)
    (hl : cutForm a l.1 (barrierTangent a j) ≠ 0) {r : ℝ}
    (hr : cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) :
    r=chartCrossingParameter a j c l := by
  have hd := barrier_cut_difference a j l.1 c 0 r
  dsimp [chartCrossingParameter]
  apply (eq_div_iff hl).mpr
  simpa only [sub_zero] using (eq_sub_iff_add_eq.mpr (by linarith :
    r*cutForm a l.1 (barrierTangent a j)+cutForm a l.1 (barrierLinePoint a j c 0)=ordinary l.2))

theorem openSquareChart_line_interval {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a)
    {j : Fin 4} {c : CutRing} {N x : ℝ} (hc : c ∈ barrierCandidate a j N)
    (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    ∃L U : ℝ,x ∈ Ioo L U ∧
      L ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      U ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      (∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ openSquareChart T p) ∧
      (∀r ∈ ({L,U} : Finset ℝ),r=barrierLineLower a j c ∨ r=barrierLineUpper a j c ∨
        ∃l ∈ T,j ≠ l.1 ∧ cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) := by
  let lo := barrierLineLower a j c
  let hi := barrierLineUpper a j c
  let R := T.filter (fun l => cutForm a l.1 (barrierTangent a j) ≠ 0)
  let E := (({lo,hi} : Finset ℝ) ∪ R.image (chartCrossingParameter a j c)).filter (fun r => r ∈ Icc lo hi)
  have hxin : x ∈ Ioo lo hi := (barrierLinePoint_interior_iff hc x).mp hx.1
  have hgap : lo ≤ hi := hxin.1.le.trans hxin.2.le
  have hlo : lo ∈ E := by simp [E,hgap]
  have hhi : hi ∈ E := by simp [E,hgap]
  have hxE : x ∉ E := by
    intro he
    have hh := (Finset.mem_filter.mp he).1
    rcases Finset.mem_union.mp hh with hh | hh
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with hh | hh
      · exact (ne_of_gt hxin.1) hh
      · exact (ne_of_lt hxin.2) hh
    · obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hh
      obtain ⟨hlT,hlne⟩ := Finset.mem_filter.mp hl
      exact (openSquareChart_signs hx hlT).1 (he ▸ chartCrossingParameter_spec a j c l hlne)
  obtain ⟨L,U,hLU,hxLU⟩ := exists_consecutiveSubdivision E hlo hhi ⟨hxin.1.le,hxin.2⟩
  have hxL : L < x := lt_of_le_of_ne hxLU.1 (fun h => hxE (h ▸ hLU.1))
  have hxU : x < U := lt_of_le_of_ne hxLU.2 (fun h => hxE (h.symm ▸ hLU.2.1))
  have hL := (Finset.mem_filter.mp hLU.1).2
  have hU := (Finset.mem_filter.mp hLU.2.1).2
  have hn (l : PlaneCut) (hl : l ∈ T) (r : ℝ) (hr : r ∈ Ioo L U) :
      cutForm a l.1 (barrierLinePoint a j c r) ≠ ordinary l.2 := by
    intro he
    by_cases hzero : cutForm a l.1 (barrierTangent a j)=0
    · have hh := barrier_cut_difference a j l.1 c r x
      rw [hzero,mul_zero,add_zero,he] at hh
      exact (openSquareChart_signs hx hl).1 hh
    · have hre : r ∈ E := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,hzero⟩,?_⟩),
          ⟨hL.1.trans hr.1.le,hr.2.le.trans hU.2⟩⟩
        exact (chartCrossingParameter_unique a j c l hzero he).symm
      exact not_le_of_gt hr.2 (hLU.2.2.2 r hre hr.1)
  refine ⟨L,U,⟨hxL,hxU⟩,hL,hU,?_,?_⟩
  · intro r hr
    refine ⟨(barrierLinePoint_interior_iff hc r).mpr ⟨hL.1.trans_lt hr.1,hr.2.trans_le hU.2⟩,?_⟩
    intro l
    have hs := continuous_nonzero_sign isPreconnected_Ioo
      (((cutForm_continuous a l.val.1).comp (barrierLinePoint_continuous a j c)).sub continuous_const).continuousOn
      (fun t ht => sub_ne_zero.mpr (hn l.val l.property t ht)) hr ⟨hxL,hxU⟩
    have hsg : (cutForm a l.val.1 (barrierLinePoint a j c r) < ordinary l.val.2 ↔
      cutForm a l.val.1 (barrierLinePoint a j c x) < ordinary l.val.2) := by simpa only [Pi.sub_apply,Function.comp_apply,sub_lt_zero] using hs
    have hh := hx.2 l
    by_cases hl : squareSign l.val p=true
    · simpa [hl] using hsg.mpr (by simpa [hl] using hh)
    · have hnot : ¬cutForm a l.val.1 (barrierLinePoint a j c r) < ordinary l.val.2 :=
        fun h => not_lt_of_gt (by simpa [hl] using hh) (hsg.mp h)
      simpa [hl] using lt_of_le_of_ne (le_of_not_gt hnot) (hn l.val l.property r hr).symm
  · intro r hr
    have hre : r ∈ E := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl|rfl
      · exact hLU.1
      · exact hLU.2.1
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hre).1 with he | he
    · simp only [Finset.mem_insert,Finset.mem_singleton] at he
      exact he.elim Or.inl (fun h => Or.inr (Or.inl h))
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hlT,hlne⟩ := Finset.mem_filter.mp hl
      refine Or.inr (Or.inr ⟨l,hlT,?_,chartCrossingParameter_spec a j c l hlne⟩)
      intro he
      exact hlne (he ▸ barrierTangent_cut a j)

end ChartLineIntervals

end SimpleAmenable
end
end

end OAI
