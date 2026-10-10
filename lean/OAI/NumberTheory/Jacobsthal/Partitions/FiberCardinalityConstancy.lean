import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.LocalGraphIff
import OAI.NumberTheory.Jacobsthal.Estimates.NestedDegreeBounds

namespace OAI

namespace Erdos970

section

namespace ErdosGlobalFiberBranches

noncomputable def orderIsoOfNatCardEq (α β : Type*) [LinearOrder α] [LinearOrder β]
    [Finite α] [Finite β] (h : Nat.card α = Nat.card β) : α ≃o β := by
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  exact (Fintype.orderIsoFinOfCardEq α rfl).symm.trans
    (Fintype.orderIsoFinOfCardEq β (by simpa only [Nat.card_eq_fintype_card] using h.symm))

theorem finite_orderIso_unique {α β : Type*} [LinearOrder α] [LinearOrder β]
    [Finite α] (f g : α ≃o β) : f = g := Subsingleton.elim f g

noncomputable def orderIsoOfStrictMonoSurjective {α β : Type*}
    [LinearOrder α] [LinearOrder β] (f : α → β) (hf : StrictMono f)
    (hs : Function.Surjective f) : α ≃o β :=
  { Equiv.ofBijective f ⟨hf.injective,hs⟩ with map_rel_iff' := hf.le_iff_le }

theorem orderIsoOfStrictMonoSurjective_apply {α β : Type*}
    [LinearOrder α] [LinearOrder β] (f : α → β) (hf : StrictMono f)
    (hs : Function.Surjective f) (a : α) :
    orderIsoOfStrictMonoSurjective f hf hs a = f a := rfl

end ErdosGlobalFiberBranches

end

section

open Filter Set
open scoped Topology ContDiff
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature

structure FiberCharts (Q : Bivariate) (x L U : ℝ) where
  a : ℝ
  b : ℝ
  left : a < x
  right : x < b
  finite_base : (boundedFiber Q x L U).Finite
  graph : boundedFiber Q x L U → ℝ → ℝ
  tube : boundedFiber Q x L U → Set ℝ
  tube_open : ∀ r, IsOpen (tube r)
  tube_base : ∀ r, (r : ℝ) ∈ tube r
  tube_interior : ∀ r, tube r ⊆ Ioo L U
  tube_disjoint : Pairwise fun r s => Disjoint (tube r) (tube s)
  graph_base : ∀ r, graph r x = r
  graph_smooth : ∀ r, ContDiffOn ℝ 2 (graph r) (Ioo a b)
  graph_inside : ∀ r, ∀ t ∈ Ioo a b, graph r t ∈ tube r
  graph_regular : ∀ r, ∀ t ∈ Ioo a b, peval (partialY Q) t (graph r t) ≠ 0
  zero_iff : ∀ r, ∀ t ∈ Ioo a b, ∀ y ∈ tube r, peval Q t y = 0 ↔ y = graph r t
  coverage : ∀ t ∈ Ioo a b, boundedFiber Q t L U = range (fun r => graph r t)
  ordered : ∀ t ∈ Ioo a b, StrictMono (fun r => graph r t)

theorem exists_bounded_fiber_charts (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0)
    (hregular : ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0) :
    Nonempty (FiberCharts Q x L U) := by
  classical
  let R := boundedFiber Q x L U
  have hR : R.Finite := boundedFiber_finite Q x L U L hL
  let : Fintype R := hR.fintype
  obtain ⟨V,hV,hsep⟩ := hR.t2_separation
  have hcharts (r : R) := exists_local_graph_iff Q x r r.property.2
    (hregular r r.property) (V r ∩ Ioo L U) ((hV r).2.inter isOpen_Ioo)
    ⟨(hV r).1,boundedFiber_interior Q x L U hL hU r.property⟩
  choose a b W f ha hb hWo hrW hWV hbase hC hmem hder hiff using hcharts
  have hWint (r : R) : W r ⊆ Ioo L U := fun y hy => (hWV r hy).2
  have hWd : Pairwise fun r s : R => Disjoint (W r) (W s) := by
    intro r s hrs
    apply (hsep r.property s.property (fun he => hrs (Subtype.ext he))).mono
    · exact fun y hy => (hWV r hy).1
    · exact fun y hy => (hWV s hy).1
  let K := Icc L U \ ⋃ r : R, W r
  have hK : IsCompact K := isCompact_Icc.diff (isOpen_iUnion hWo)
  have hKzero : ∀ y ∈ K, peval Q x y ≠ 0 := by
    intro y hy hzero
    have hyR : y ∈ R := ⟨hy.1,hzero⟩
    exact hy.2 (mem_iUnion.mpr ⟨⟨y,hyR⟩,hrW ⟨y,hyR⟩⟩)
  have hnoextra := compact_nonzero_eventually Q x K hK hKzero
  have hdomains : ∀ᶠ t in 𝓝 x, ∀ r : R, t ∈ Ioo (a r) (b r) :=
    eventually_all.mpr fun r => isOpen_Ioo.mem_nhds ⟨ha r,hb r⟩
  have hcont (r : R) : ContinuousAt (f r) x :=
    (hC r).continuousOn.continuousAt (isOpen_Ioo.mem_nhds ⟨ha r,hb r⟩)
  have horder : ∀ᶠ t in 𝓝 x, ∀ r s : R, r < s → f r t < f s t := by
    apply eventually_all.mpr
    intro r
    apply eventually_all.mpr
    intro s
    by_cases hrs : r < s
    · have hlt : f r x < f s x := by simpa only [hbase] using (show (r : ℝ) < (s : ℝ) from hrs)
      exact ((hcont r).eventually_lt (hcont s) hlt).mono fun t ht _ => ht
    · exact Eventually.of_forall fun t ht => (hrs ht).elim
  have hN : {t | (∀ r : R, t ∈ Ioo (a r) (b r)) ∧
      (∀ y ∈ K, peval Q t y ≠ 0) ∧ (∀ r s : R, r < s → f r t < f s t)} ∈ 𝓝 x :=
    hdomains.and (hnoextra.and horder)
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hs : Ioo (x-eps) (x+eps) ⊆ {t | (∀ r : R, t ∈ Ioo (a r) (b r)) ∧
      (∀ y ∈ K, peval Q t y ≠ 0) ∧ (∀ r s : R, r < s → f r t < f s t)} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨{
    a := x-eps
    b := x+eps
    left := by linarith
    right := by linarith
    finite_base := hR, graph := f, tube := W, tube_open := hWo, tube_base := hrW,
    tube_interior := hWint, tube_disjoint := hWd, graph_base := hbase,
    graph_smooth := fun r => (hC r).mono (fun t ht => (hs ht).1 r),
    graph_inside := fun r t ht => hmem r t ((hs ht).1 r),
    graph_regular := fun r t ht => hder r t ((hs ht).1 r),
    zero_iff := fun r t ht => hiff r t ((hs ht).1 r),
    coverage := ?_, ordered := fun t ht => (hs ht).2.2 }⟩
  intro t ht
  ext y
  constructor
  · intro hy
    have hyW : y ∈ ⋃ r : R, W r := by
      by_contra hn
      exact (hs ht).2.1 y ⟨hy.1,hn⟩ hy.2
    obtain ⟨r,hyr⟩ := mem_iUnion.mp hyW
    exact ⟨r,((hiff r t ((hs ht).1 r) y hyr).mp hy.2).symm⟩
  · rintro ⟨r,rfl⟩
    have hfW := hmem r t ((hs ht).1 r)
    exact ⟨Ioo_subset_Icc_self (hWint r hfW),
      (hiff r t ((hs ht).1 r) (f r t) hfW).mpr rfl⟩

end ErdosLocalFiberGraphs

end

section

open Set
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

noncomputable def chartOrderIso {Q : Bivariate} {x L U : ℝ}
    (c : FiberCharts Q x L U) (t : ℝ) (ht : t ∈ Ioo c.a c.b) :
    boundedFiber Q x L U ≃o boundedFiber Q t L U := by
  let f : boundedFiber Q x L U → boundedFiber Q t L U := fun r =>
    ⟨c.graph r t,by rw [c.coverage t ht]; exact mem_range_self r⟩
  apply orderIsoOfStrictMonoSurjective f
  · exact fun r s hrs => (c.ordered t ht) hrs
  · intro y
    have hy := (c.coverage t ht).subset y.property
    obtain ⟨r,hr⟩ := hy
    exact ⟨r,Subtype.ext hr⟩

theorem chartOrderIso_val {Q : Bivariate} {x L U : ℝ}
    (c : FiberCharts Q x L U) (t : ℝ) (ht : t ∈ Ioo c.a c.b)
    (r : boundedFiber Q x L U) : (chartOrderIso c t ht r : ℝ) = c.graph r t := rfl

end ErdosGlobalFiberBranches

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosCriticalGeometry

theorem boundedFiber_card_le_degree (Q : Bivariate) (x L U z : ℝ)
    (hz : peval Q x z ≠ 0) : (boundedFiber Q x L U).ncard ≤ Q.totalDegree := by
  classical
  have hf := boundedFiber_finite Q x L U z hz
  have hp : verticalPolynomial Q x ≠ 0 := by
    intro he
    apply hz
    rw [← verticalPolynomial_eval,he,Polynomial.eval_zero]
  calc
    (boundedFiber Q x L U).ncard = hf.toFinset.card := ncard_eq_toFinset_card _ hf
    _ ≤ (verticalPolynomial Q x).natDegree := Polynomial.card_le_degree_of_subset_roots (by
      intro y hy
      apply (Polynomial.mem_roots hp).mpr
      change (verticalPolynomial Q x).eval y = 0
      exact (verticalPolynomial_eval Q x y).trans (hf.mem_toFinset.mp hy).2)
    _ ≤ (nestedY ℝ Q).natDegree := Polynomial.natDegree_map_le
    _ ≤ Q.totalDegree := nestedY_degree_le ℝ Q

namespace FiberCharts
variable {Q : Bivariate} {x L U : ℝ} (c : FiberCharts Q x L U)

theorem fiber_finite {t : ℝ} (ht : t ∈ Ioo c.a c.b) :
    (boundedFiber Q t L U).Finite := by
  let := c.finite_base.fintype
  rw [c.coverage t ht]
  exact finite_range _

theorem fiber_card_eq {t : ℝ} (ht : t ∈ Ioo c.a c.b) :
    (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  rw [c.coverage t ht,ncard_range_of_injective (c.ordered t ht).injective,
    Nat.card_coe_set_eq]

theorem unique_root_in_tube (r : boundedFiber Q x L U) {t : ℝ}
    (ht : t ∈ Ioo c.a c.b) :
    ∃! y, y ∈ c.tube r ∧ peval Q t y = 0 := by
  refine ⟨c.graph r t,⟨c.graph_inside r t ht,?_⟩,?_⟩
  · exact (c.zero_iff r t ht _ (c.graph_inside r t ht)).mpr rfl
  · exact fun y hy => (c.zero_iff r t ht y hy.1).mp hy.2

theorem all_roots_regular {t : ℝ} (ht : t ∈ Ioo c.a c.b) :
    ∀ y ∈ boundedFiber Q t L U, peval (partialY Q) t y ≠ 0 := by
  intro y hy
  rw [c.coverage t ht] at hy
  obtain ⟨r,rfl⟩ := hy
  exact c.graph_regular r t ht
end FiberCharts

theorem locally_constant_fiber_card (Q : Bivariate) (x L U : ℝ)
    (hL : peval Q x L ≠ 0) (hU : peval Q x U ≠ 0)
    (hregular : ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ ∀ t ∈ Ioo a b,
      (boundedFiber Q t L U).Finite ∧
      (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  obtain ⟨c⟩ := exists_bounded_fiber_charts Q x L U hL hU hregular
  exact ⟨c.a,c.b,c.left,c.right,fun t ht => ⟨c.fiber_finite ht,c.fiber_card_eq ht⟩⟩

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection

def regularParameters (Q : Bivariate) (L U : ℝ) : Set ℝ :=
  {x | peval Q x L ≠ 0 ∧ peval Q x U ≠ 0 ∧
    ∀ y ∈ boundedFiber Q x L U, peval (partialY Q) x y ≠ 0}

theorem continuous_horizontal_eval (Q : Bivariate) (y : ℝ) :
    Continuous (fun t => peval Q t y) := by
  change Continuous (planeEval Q ∘ (fun t : ℝ => (t,y)))
  exact (contDiff_planeEval Q 0).continuous.comp (continuous_id.prodMk continuous_const)

theorem regularParameters_isOpen (Q : Bivariate) (L U : ℝ) :
    IsOpen (regularParameters Q L U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨c⟩ := exists_bounded_fiber_charts Q x L U hx.1 hx.2.1 hx.2.2
  have hleft := (continuous_horizontal_eval Q L).continuousAt.eventually_ne hx.1
  have hright := (continuous_horizontal_eval Q U).continuousAt.eventually_ne hx.2.1
  filter_upwards [hleft,hright,isOpen_Ioo.mem_nhds ⟨c.left,c.right⟩] with t htL htU ht
  exact ⟨htL,htU,c.all_roots_regular ht⟩

theorem fiber_card_eventually_eq (Q : Bivariate) (L U : ℝ) {x : ℝ}
    (hx : x ∈ regularParameters Q L U) :
    ∀ᶠ t in 𝓝 x, (boundedFiber Q t L U).ncard = (boundedFiber Q x L U).ncard := by
  obtain ⟨a,b,ha,hb,h⟩ := locally_constant_fiber_card Q x L U hx.1 hx.2.1 hx.2.2
  filter_upwards [isOpen_Ioo.mem_nhds ⟨ha,hb⟩] with t ht
  exact (h t ht).2

end ErdosLocalFiberGraphs

end

section

open Set Filter
open scoped Topology
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

theorem continuousOn_fiber_card (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hI : I ⊆ regularParameters Q L U) :
    ContinuousOn (fun x => (boundedFiber Q x L U).ncard) I := by
  intro x hx
  have he : (fun t => (boundedFiber Q t L U).ncard) =ᶠ[𝓝 x]
      (fun _ => (boundedFiber Q x L U).ncard) := fiber_card_eventually_eq Q L U (hI hx)
  have hc : ContinuousAt (fun t => (boundedFiber Q t L U).ncard) x :=
    continuousAt_const.congr he.symm
  exact hc.continuousWithinAt

theorem fiber_card_eq_on_preconnected (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hconn : IsPreconnected I) (hI : I ⊆ regularParameters Q L U)
    {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    (boundedFiber Q x L U).ncard = (boundedFiber Q t L U).ncard :=
  hconn.constant (continuousOn_fiber_card Q L U I hI) hx ht

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
