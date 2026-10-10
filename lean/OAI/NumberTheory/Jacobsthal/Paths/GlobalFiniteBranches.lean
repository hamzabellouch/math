import OAI.NumberTheory.Jacobsthal.Partitions.FiberCardinalityConstancy

namespace OAI

namespace Erdos970

section

open Set
open scoped Topology
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

structure RegularDomain (Q : Bivariate) (x L U : ℝ) (I : Set ℝ) : Prop where
  isOpen : IsOpen I
  isPreconnected : IsPreconnected I
  base_mem : x ∈ I
  regular : I ⊆ regularParameters Q L U

namespace RegularDomain
variable {Q : Bivariate} {x L U : ℝ} {I : Set ℝ} (d : RegularDomain Q x L U I)
include d

theorem fiber_finite {t : ℝ} (ht : t ∈ I) : (boundedFiber Q t L U).Finite :=
  boundedFiber_finite Q t L U L (d.regular ht).1

noncomputable def transport (t : ℝ) (ht : t ∈ I) :
    boundedFiber Q x L U ≃o boundedFiber Q t L U := by
  letI := (d.fiber_finite d.base_mem).fintype
  letI := (d.fiber_finite ht).fintype
  exact orderIsoOfNatCardEq _ _ (fiber_card_eq_on_preconnected Q L U I
    d.isPreconnected d.regular d.base_mem ht)

noncomputable def branch (r : boundedFiber Q x L U) (t : ℝ) : ℝ := by
  classical
  exact if ht : t ∈ I then (d.transport t ht r : ℝ) else r

theorem branch_eq_transport (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t = (d.transport t ht r : ℝ) := by simp only [branch,dite_eq_left ht]

theorem transport_base : d.transport x d.base_mem = OrderIso.refl (boundedFiber Q x L U) := by
  let := (d.fiber_finite d.base_mem).fintype
  exact finite_orderIso_unique _ _

theorem branch_base (r : boundedFiber Q x L U) : d.branch r x = r := by
  rw [d.branch_eq_transport r d.base_mem,d.transport_base]
  rfl

theorem branch_mem (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t ∈ boundedFiber Q t L U := by
  rw [d.branch_eq_transport r ht]
  exact (d.transport t ht r).property

theorem branch_ordered {t : ℝ} (ht : t ∈ I) : StrictMono (fun r => d.branch r t) := by
  intro r s hrs
  change d.branch r t < d.branch s t
  rw [d.branch_eq_transport r ht,d.branch_eq_transport s ht]
  exact (d.transport t ht).strictMono hrs

theorem branch_coverage {t : ℝ} (ht : t ∈ I) :
    boundedFiber Q t L U = range (fun r => d.branch r t) := by
  ext y
  constructor
  · intro hy
    obtain ⟨r,hr⟩ := (d.transport t ht).surjective ⟨y,hy⟩
    refine ⟨r,?_⟩
    change d.branch r t = y
    rw [d.branch_eq_transport r ht]
    exact congrArg Subtype.val hr
  · rintro ⟨r,rfl⟩
    exact d.branch_mem r ht

theorem branch_interior (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    d.branch r t ∈ Ioo L U :=
  boundedFiber_interior Q t L U (d.regular ht).1 (d.regular ht).2.1 (d.branch_mem r ht)

end RegularDomain

end ErdosGlobalFiberBranches

end

section

open Set Filter
open scoped Topology ContDiff
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs
namespace RegularDomain
variable {Q : Bivariate} {x L U : ℝ} {I : Set ℝ} (d : RegularDomain Q x L U I)

theorem transport_chart {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I)
    (c : FiberCharts Q t L U) (hsc : s ∈ Ioo c.a c.b) :
    d.transport s hs = (d.transport t ht).trans (chartOrderIso c s hsc) := by
  let := (d.fiber_finite d.base_mem).fintype
  exact finite_orderIso_unique _ _

theorem branch_eq_chart (r : boundedFiber Q x L U) {t s : ℝ}
    (ht : t ∈ I) (hs : s ∈ I) (c : FiberCharts Q t L U) (hsc : s ∈ Ioo c.a c.b) :
    d.branch r s = c.graph (d.transport t ht r) s := by
  rw [d.branch_eq_transport r hs,d.transport_chart ht hs c hsc]
  exact chartOrderIso_val c s hsc (d.transport t ht r)

theorem branch_smooth (r : boundedFiber Q x L U) : ContDiffOn ℝ 2 (d.branch r) I := by
  apply d.isOpen.contDiffOn_iff.mpr
  intro t ht
  obtain ⟨c⟩ := exists_bounded_fiber_charts Q t L U
    (d.regular ht).1 (d.regular ht).2.1 (d.regular ht).2.2
  have hc : ContDiffAt ℝ 2 (c.graph (d.transport t ht r)) t :=
    (c.graph_smooth _).contDiffAt (isOpen_Ioo.mem_nhds ⟨c.left,c.right⟩)
  apply hc.congr_of_eventuallyEq
  filter_upwards [d.isOpen.mem_nhds ht,isOpen_Ioo.mem_nhds ⟨c.left,c.right⟩] with s hsI hsC
  exact d.branch_eq_chart r ht hsI c hsC

theorem branch_derivatives (r : boundedFiber Q x L U) {t : ℝ} (ht : t ∈ I) :
    deriv (d.branch r) t =
      -peval (partialX Q) t (d.branch r t)/peval (partialY Q) t (d.branch r t) ∧
    deriv (deriv (d.branch r)) t =
      -peval (inflectionPolynomial Q) t (d.branch r t)/(peval (partialY Q) t (d.branch r t))^3 :=
  implicit_derivatives Q (d.branch r) d.isOpen (d.branch_smooth r)
    (fun _ hs => (d.branch_mem r hs).2) ht ((d.regular ht).2.2 _ (d.branch_mem r ht))

end RegularDomain

end ErdosGlobalFiberBranches

end

section

open Set
open scoped Topology ContDiff
namespace ErdosGlobalFiberBranches
open ErdosImplicitCurvature ErdosLocalFiberGraphs

theorem global_finite_ordered_branches (Q : Bivariate) (x L U : ℝ) (I : Set ℝ)
    (hopen : IsOpen I) (hconn : IsPreconnected I) (hx : x ∈ I)
    (hregular : I ⊆ regularParameters Q L U) :
    ∃ n : ℕ, n = (boundedFiber Q x L U).ncard ∧ n ≤ Q.totalDegree ∧
      ∃ f : Fin n → ℝ → ℝ,
        (∀ i, ContDiffOn ℝ 2 (f i) I) ∧
        (∀ t ∈ I, StrictMono (fun i => f i t)) ∧
        (∀ i, ∀ t ∈ I, f i t ∈ Ioo L U ∧ peval Q t (f i t) = 0 ∧
          peval (partialY Q) t (f i t) ≠ 0) ∧
        (∀ t ∈ I, boundedFiber Q t L U = range (fun i => f i t)) := by
  classical
  let d : RegularDomain Q x L U I := ⟨hopen,hconn,hx,hregular⟩
  let := (d.fiber_finite hx).fintype
  let n := (boundedFiber Q x L U).ncard
  let e : Fin n ≃o boundedFiber Q x L U :=
    Fintype.orderIsoFinOfCardEq _ (fintypeCard_eq_ncard _)
  refine ⟨n,rfl,boundedFiber_card_le_degree Q x L U L (hregular hx).1,
    (fun i => d.branch (e i)),(fun i => d.branch_smooth (e i)),?_,?_,?_⟩
  · exact fun t ht => (d.branch_ordered ht).comp e.strictMono
  · intro i t ht
    exact ⟨d.branch_interior (e i) ht,(d.branch_mem (e i) ht).2,
      (hregular ht).2.2 _ (d.branch_mem (e i) ht)⟩
  · intro t ht
    rw [d.branch_coverage ht]
    ext y
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨i,rfl⟩ := e.surjective r
      exact ⟨i,hr⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩

theorem global_branches_on_regular_domain (Q : Bivariate) (L U : ℝ) (I : Set ℝ)
    (hopen : IsOpen I) (hconn : IsPreconnected I)
    (hregular : I ⊆ regularParameters Q L U) :
    ∃ n ≤ Q.totalDegree, ∃ f : Fin n → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ 2 (f i) I) ∧
      (∀ t ∈ I, StrictMono (fun i => f i t)) ∧
      (∀ i, ∀ t ∈ I, f i t ∈ Ioo L U ∧ peval Q t (f i t) = 0 ∧
        peval (partialY Q) t (f i t) ≠ 0) ∧
      (∀ t ∈ I, boundedFiber Q t L U = range (fun i => f i t)) := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨x,hx⟩ := hI
    obtain ⟨n,_,hn,f,hf⟩ := global_finite_ordered_branches Q x L U I hopen hconn hx hregular
    exact ⟨n,hn,f,hf⟩
  · have hempty : I = ∅ := not_nonempty_iff_eq_empty.mp hI
    subst I
    refine ⟨0,Nat.zero_le _,Fin.elim0,?_,?_,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · simp
    · simp
    · simp

end ErdosGlobalFiberBranches

end

end Erdos970

end OAI
