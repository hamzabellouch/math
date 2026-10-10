import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallRegrade
import OAI.Combinatorics.Chromatic.Walls.AllOrderSectionLine
import OAI.Combinatorics.Chromatic.Walls.ComparisonRefinement

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
structure LineRayData (v k : Module.Dual ℝ E) (a : ℝ) where
  root : M
  degree : ℕ
  degree_pos : 0<degree
  root_degree : HasRootDegree C degree root
  transverse : v (e root)≠0
  generic : ∀N,RayGeneric C N root ((k+a • v).toAddMonoidHom.comp e)

variable (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
omit [DecidableEq I] in
include he hdeg in
lemma lineRayData_nonempty (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    Nonempty (LineRayData C e v k a) := by
  obtain ⟨N,ha⟩:=ha
  obtain ⟨r,d,hd,_,hr,hv,hg⟩:=section_event_ray_all_orders C e he L hdeg N v k H a ha
  exact ⟨⟨r,d,hd,hr,hv,hg⟩⟩

def lineRayData (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    LineRayData C e v k a :=
  Classical.choice (lineRayData_nonempty C e he L hdeg v k H a ha)

lemma cutSide_decide (h : M →+ ℝ) (p : M) (hp : h p≠0) :
    cutSide (decide (0<h p)) h p := by
  classical
  by_cases hh : 0<h p
  · simp only [hh,decide_true,cutSide,↓reduceIte]
  · simpa [hh,cutSide] using lt_of_le_of_ne (le_of_not_gt hh) hp
end
end ElementaryPositivity.QuantumTorus

namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def actualLineLetter (a : ℝ) :
    ComparisonCrossing LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    if hp : (k+a • v) (e (simpleRoot C pc))=0 then
      .pure (decide (v (e (simpleRoot C pc))<0))
    else
      let data:=lineRayData C e he L hdeg v k H a ha
      let U:=completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))
      let side:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      let hs:=cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp
      let hf:=simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic side hs
      let hi:=simple_inverse_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic side hs
      orientedBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
        (mutationSize Ω C pc+1) U hf hi (decide (v (e data.root)<0))
  else .bounded 1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _)

include hdeg H in
lemma line_cut_event (a : ℝ) (ha : (k+a • v) (e (simpleRoot C pc))=0) :
    a∈lineEvents (realRootsThrough e C 1) v k := by
  by_contra hn
  exact line_chamber_of_not_event C e L hdeg 1 v k (H 1) a hn 1 one_pos le_rfl
    (simpleRoot C pc) (simpleRoot_degree C pc) ha

lemma actualLineLetter_high (a : ℝ) (N : ℕ) (hN : 1≤N)
    (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    CrossingTrivial LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) N
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) := by
  classical
  unfold actualLineLetter
  split
  · next hh=>
    split
    · next hp=>
      exact False.elim (ha (lineEvents_mono
        (realRootsThrough_mono C e hN) v k (line_cut_event C pc e L hdeg v k H a hp)))
    · apply orientedBounded_trivial
      exact line_chart_trivial C e L hdeg LaurentRay.vUnit Ω (simpleTotalTransport Ω C)
        N v k (H N) a ha
  · exact .bounded 1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _) (fun _ _=>rfl)
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
lemma sort_filter_subset {A : Type*} [LinearOrder A] (S T : Finset A) (h : S⊆T) :
    (T.sort (· ≥ ·)).filter (fun a=>decide (a∈S))=S.sort (· ≥ ·) := by
  classical
  have Hp : ((T.sort (· ≥ ·)).filter (fun a=>decide (a∈S))).Perm (S.sort (· ≥ ·)):=by
    apply (List.perm_ext_iff_of_nodup ((T.sort_nodup _).filter _) (S.sort_nodup _)).mpr
    intro a
    simp only [List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨fun ha=>ha.2,fun ha=>⟨h ha,ha⟩⟩
  exact Hp.eq_of_pairwise' (List.Pairwise.filter _ (T.pairwise_sort _)) (S.pairwise_sort _)

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (v k : Module.Dual ℝ E)
def intervalLineEvents (lo hi : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (lineEvents (realRootsThrough e C N) v k).filter (fun a=>lo<a ∧ a<hi)
lemma intervalLineEvents_mono (lo hi : ℝ) {N K : ℕ} (h : N≤K) :
    intervalLineEvents C e v k lo hi N⊆intervalLineEvents C e v k lo hi K := by
  classical
  intro a ha
  obtain ⟨ha,hab⟩:=Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e h) v k ha,hab⟩

def intervalEventList (lo hi : ℝ) (N : ℕ) : List ℝ :=
  (intervalLineEvents C e v k lo hi N).sort (· ≥ ·)

lemma intervalEventList_filter (lo hi : ℝ) {N K : ℕ} (h : N≤K) :
    (intervalEventList C e v k lo hi K).filter
      (fun a=>decide (a∈intervalLineEvents C e v k lo hi N))=
    intervalEventList C e v k lo hi N :=
  sort_filter_subset _ _ (intervalLineEvents_mono C e v k lo hi h)

lemma event_not_retained (lo hi : ℝ) {N K : ℕ} (a : ℝ)
    (ha : a∈intervalEventList C e v k lo hi K)
    (hn : a∉intervalLineEvents C e v k lo hi N) :
    a∉lineEvents (realRootsThrough e C N) v k := by
  classical
  have haF : a∈intervalLineEvents C e v k lo hi K:=Finset.mem_sort _ |>.mp ha
  intro ham
  exact hn (Finset.mem_filter.mpr ⟨ham,(Finset.mem_filter.mp haF).2⟩)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
