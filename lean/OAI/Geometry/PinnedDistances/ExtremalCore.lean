import OAI.Geometry.PinnedDistances.ExtremalFractions

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

/- Finite extremal core construction. The truncated-fiber score gives the same
   core as pruning while avoiding an arbitrary pruning order. It uses the
   original fibers without a generic-position hypothesis. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Core
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]

structure Fibers (V : Type u3) (I : Type u4) [DecidableEq V] where
  source : I → V
  targets : I → Finset V
  no_loop : ∀ e, source e ∉ targets e
  disjoint : ∀ e f, e ≠ f → source e=source f → Disjoint (targets e) (targets f)

namespace Fibers
variable (G : Fibers V I)

def size (C : Finset V) (e : I) : ℕ := (G.targets e ∩ C).card

def contribution (K : ℝ) (C : Finset V) (e : I) : ℝ :=
  if G.source e ∈ C then max ((G.size C e : ℝ)-K) 0 else 0

def score (K : ℝ) (C : Finset V) : ℝ := ∑ e, G.contribution K C e

def active (K : ℝ) (C : Finset V) (e : I) : Prop :=
  G.source e ∈ C ∧ K < (G.size C e : ℝ)

instance (K : ℝ) (C : Finset V) (e : I) : Decidable (G.active K C e) := Classical.propDecidable _

def edge (K : ℝ) (C : Finset V) (x y : V) : Prop :=
  ∃ e, G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C

instance (K : ℝ) (C : Finset V) (x y : V) : Decidable (G.edge K C x y) := Classical.propDecidable _

def degree (K : ℝ) (C : Finset V) (v : V) : ℝ :=
  (Finset.univ.filter (G.edge K C v)).card + (Finset.univ.filter (fun x => G.edge K C x v)).card

def fiberDegree (K : ℝ) (C : Finset V) (v : V) (e : I) : ℝ :=
  if G.active K C e then
    (if G.source e=v then (G.size C e : ℝ) else 0) +
    (if v ∈ G.targets e ∩ C then 1 else 0)
  else 0

omit [Fintype V] [Fintype I] in
lemma size_mono {C D : Finset V} (h : C ⊆ D) (e : I) : G.size C e ≤ G.size D e :=
  Finset.card_le_card (Finset.inter_subset_inter_left h)

omit [Fintype V] [Fintype I] in
lemma size_erase (C : Finset V) (v : V) (e : I) :
    G.size (C.erase v) e = G.size C e - if v ∈ G.targets e ∩ C then 1 else 0 := by
  have he : G.targets e ∩ C.erase v=(G.targets e ∩ C).erase v := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_erase]
    tauto
  change (G.targets e ∩ C.erase v).card=_
  rw [he]
  by_cases hv : v ∈ G.targets e ∩ C
  · simp [size,hv,Finset.card_erase_of_mem hv]
  · simp [size,hv]

omit [Fintype V] [Fintype I] in
lemma contribution_nonneg (K : ℝ) (C : Finset V) (e : I) : 0 ≤ G.contribution K C e := by
  unfold contribution
  split_ifs <;> positivity

omit [Fintype V] [Fintype I] in
lemma contribution_mono (K : ℝ) {C D : Finset V} (h : C ⊆ D) (e : I) :
    G.contribution K C e ≤ G.contribution K D e := by
  unfold contribution
  by_cases hs : G.source e ∈ C
  · simp only [ite_eq_left hs,ite_eq_left (h hs)]
    exact max_le_max (sub_le_sub_right (by exact_mod_cast G.size_mono h e) K) le_rfl
  · simp only [ite_eq_right hs]
    split_ifs <;> positivity

omit [Fintype V] [Fintype I] in
lemma contribution_erase_loss (K : ℝ) (hK : 0 ≤ K) (C : Finset V) (v : V) (e : I) :
    G.contribution K C e-G.contribution K (C.erase v) e ≤ G.fiberDegree K C v e := by
  by_cases ha : G.active K C e
  · obtain ⟨hs,hk⟩ := ha
    rw [fiberDegree,ite_eq_left ⟨hs,hk⟩]
    by_cases hv : G.source e=v
    · have hno : v ∉ G.targets e ∩ C := by
        intro hh
        exact G.no_loop e (hv ▸ (Finset.mem_inter.mp hh).1)
      have he1 : G.contribution K C e=(G.size C e : ℝ)-K := by
        simp [contribution,hs,max_eq_left (le_of_lt (sub_pos.mpr hk))]
      have he0 : G.contribution K (C.erase v) e=0 := by simp [contribution,hv]
      rw [he1,he0,ite_eq_left hv,ite_eq_right hno]
      linarith
    · have hse : G.source e ∈ C.erase v := Finset.mem_erase.mpr ⟨hv,hs⟩
      simp only [contribution,ite_eq_left hs,ite_eq_left hse,ite_eq_right hv,zero_add,
        max_eq_left (le_of_lt (sub_pos.mpr hk))]
      by_cases hm : v ∈ G.targets e ∩ C
      · rw [ite_eq_left hm,G.size_erase,ite_eq_left hm]
        have hpos : 1 ≤ G.size C e := Finset.one_le_card.mpr ⟨v,hm⟩
        rw [Nat.cast_sub hpos]
        have hh := le_max_left ((G.size C e : ℝ)-1-K) 0
        norm_num only [Nat.cast_one]
        linarith
      · rw [ite_eq_right hm,G.size_erase,ite_eq_right hm,Nat.sub_zero,max_eq_left (le_of_lt (sub_pos.mpr hk))]
        simp
  · have hz : G.contribution K C e=0 := by
      unfold contribution
      by_cases hs : G.source e ∈ C
      · rw [ite_eq_left hs,max_eq_right]
        exact sub_nonpos.mpr (le_of_not_gt (fun hk => ha ⟨hs,hk⟩))
      · rw [ite_eq_right hs]
    rw [hz,fiberDegree,ite_eq_right ha,zero_sub]
    exact neg_nonpos.mpr (G.contribution_nonneg K _ e)

omit [Fintype V] [Fintype I] in
lemma edge_no_loop (K : ℝ) (C : Finset V) (v : V) : ¬G.edge K C v v := by
  rintro ⟨e,_,he,hv⟩
  exact G.no_loop e (he ▸ (Finset.mem_inter.mp hv).1)

omit [Fintype V] [Fintype I] in
lemma edge_unique (_K : ℝ) (_C : Finset V) (x y : V) {e f : I}
    (he : G.source e=x) (hf : G.source f=x) (hye : y ∈ G.targets e) (hyf : y ∈ G.targets f) : e=f := by
  by_contra hn
  exact Finset.disjoint_left.mp (G.disjoint e f hn (he.trans hf.symm)) hye hyf

lemma sum_fiberDegree (K : ℝ) (C : Finset V) (v : V) :
    (∑ e, G.fiberDegree K C v e)=G.degree K C v := by
  classical
  have hout (e : I) : (if G.active K C e then (if G.source e=v then (G.size C e : ℝ) else 0) else 0)=
      ∑ y : V, if G.active K C e ∧ G.source e=v ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0 := by
    by_cases ha : G.active K C e <;> by_cases hs : G.source e=v <;>
      simp [ha,hs,size]
    congr 1
    ext y
    simp
  have hin (e : I) : (if G.active K C e then (if v ∈ G.targets e ∩ C then (1:ℝ) else 0) else 0)=
      ∑ x : V, if G.active K C e ∧ G.source e=x ∧ v ∈ G.targets e ∩ C then (1:ℝ) else 0 := by
    by_cases ha : G.active K C e <;> by_cases hv : v ∈ G.targets e ∩ C <;> simp [ha,hv]
  have hone (x y : V) : (∑ e, if G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.edge K C x y then 1 else 0 := by
    by_cases hh : G.edge K C x y
    · obtain ⟨e,he,hs,hy⟩ := hh
      rw [ite_eq_left ⟨e,he,hs,hy⟩]
      rw [Finset.sum_eq_single e]
      · simp [he,hs,hy]
      · intro f _ hfe
        rw [ite_eq_right]
        rintro ⟨_,hfs,hfy⟩
        exact hfe (G.edge_unique K C x y hfs hs (Finset.mem_inter.mp hfy).1 (Finset.mem_inter.mp hy).1)
      · simp
    · have hn : ∀ e, ¬(G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C) :=
        fun e he => hh ⟨e,he⟩
      simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_right hh]
  have hs (e : I) : G.fiberDegree K C v e =
      (if G.active K C e then (if G.source e=v then (G.size C e : ℝ) else 0) else 0)+
      (if G.active K C e then (if v ∈ G.targets e ∩ C then (1:ℝ) else 0) else 0) := by
    unfold fiberDegree
    split_ifs <;> ring
  simp_rw [hs,hout,hin]
  rw [Finset.sum_add_distrib,Finset.sum_comm,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun e x => if G.active K C e ∧ G.source e=x ∧ v ∈ G.targets e ∩ C then (1:ℝ) else 0)]
  simp only [hone,degree,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

lemma score_erase_loss (K : ℝ) (hK : 0 ≤ K) (C : Finset V) (v : V) :
    G.score K C-G.score K (C.erase v) ≤ G.degree K C v := by
  rw [score,score,← Finset.sum_sub_distrib,← G.sum_fiberDegree K C v]
  exact Finset.sum_le_sum (fun e _ => G.contribution_erase_loss K hK C v e)

def penalty (a : ℝ) (C : Finset V) : ℝ := a*(C.card : ℝ)*((C.card : ℝ)-1)

def objective (K a : ℝ) (C : Finset V) : ℝ := G.score K C-penalty a C

/-- Constants here are finite numeric bounds on the original extremal scores.
    The proof is a maximization on subsets, not an assumption of a core. -/
theorem exists_core (K a U : ℝ) (hK : 0 ≤ K) (m₀ : ℕ) (hm : m₀ < Fintype.card V)
    (hboundary : ∀ C : Finset V, C.card=m₀ → G.score K C ≤ U*(m₀ : ℝ)*((m₀ : ℝ)-1))
    (hgap : (U-a)*(m₀ : ℝ)*((m₀ : ℝ)-1) < G.objective K a Finset.univ) :
    ∃ C : Finset V, m₀ < C.card ∧ G.objective K a Finset.univ ≤ G.objective K a C ∧
      ∀ v ∈ C, 2*a*((C.card : ℝ)-1) ≤ G.degree K C v := by
  classical
  let S : Finset (Finset V) := Finset.univ.filter (fun C => m₀ ≤ C.card)
  have hu : (Finset.univ : Finset V) ∈ S := by simp [S,le_of_lt hm]
  obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image S (G.objective K a) ⟨_,hu⟩
  have hmc : m₀ ≤ C.card := (Finset.mem_filter.mp hC).2
  have hge := hmax _ hu
  have hlt : m₀ < C.card := by
    by_contra hh
    have he : C.card=m₀ := le_antisymm (le_of_not_gt hh) hmc
    have hb := hboundary C he
    unfold objective penalty at hge hgap
    rw [he] at hge
    nlinarith
  refine ⟨C,hlt,hge,?_⟩
  intro v hv
  have hce : C.erase v ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_erase_of_mem hv]
    omega
  have hh := hmax _ hce
  have hl := G.score_erase_loss K hK C v
  have hn : 1 ≤ C.card := Finset.one_le_card.mpr ⟨v,hv⟩
  unfold objective penalty at hh
  rw [Finset.card_erase_of_mem hv,Nat.cast_sub hn] at hh
  norm_num at hh
  nlinarith

end Fibers
end WeakPinned.Core

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def edgeSet (K : ℝ) (C : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun xy => G.edge K C xy.1 xy.2)

omit [Fintype V] in
lemma edge_indicator (K : ℝ) (C : Finset V) (x y : V) :
    (∑ e, if G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.edge K C x y then 1 else 0 := by
  classical
  by_cases hh : G.edge K C x y
  · obtain ⟨e,he,hs,hy⟩ := hh
    rw [ite_eq_left ⟨e,he,hs,hy⟩,Finset.sum_eq_single e]
    · simp [he,hs,hy]
    · intro f _ hfe
      rw [ite_eq_right]
      rintro ⟨_,hfs,hfy⟩
      exact hfe (G.edge_unique K C x y hfs hs (Finset.mem_inter.mp hfy).1 (Finset.mem_inter.mp hy).1)
    · simp
  · have hn : ∀ e, ¬(G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C) :=
      fun e he => hh ⟨e,he⟩
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_right hh]

lemma edgeSet_card (K : ℝ) (C : Finset V) :
    ((G.edgeSet K C).card : ℝ)=∑ e, if G.active K C e then (G.size C e : ℝ) else 0 := by
  classical
  have he (e : I) : (∑ xy : V × V, if G.active K C e ∧ G.source e=xy.1 ∧ xy.2 ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.active K C e then (G.size C e : ℝ) else 0 := by
    by_cases ha : G.active K C e
    · simp only [ha,true_and,Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (G.source e)]
      · simp only [true_and]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
        change ((Finset.univ.filter (fun y => y ∈ G.targets e ∩ C)).card : ℝ) = (G.size C e : ℝ)
        simp only [size,Finset.mem_inter]
        congr 2
        ext y
        simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · simp [ha]
  change ((Finset.univ.filter (fun xy : V × V => G.edge K C xy.1 xy.2)).card : ℝ)=_
  rw [← Finset.sum_boole]
  simp_rw [← G.edge_indicator K C]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => he e)

omit [Fintype V] [Fintype I] in
lemma contribution_formula (K : ℝ) (C : Finset V) (e : I) :
    G.contribution K C e = if G.active K C e then (G.size C e : ℝ)-K else 0 := by
  unfold contribution active
  by_cases hs : G.source e ∈ C
  · by_cases hk : K < (G.size C e : ℝ)
    · simp [hs,hk,max_eq_left (le_of_lt (sub_pos.mpr hk))]
    · simp [hs,hk,max_eq_right (sub_nonpos.mpr (le_of_not_gt hk))]
  · simp [hs]

lemma score_le_edgeSet (K : ℝ) (hK : 0 ≤ K) (C : Finset V) :
    G.score K C ≤ (G.edgeSet K C).card := by
  rw [score,G.edgeSet_card]
  apply Finset.sum_le_sum
  intro e _
  rw [G.contribution_formula]
  split_ifs <;> linarith

lemma score_univ_lower (K : ℝ) :
    (∑ e, (G.targets e).card : ℝ)-K*(Fintype.card I : ℝ) ≤ G.score K Finset.univ := by
  have hh : ∀ e, (G.targets e).card-K ≤ G.contribution K Finset.univ e := by
    intro e
    simp [contribution,size]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hh e)
  simpa [Finset.sum_sub_distrib,score,mul_comm] using hs

lemma sum_sizes_le_edgeSet_univ (K : ℝ) (h : ∀ e, K < ((G.targets e).card : ℝ)) :
    (∑ e, ((G.targets e).card : ℝ))=(G.edgeSet K Finset.univ).card := by
  rw [G.edgeSet_card]
  apply Finset.sum_congr rfl
  intro e _
  have ha : G.active K Finset.univ e := by simp [active,size,h e]
  simp [ha,size]

lemma number_fibers (L K : ℝ) (hKL : K < L)
    (hL : ∀ e, L ≤ ((G.targets e).card : ℝ)) :
    (Fintype.card I : ℝ)*L ≤ (G.edgeSet K Finset.univ).card := by
  rw [← G.sum_sizes_le_edgeSet_univ K (fun e => hKL.trans_le (hL e))]
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hL e)

end WeakPinned.Core.Fibers

namespace WeakPinned
open WeakPinned.Core

def fiberIndices (P : Finset Plane) (s : ℝ) : Finset (Plane × ℝ) :=
  (richPairs P s).image (fun xy => (xy.1,dist xy.2 xy.1))

lemma index_source_mem (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) : e.val.1 ∈ P := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨hP,_,_⟩ := Finset.mem_filter.mp hxy
  rw [← he]
  exact (Finset.mem_product.mp hP).1

lemma index_radius_pos (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) : 0 < e.val.2 := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨_,hne,_⟩ := Finset.mem_filter.mp hxy
  rw [← he]
  exact dist_pos.mpr hne.symm

def planarFibers (P : Finset Plane) (s : ℝ) : Core.Fibers P (fiberIndices P s) where
  source e := ⟨e.val.1,index_source_mem P s e⟩
  targets e := Finset.univ.filter (fun y : P => dist y.val e.val.1=e.val.2)
  no_loop e := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,dist_self]
    exact (index_radius_pos P s e).ne
  disjoint e f hef hsrc := by
    apply Finset.disjoint_left.mpr
    intro y hye hyf
    have hs : e.val.1=f.val.1 := congrArg Subtype.val hsrc
    have he := (Finset.mem_filter.mp hye).2
    have hf := (Finset.mem_filter.mp hyf).2
    apply hef
    apply Subtype.ext
    apply Prod.ext hs
    rw [← he,← hf,hs]

lemma planar_target_iff (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) (y : P) :
    y ∈ (planarFibers P s).targets e ↔ dist y.val e.val.1=e.val.2 := by
  simp [planarFibers]

lemma planar_fiber_card (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) :
    (P.card : ℝ)^s ≤ ((planarFibers P s).targets e).card := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp hxy
  have hsrc : e.val.1=xy.1 := (congrArg Prod.fst he).symm
  have hrad : e.val.2=dist xy.2 xy.1 := (congrArg Prod.snd he).symm
  have hi : Function.Injective (fun y : P => y.val) := Subtype.val_injective
  have heq : ((planarFibers P s).targets e).image (fun y : P => y.val)=distanceFiber P xy.1 xy.2 := by
    ext y
    simp only [Finset.mem_image,distanceFiber,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz' := (planar_target_iff P s e z).mp hz
      rw [hsrc,hrad] at hz'
      refine ⟨⟨?_,z.property⟩,hz'⟩
      intro hh
      rw [hh,dist_self] at hz'
      exact (dist_pos.mpr hne.symm).ne hz'
    · rintro ⟨⟨_,hy⟩,hd⟩
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      apply (planar_target_iff _ _ _ _).mpr
      simpa [hsrc,hrad] using hd
  have hc : ((planarFibers P s).targets e).card = k P xy.1 xy.2 := by
    rw [← Finset.card_image_of_injective _ hi,heq]
    rfl
  rw [hc]
  exact hk

/-- Return from a subset of labelled vertices to the original plane, retaining
    all distances and its exact cardinality. -/
def planeSubset (P : Finset Plane) (C : Finset P) : Finset Plane := C.image Subtype.val

lemma planeSubset_card (P : Finset Plane) (C : Finset P) : (planeSubset P C).card=C.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

lemma restricted_targets_subset (P : Finset Plane) (s : ℝ) (C : Finset P)
    (e : fiberIndices P s) (y : P) (hy : y ∈ (planarFibers P s).targets e) :
    (((planarFibers P s).targets e ∩ C).image Subtype.val) ⊆
      distanceFiber (planeSubset P C) e.val.1 y.val := by
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
  subst z
  obtain ⟨hzt,hzC⟩ := Finset.mem_inter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_image.mpr ⟨w,hzC,rfl⟩⟩,?_⟩
  · intro hh
    have hd := (planar_target_iff P s e w).mp hzt
    rw [hh,dist_self] at hd
    exact (index_radius_pos P s e).ne hd
  · rw [(planar_target_iff _ _ _ _).mp hzt,(planar_target_iff _ _ _ _).mp hy]

lemma core_edge_rich (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK : (C.card : ℝ)^r ≤ K) (x y : P)
    (hxy : (planarFibers P s).edge K C x y) :
    (x.val,y.val) ∈ richPairs (planeSubset P C) r := by
  obtain ⟨e,⟨hs,hsize⟩,hsrc,hy⟩ := hxy
  have hxC : x ∈ C := hsrc ▸ hs
  have hyC := (Finset.mem_inter.mp hy).2
  have hyT := (Finset.mem_inter.mp hy).1
  have hne : x ≠ y := by
    intro hh
    exact (planarFibers P s).no_loop e (hsrc ▸ hh ▸ hyT)
  have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hxC,rfl⟩,
    Finset.mem_image.mpr ⟨y,hyC,rfl⟩⟩,?_,?_⟩
  · exact fun hh => hne (Subtype.ext hh)
  · rw [planeSubset_card]
    have hc := Finset.card_le_card (restricted_targets_subset P s C e y hyT)
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hsrc'] at hc
    have hc' : ((planarFibers P s).size C e : ℝ) ≤ k (planeSubset P C) x.val y.val := by
      exact_mod_cast hc
    exact hK.trans ((le_of_lt hsize).trans hc')

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma subtype_pair_injective (P : Finset Plane) :
    Function.Injective (fun xy : P × P => (xy.1.val,xy.2.val)) := by
  intro x y h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma core_edge_card (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK : (C.card : ℝ)^r ≤ K) :
    ((planarFibers P s).edgeSet K C).card ≤ (richPairs (planeSubset P C) r).card := by
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨xy,he,hval⟩ := Finset.mem_image.mp hz
  subst z
  exact core_edge_rich P s K r C hK xy.1 xy.2 (Finset.mem_filter.mp he).2

lemma core_score_bound (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK0 : 0 ≤ K) (hK : (C.card : ℝ)^r ≤ K) (hn : 2 ≤ C.card) :
    (planarFibers P s).score K C ≤ F C.card r*(C.card : ℝ)*((C.card : ℝ)-1) := by
  have hQ := fraction_le_F (planeSubset P C) r (by simpa [planeSubset_card] using hn)
  have hpos : 0 < (C.card : ℝ)*((C.card : ℝ)-1) := by
    have hh : (2:ℝ) ≤ C.card := by exact_mod_cast hn
    nlinarith
  rw [pairFraction,planeSubset_card,div_le_iff₀ hpos] at hQ
  calc
    _ ≤ (((planarFibers P s).edgeSet K C).card : ℝ) := (planarFibers P s).score_le_edgeSet K hK0 C
    _ ≤ ((richPairs (planeSubset P C) r).card : ℝ) := by exact_mod_cast core_edge_card P s K r C hK
    _ ≤ _ := by simpa only [mul_assoc] using hQ

lemma initial_edge_image (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    ((planarFibers P s).edgeSet K Finset.univ).image (fun xy : P × P => (xy.1.val,xy.2.val)) =
      richPairs P s := by
  ext xy
  constructor
  · intro h
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨e,_,hsrc,hy⟩ := (Finset.mem_filter.mp hxy).2
    have hyT := (Finset.mem_inter.mp hy).1
    have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
    have hr : dist y.val e.val.1=e.val.2 := (planar_target_iff P s e y).mp hyT
    have hne : x.val ≠ y.val := by
      intro hh
      rw [hsrc',hh,dist_self] at hr
      exact (index_radius_pos P s e).ne hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨x.property,y.property⟩,hne,?_⟩
    have hc := planar_fiber_card P s e
    have heq : ((planarFibers P s).targets e).image Subtype.val=distanceFiber P x.val y.val := by
      ext z
      constructor
      · intro hz
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        have hd := (planar_target_iff P s e w).mp hw
        rw [hsrc'] at hd hr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_erase.mpr ⟨?_,w.property⟩,hd.trans hr.symm⟩
        intro hh
        rw [hh,dist_self] at hd
        exact (index_radius_pos P s e).ne hd
      · intro hz
        obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
        have hzP := (Finset.mem_erase.mp hz).2
        refine Finset.mem_image.mpr ⟨⟨z,hzP⟩,?_,rfl⟩
        apply (planar_target_iff P s e _).mpr
        simpa [hsrc'] using hd.trans (by simpa [hsrc'] using hr)
    have hcard : ((planarFibers P s).targets e).card=k P x.val y.val := by
      rw [← Finset.card_image_of_injective _ Subtype.val_injective,heq]
      rfl
    simpa only [hcard] using hc
  · intro hxy
    obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hP
    let x : P := ⟨xy.1,hx⟩
    let y : P := ⟨xy.2,hy⟩
    let e : fiberIndices P s := ⟨(xy.1,dist xy.2 xy.1),Finset.mem_image.mpr ⟨xy,hxy,rfl⟩⟩
    refine Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    refine ⟨e,⟨Finset.mem_univ _,?_⟩,rfl,Finset.mem_inter.mpr ⟨?_,Finset.mem_univ _⟩⟩
    · simpa only [Core.Fibers.size,Finset.inter_univ] using hK.trans_le (planar_fiber_card P s e)
    · exact (planar_target_iff P s e y).mpr rfl

lemma initial_edge_card (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    ((planarFibers P s).edgeSet K Finset.univ).card=(richPairs P s).card := by
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P),initial_edge_image P s K hK]

lemma initial_score_lower (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    (richPairs P s).card-K*(Fintype.card (fiberIndices P s) : ℝ) ≤
      (planarFibers P s).score K Finset.univ := by
  have hh := (planarFibers P s).score_univ_lower K
  rw [(planarFibers P s).sum_sizes_le_edgeSet_univ K (fun e => hK.trans_le (planar_fiber_card P s e)),
    initial_edge_card P s K hK] at hh
  exact hh

lemma index_card_bound (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    (Fintype.card (fiberIndices P s) : ℝ)*(P.card : ℝ)^s ≤ (richPairs P s).card := by
  have hh := (planarFibers P s).number_fibers ((P.card : ℝ)^s) K hK (planar_fiber_card P s)
  simpa only [initial_edge_card P s K hK] using hh

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma initial_score_rate (P : Finset Plane) (s K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hK : K < (P.card : ℝ)^s) (hKL : K ≤ ρ*(P.card : ℝ)^s) :
    (richPairs P s).card-ρ*((P.card : ℝ)*((P.card : ℝ)-1)) ≤
      (planarFibers P s).score K Finset.univ := by
  have hf := index_card_bound P s K hK
  have hc : ((richPairs P s).card : ℝ) ≤ (P.card : ℝ)*((P.card : ℝ)-1) := by
    by_cases hn : 1 ≤ P.card
    · have hh := richPairs_card_le P s
      have hc' : ((richPairs P s).card : ℝ) ≤ (P.card*(P.card-1) : ℕ) := by exact_mod_cast hh
      simpa only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_one] using hc'
    · have hz : P.card=0 := by omega
      have hzero : (richPairs P s).card=0 := by
        have hh := richPairs_card_le P s
        rw [hz] at hh
        simpa using hh
      simp [hz,hzero]
  have hi0 : 0 ≤ (Fintype.card (fiberIndices P s) : ℝ) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hKL hi0
  have h2 := mul_le_mul_of_nonneg_left hf hρ
  have h3 := mul_le_mul_of_nonneg_left hc hρ
  have h4 := initial_score_lower P s K hK
  nlinarith

/-- A finite actual planar core. All hypotheses before the conclusion are
    scalar extremal bounds; the graph, degrees and surviving fibers are
    constructed, not postulated. -/
theorem finite_extremal_core (P : Finset Plane) (s r K θ η : ℝ) (m₀ : ℕ)
    (hn : 2 ≤ P.card) (hm0 : 2 ≤ m₀) (hm : m₀ < P.card)
    (hη : 0 < η) (hK0 : 0 ≤ K) (hK : K < (P.card : ℝ)^s)
    (hloss : K ≤ (η/8)*(P.card : ℝ)^s)
    (hinit : θ-η/8 ≤ pairFraction P s)
    (hboundary : (m₀ : ℝ)*((m₀ : ℝ)-1) ≤ (P.card : ℝ)*((P.card : ℝ)-1)/2)
    (hthreshold : ∀ m : ℕ, m₀ ≤ m → m ≤ P.card → (m : ℝ)^r ≤ K)
    (hext : ∀ m : ℕ, m₀ ≤ m → m ≤ P.card → F m r ≤ θ+η/8) :
    ∃ C : Finset P, m₀ < C.card ∧
      (θ-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ ((planarFibers P s).edgeSet K C).card ∧
      (((planarFibers P s).edgeSet K C).card : ℝ) ≤ (θ+η/8)*(C.card : ℝ)*((C.card : ℝ)-1) ∧
      (∀ x ∈ C, 2*(θ-η)*((C.card : ℝ)-1) ≤ (planarFibers P s).degree K C x) := by
  let G := planarFibers P s
  let A : ℝ := (P.card : ℝ)*((P.card : ℝ)-1)
  have hA : 0 < A := by
    have hh : (2:ℝ) ≤ P.card := by exact_mod_cast hn
    dsimp [A]
    nlinarith
  have hinit' : (θ-η/8)*A ≤ (richPairs P s).card := by
    simpa only [pairFraction,A,le_div_iff₀ hA] using hinit
  have hscore := initial_score_rate P s K (η/8) (by positivity) hK hloss
  have hscore' : (θ-η/4)*A ≤ G.score K Finset.univ := by
    change (richPairs P s).card-η/8*A ≤ G.score K Finset.univ at hscore
    nlinarith
  have hobj : 3*η/4*A ≤ G.objective K (θ-η) Finset.univ := by
    simp only [Core.Fibers.objective,Core.Fibers.penalty,Finset.card_univ,Fintype.card_coe]
    unfold A at hscore' ⊢
    nlinarith
  obtain ⟨C,hC,hge,hdeg⟩ := G.exists_core K (θ-η) (θ+η/8) hK0 m₀
    (by simpa using hm) (fun C hCm => by
      have hc := core_score_bound P s K r C hK0 (hCm ▸ hthreshold m₀ le_rfl (le_of_lt hm)) (by omega)
      rw [hCm] at hc
      have hmR : (1:ℝ) ≤ m₀ := by exact_mod_cast (show 1 ≤ m₀ by omega)
      have he := mul_le_mul_of_nonneg_right (hext m₀ le_rfl (le_of_lt hm))
        (mul_nonneg (Nat.cast_nonneg m₀) (sub_nonneg.mpr hmR))
      dsimp [G]
      nlinarith) (by
      have hh := mul_le_mul_of_nonneg_left hboundary (show 0 ≤ 9*η/8 by positivity)
      change _ < G.objective K (θ-η) Finset.univ
      unfold A at hobj
      have hηA := mul_pos hη hA
      unfold A at hηA
      nlinarith)
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hCm : m₀ ≤ C.card := le_of_lt hC
  have hC1 : (1:ℝ) ≤ C.card := by exact_mod_cast (show 1 ≤ C.card by omega)
  have hprod : 0 ≤ (C.card : ℝ)*((C.card : ℝ)-1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hC1)
  have hscore0 : (θ-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ G.score K C := by
    have hh : 0 ≤ G.objective K (θ-η) Finset.univ := (le_of_lt (by positivity : 0 < 3*η/4*A)).trans hobj
    unfold Core.Fibers.objective Core.Fibers.penalty at hge hh
    linarith
  have hedge := core_edge_card P s K r C (hthreshold C.card hCm hCn)
  have hQ := fraction_le_F (planeSubset P C) r (by simpa [planeSubset_card] using (show 2 ≤ C.card by omega))
  rw [pairFraction,planeSubset_card] at hQ
  have hp : 0 < (C.card : ℝ)*((C.card : ℝ)-1) := by
    have h2 : (2:ℝ) ≤ C.card := by exact_mod_cast (show 2 ≤ C.card by omega)
    nlinarith
  rw [div_le_iff₀ hp] at hQ
  have he := mul_le_mul_of_nonneg_right (hext C.card hCm hCn) hprod
  refine ⟨C,hC,hscore0.trans (G.score_le_edgeSet K hK0 C),?_,hdeg⟩
  have he' : (((planarFibers P s).edgeSet K C).card : ℝ) ≤ (richPairs (planeSubset P C) r).card := by exact_mod_cast hedge
  nlinarith

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
