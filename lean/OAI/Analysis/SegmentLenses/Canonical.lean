import OAI.Analysis.SegmentLenses.ConeNorms

namespace OAI

/-!
# Endpoint vectors and canonical bidual identifications
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section ConditionalGateL2
variable {I : Type*}



def dominatedL2 (m : lp (fun _ : I => ℝ) 2) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ 2*m i) : lp (fun _ : I => ℝ) 2 :=
  ⟨a, (lp.memℓp ((2:ℝ) • m)).mono (fun i => by
    rw [Real.norm_eq_abs,abs_of_nonneg (ha i)]
    change a i ≤ 2*m i
    exact hab i)⟩

@[simp] theorem dominatedL2_apply (m : lp (fun _ : I => ℝ) 2) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ 2*m i) (i : I) :
    dominatedL2 m a ha hab i = a i := rfl

end ConditionalGateL2

section EndpointL2Vectors
open scoped Classical
variable {V ΩP ΩM : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]
  [Fintype ΩP] [Fintype ΩM]



theorem endpoint_law_vectors {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hxn : 1-d ≤ ‖x‖) (hplus : ‖x+y‖ ≤ 1) (hminus : ‖x-y‖ ≤ 1)
    (p : Test V) (hpH : p.coeff.support ⊆ H) (hp : ‖p‖ = 1) (hxp : x (p : Primal V) = ‖x‖)
    (μP : FiniteLaw ΩP) (μM : FiniteLaw ΩM)
    (AP : ΩP → Representation V) (AM : ΩM → Representation V)
    (hAP : ∀ ω, (AP ω).energy ≤ 1) (hAM : ∀ ω, (AM ω).energy ≤ 1)
    (hmeanP : μP.expect (fun ω => (AP ω).value) = head K (x+y))
    (hmeanM : μM.expect (fun ω => (AM ω).value) = head K (x-y)) :
    (lawSlack μP AP p + lawError μP AP p ≤ 4*d) ∧
    (lawSlack μM AM p + lawError μM AM p ≤ 4*d) ∧
    μP.mean (fun ω => ‖(AP ω).value - ((AP ω).family.replacement p.coeff).value‖) ≤ 2*Real.sqrt d ∧
    μM.mean (fun ω => ‖(AM ω).value - ((AM ω).family.replacement p.coeff).value‖) ≤ 2*Real.sqrt d ∧
    ∃ mP mM m : lp (fun _ : {g // Gate H g} => ℝ) 2,
      (∀ g, mP g = μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|)) ∧
      (∀ g, mM g = μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)) ∧
      m = (1/2:ℝ) • (mP+mM) ∧ ‖m‖ ≤ Real.sqrt (6*d) ∧
      (∀ g, 0 ≤ mP g ∧ 0 ≤ mM g ∧ mP g ≤ 2*m g ∧ mM g ≤ 2*m g) := by
  obtain ⟨h1,h2,h3,h4,m,hm,hmn,hdom⟩ :=
    endpoint_laws_global hH hK hHK x y hx hd hd1 hxn hplus hminus p hpH hp hxp
      μP μM AP AM hAP hAM hmeanP hmeanM
  let aP := fun g : {g // Gate H g} => μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|)
  let aM := fun g : {g // Gate H g} => μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)
  let mP := dominatedL2 m aP (fun g => (hdom g).1) (fun g => (hdom g).2.2.1)
  let mM := dominatedL2 m aM (fun g => (hdom g).2.1) (fun g => (hdom g).2.2.2)
  refine ⟨h1,h2,h3,h4,mP,mM,m,(fun _ => rfl),(fun _ => rfl),?_,hmn,hdom⟩
  apply lp.ext
  funext g
  change m g = (1/2:ℝ)*(aP g+aM g)
  rw [hm]
  ring

end EndpointL2Vectors



section FoundationWitnesses
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]


theorem primal_coordinate_density :
    (Submodule.span ℝ (Set.range (unitVector (V := V)))).topologicalClosure = ⊤ := by
  have _ := decidableEqV
  apply top_unique
  intro x hx
  have hsub : Set.range (fun u : Test V => (u : Primal V)) ⊆
      (Submodule.span ℝ (Set.range (unitVector (V := V)))) := by
    rintro _ ⟨u,rfl⟩
    change (u : Primal V) ∈ Submodule.span ℝ (Set.range (unitVector (V := V)))
    rw [test_as_sum u]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,rfl⟩)
  exact (closure_mono hsub) (UniformSpace.Completion.denseRange_coe x)



theorem coordinatePredual_complete : CompleteSpace (CoordinatePredual V) := by
  have _ := decidableEqV
  exact
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (coordinate (V := V))))).completeSpace_coe

@[simp] theorem primalHead_idempotent (H : Finset V) (x : Primal V) :
    primalHead H (primalHead H x) = primalHead H x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((primalHead H).continuous.comp (primalHead H).continuous)
      (primalHead H).continuous) ?_
  intro u
  rw [primalHead_test,primalHead_test]
  congr 1
  apply Finsupp.ext
  intro v
  change ((u.coeff.filter (· ∈ H)).filter (· ∈ H)) v = (u.coeff.filter (· ∈ H)) v
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

@[simp] theorem primalTail_idempotent (H : Finset V) (x : Primal V) :
    primalTail H (primalTail H x) = primalTail H x := by
  change (x-primalHead H x)-primalHead H (x-primalHead H x) = x-primalHead H x
  rw [map_sub,primalHead_idempotent,sub_self,sub_zero]

end FoundationWitnesses

section CanonicalDualIdentification
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def canonicalBidualEquiv (h : Reflexive E) : E ≃ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  LinearIsometryEquiv.ofSurjective (NormedSpace.inclusionInDoubleDualLi ℝ) h

@[simp] theorem canonicalBidualEquiv_apply (h : Reflexive E) (x : E) (f : StrongDual ℝ E) :
    canonicalBidualEquiv h x f = f x := rfl


def forestCanonicalDual : J ≃ₗᵢ[ℝ] StrongDual ℝ X := canonicalBidualEquiv forest_primal_reflexive

@[simp] theorem forestCanonicalDual_apply (u : J) (x : X) : forestCanonicalDual u x = x u := rfl

end CanonicalDualIdentification



theorem infinite_main_tail_internal (H : Finset InfiniteVertex) (hH : Ancestral List.IsPrefix H)
    (x y : BInfinite) (hx : x = predualHead hH x) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖predualTail hH y‖ ≤ 2*Real.sqrt (R^2-‖x‖^2) := by
  classical
  exact infinite_main_tail H hH x y (congrArg Subtype.val hx) R hR hp hm



theorem forest_radial_tail (H : Finset ForestVertex) (hH : Ancestral ForestAncestor H)
    (x y : X) (hx : x = head H x) (R : ℝ)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖tail H y‖ ≤ (Real.sqrt 2+Real.sqrt 6)*Real.sqrt (R*(R-‖x‖)) := by
  classical
  exact radial_tail_bound hH x y hx.symm R ((norm_nonneg _).trans hp) hp hm


theorem infinite_original_coefficient_average (H : Finset InfiniteVertex)
    (hH : Ancestral List.IsPrefix H) (x z : BInfinite)
    (hx : x = predualHead hH x) (hz : predualHead hH z = 0) :
    ‖x‖ ≤ ‖x+z‖ ∧ ‖x‖ ≤ ‖x-z‖ ∧
    ‖z‖ ≤ (Real.sqrt 2+Real.sqrt 6)*
      Real.sqrt (((‖x+z‖+‖x-z‖)/2)*((‖x+z‖+‖x-z‖)/2-‖x‖)) := by
  classical
  exact original_coefficient_average hH x.val z.val (congrArg Subtype.val hx).symm
    (congrArg Subtype.val hz)



namespace LevelForest
open scoped Classical



abbrev Index := {n : ℕ // 1 ≤ n}
abbrev Vertex := IndexedForest.Vertex (fun n : Index => n.val-1)
abbrev J := Primal Vertex
abbrev X := FullDual Vertex


def shiftOrderEmbedding : Vertex ↪o Levels.Vertex where
  toFun v := ⟨(v.val.1.val-1,v.val.2),v.property⟩
  inj' := by
    intro v w he
    have hi := congrArg (fun u : Levels.Vertex => u.val.1) he
    have hw := congrArg (fun u : Levels.Vertex => u.val.2) he
    have hv1 := v.val.1.property
    have hw1 := w.val.1.property
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change v.val.1.val-1 = w.val.1.val-1 at hi
      omega
    · exact hw
  map_rel_iff' := by
    intro v w
    change (v.val.1.val-1 = w.val.1.val-1 ∧ v.val.2.IsPrefix w.val.2) ↔
      (v.val.1 = w.val.1 ∧ v.val.2.IsPrefix w.val.2)
    constructor
    · rintro ⟨hi,hw⟩
      refine ⟨Subtype.ext ?_,hw⟩
      have hv1 := v.val.1.property
      have hw1 := w.val.1.property
      omega
    · rintro ⟨hi,hw⟩
      exact ⟨congrArg (fun n : Index => n.val-1) hi,hw⟩

theorem shiftOrderEmbedding_surjective : Function.Surjective shiftOrderEmbedding := by
  intro v
  let n : Index := ⟨v.val.1+1,by omega⟩
  let w : Vertex := ⟨(n,v.val.2),by simpa only [n,Nat.add_sub_cancel] using v.property⟩
  refine ⟨w,?_⟩
  apply Subtype.ext
  exact Prod.ext (Nat.add_sub_cancel _ _) rfl

def shiftEmbedding : SegmentEmbedding (V := Vertex) (W := Levels.Vertex) :=
  convexSegmentEmbedding shiftOrderEmbedding
    (fun {_ _ v} _ _ _ _ => shiftOrderEmbedding_surjective v)



def heightEquiv : J ≃ₗᵢ[ℝ] Levels.J :=
  shiftEmbedding.primalEquivOfSurjective shiftOrderEmbedding_surjective


def primalSplit : J ≃ₗᵢ[ℝ] RealSum2 SegmentLenses.J := heightEquiv.trans Levels.primalSplit


def dualSplit : X ≃ₗᵢ[ℝ] RealSum2 SegmentLenses.X :=
  (dualTransport heightEquiv).trans Levels.dualSplit

@[simp] theorem shift_component (v : Vertex) :
    (shiftOrderEmbedding v).val.1 = v.val.1.val-1 := rfl

@[simp] theorem shift_word (v : Vertex) :
    (shiftOrderEmbedding v).val.2 = v.val.2 := rfl

end LevelForest

namespace SingleTree


def IsLeaf {h : ℕ} (v : Vertex h) : Prop := ∀ w : Vertex h, v ≤ w → w = v

theorem leaf_iff_full_height {h : ℕ} (v : Vertex h) : IsLeaf v ↔ v.val.length = h := by
  constructor
  · intro hv
    apply le_antisymm v.property
    by_contra! hlt
    let w : Vertex h := ⟨v.val++[0],by simpa using Nat.succ_le_of_lt hlt⟩
    have hp : v ≤ w := by
      change v.val.IsPrefix (v.val++[0])
      exact List.prefix_append _ _
    have he := congrArg (fun w : Vertex h => w.val.length) (hv w hp)
    simp [w] at he

  · intro hv w hp
    apply Subtype.ext
    have hp' : v.val.IsPrefix w.val := hp
    have hw := w.property
    have he : v.val.length = w.val.length := by
      have hle := hp'.length_le
      omega
    exact (hp'.eq_of_length he).symm



theorem every_n_levels_leaf_steps {n : ℕ} (hn : 1 ≤ n) (v : Vertex (n-1))
    (hleaf : IsLeaf v) : extensionSteps v = n-1 ∧ extensionSteps v+1 = n := by
  have he := (leaf_iff_full_height v).mp hleaf
  change v.val.length = n-1 ∧ v.val.length+1 = n
  exact ⟨he,by rw [he]; exact Nat.sub_add_cancel hn⟩

end SingleTree



end SegmentLenses

end

end OAI
