import OAI.Combinatorics.CompleteCrossing.AlgebraDefs
import OAI.Combinatorics.CompleteCrossing.CycleSpace
import OAI.Combinatorics.CompleteCrossing.Plane

namespace OAI

/-! Geometric crossing tensors, local orders, supports, and bilinear chain pairings. -/

section

/-! Algebraic consequences of the actual signed-intersection definition. -/
noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170
variable {V E : Type} {G : Graph V E}

theorem interiorIntersection_swap (N : NormalizedDrawing G) (e f : E) :
    interiorIntersection N f e = -interiorIntersection N e f := by
  by_cases h : e = f
  · subst f
    simp [interiorIntersection]
  · simp only [interiorIntersection, h, Ne.symm h, ite_false]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact segmentIntersection_swap _ _ _ _

theorem spokeComparison_swap {N : NormalizedDrawing G} (O : SpokeOrders N)
    (v : V) (e f : E) : spokeComparison O v f e = -spokeComparison O v e f := by
  by_cases he : G.src e = v ∨ G.dst e = v
  · by_cases hf : G.src f = v ∨ G.dst f = v
    · let : LinearOrder (G.IncidentEdge v) := O.order v
      rcases lt_trichotomy (⟨e,he⟩ : G.IncidentEdge v) ⟨f,hf⟩ with h | h | h
      · simp [spokeComparison, he, hf, h, not_lt.mpr h.le]
      · simp [spokeComparison, he, hf, h]
      · simp [spokeComparison, he, hf, h, not_lt.mpr h.le]
    · simp [spokeComparison, he, hf]
  · simp [spokeComparison, he]

variable [Fintype V]

theorem cycle_intersection_skew {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)
    (N : NormalizedDrawing G) (O : SpokeOrders N) (e f : E) :
    cycleIntersection O f e = -cycleIntersection O e f := by
  have hs : (∑ v, endpointSign G v f * endpointSign G v e * spokeComparison O v f e) =
      -(∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [spokeComparison_swap]
    ring
  unfold cycleIntersection
  rw [interiorIntersection_swap, hs]
  ring

variable [Fintype E]

theorem edgePairing_neg_left (J : E → E → ℝ) (z z' : E → ℝ) :
    edgePairing J (-z) z' = -edgePairing J z z' := by
  simp [edgePairing, Finset.sum_neg_distrib]

theorem edgePairing_neg_right (J : E → E → ℝ) (z z' : E → ℝ) :
    edgePairing J z (-z') = -edgePairing J z z' := by
  simp [edgePairing, Finset.sum_neg_distrib]

theorem edgePairing_swap (J : E → E → ℝ) (hJ : ∀ e f, J f e = -J e f)
    (z z' : E → ℝ) : edgePairing J z' z = -edgePairing J z z' := by
  unfold edgePairing
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro f _
  rw [hJ]
  ring

theorem completeEdgeVector_self {n : ℕ} (i : Fin n) : completeEdgeVector i i = 0 := by
  funext e
  have h : ¬(e.val.1 = i ∧ e.val.2 = i) := by
    rintro ⟨h1,h2⟩
    exact (ne_of_lt e.property) (h1.trans h2.symm)
  simp [completeEdgeVector, h]

theorem completeEdgeVector_reverse {n : ℕ} (i p : Fin n) :
    completeEdgeVector p i = -completeEdgeVector i p := by
  funext e
  by_cases h : e.val.1 = i ∧ e.val.2 = p
  · have hn : ¬(e.val.1 = p ∧ e.val.2 = i) := by
      rintro ⟨h1,h2⟩
      exact (ne_of_lt e.property) (h.1.trans h2.symm)
    simp only [completeEdgeVector, Pi.neg_apply, ite_eq_left h, ite_eq_right hn]
  · by_cases hr : e.val.1 = p ∧ e.val.2 = i
    · simp only [completeEdgeVector, Pi.neg_apply, ite_eq_right h, ite_eq_left hr, neg_neg]
    · simp only [completeEdgeVector, Pi.neg_apply, ite_eq_right h, ite_eq_right hr, neg_zero]

theorem raw_cycle_symmetries {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    (∀ i k q, rawCycleIntersection O i i k q = 0) ∧
    (∀ i p k, rawCycleIntersection O i p k k = 0) ∧
    (∀ i p k q, rawCycleIntersection O p i k q = -rawCycleIntersection O i p k q) ∧
    (∀ i p k q, rawCycleIntersection O i p q k = -rawCycleIntersection O i p k q) ∧
    (∀ i p k q, rawCycleIntersection O k q i p = -rawCycleIntersection O i p k q) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i k q
    simp [rawCycleIntersection, completeEdgeVector_self, edgePairing]
  · intro i p k
    simp [rawCycleIntersection, completeEdgeVector_self, edgePairing]
  · intro i p k q
    unfold rawCycleIntersection
    rw [completeEdgeVector_reverse i p, edgePairing_neg_left]
  · intro i p k q
    unfold rawCycleIntersection
    rw [completeEdgeVector_reverse k q, edgePairing_neg_right]
  · intro i p k q
    exact edgePairing_swap _ (cycle_intersection_skew _ N O) _ _

end Paper170

end
end

section

/-! Every nonzero independent-edge coefficient is witnessed by an actual crossing point. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

theorem completeEdgeVector_endpoints {n : ℕ} (e : CompleteEdge n) :
    completeEdgeVector e.val.1 e.val.2 = Pi.single e 1 := by
  funext f
  by_cases h : f = e
  · subst f
    simp only [completeEdgeVector, and_self, ite_true, Pi.single_eq_same]
  · have hne : ¬(f.val.1 = e.val.1 ∧ f.val.2 = e.val.2) := by
      rintro ⟨h1,h2⟩
      exact h (Subtype.ext (Prod.ext h1 h2))
    have hrev : ¬(f.val.1 = e.val.2 ∧ f.val.2 = e.val.1) := by
      rintro ⟨h1,h2⟩
      have hf := f.property
      rw [h1,h2] at hf
      exact lt_asymm e.property hf
    simp only [completeEdgeVector, ite_eq_right hne, ite_eq_right hrev, Pi.single_eq_of_ne h]

theorem rawCycleIntersection_endpoints {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (e f : CompleteEdge n) :
    rawCycleIntersection O e.val.1 e.val.2 f.val.1 f.val.2 = cycleIntersection O e f := by
  rw [rawCycleIntersection, completeEdgeVector_endpoints, completeEdgeVector_endpoints]
  simp [edgePairing, Pi.single_apply, ite_mul, mul_ite]

theorem independent_cycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (e f : CompleteEdge n)
    (h11 : e.val.1 ≠ f.val.1) (h12 : e.val.1 ≠ f.val.2)
    (h21 : e.val.2 ≠ f.val.1) (h22 : e.val.2 ≠ f.val.2) :
    cycleIntersection O e f = interiorIntersection N e f := by
  have hs : (∑ v, endpointSign (completeGraph n) v e *
      endpointSign (completeGraph n) v f * spokeComparison O v e f) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases he1 : e.val.1 = v
    · have hf1 : f.val.1 ≠ v := fun h => h11 (he1.trans h.symm)
      have hf2 : f.val.2 ≠ v := fun h => h12 (he1.trans h.symm)
      simp [endpointSign, completeGraph, hf1, hf2]
    · by_cases he2 : e.val.2 = v
      · have hf1 : f.val.1 ≠ v := fun h => h21 (he2.trans h.symm)
        have hf2 : f.val.2 ≠ v := fun h => h22 (he2.trans h.symm)
        simp [endpointSign, completeGraph, hf1, hf2]
      · simp [endpointSign, completeGraph, he1, he2]
  simp [cycleIntersection, hs]

theorem interiorIntersection_ne_zero_crossing {V E : Type} {G : Graph V E}
    (N : NormalizedDrawing G) (e f : E) (h : interiorIntersection N e f ≠ 0) :
    (Paper170Geometry.pairCrossings N.toAdmissibleDrawing e f).Nonempty := by
  have hef : e ≠ f := by
    intro he
    subst f
    exact h (by simp [interiorIntersection])
  rw [interiorIntersection, ite_eq_right hef] at h
  obtain ⟨i,hi,hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j,hj,hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi'
  have hc : ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      segmentPoint ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i+1)) s =
        segmentPoint ((N.polygonal f).vertices j) ((N.polygonal f).vertices (j+1)) t := by
    by_contra hn
    exact hij (by unfold segmentIntersection; rw [ite_eq_right hn])
  obtain ⟨s,hs,t,ht,hst⟩ := hc
  let x := segmentPoint ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i+1)) s
  have he : x ∈ edgeInterior N.toContinuousDrawing e :=
    (N.polygonal e).segment_mem_interior N.toContinuousDrawing e ⟨i,Finset.mem_range.mp hi⟩ s hs
  have hf : x ∈ edgeInterior N.toContinuousDrawing f := by
    rw [show x = _ from hst]
    exact (N.polygonal f).segment_mem_interior N.toContinuousDrawing f
      ⟨j,Finset.mem_range.mp hj⟩ t ht
  refine ⟨x, Finset.mem_filter.mpr ⟨?_,hef,he,hf⟩⟩
  exact N.crossings_finite.mem_toFinset.mpr ⟨e,f,hef,he,hf⟩

theorem signed_support_bound {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    (supportedPairs (rawCycleIntersection O)).card ≤ 2 * crossingCount N.toAdmissibleDrawing := by
  let W := ↥(supportedPairs (rawCycleIntersection O))
  let e : W → CompleteEdge n := fun w => ⟨w.val.1,(Finset.mem_filter.mp w.property).2.1⟩
  let f : W → CompleteEdge n := fun w => ⟨w.val.2,(Finset.mem_filter.mp w.property).2.2.1⟩
  have hc (w : W) : (Paper170Geometry.pairCrossings N.toAdmissibleDrawing (e w) (f w)).Nonempty := by
    obtain ⟨_,_,_,h11,h12,h21,h22,hJ⟩ := Finset.mem_filter.mp w.property
    apply interiorIntersection_ne_zero_crossing
    have hr := rawCycleIntersection_endpoints O (e w) (f w)
    rw [independent_cycleIntersection O (e w) (f w) h11 h12 h21 h22] at hr
    exact fun hz => hJ (hr.trans hz)
  choose x hx using hc
  let φ : W → (Σ a : CompleteEdge n, Σ b : CompleteEdge n,
      ↥(Paper170Geometry.pairCrossings N.toAdmissibleDrawing a b)) :=
    fun w => ⟨e w,f w,⟨x w,hx w⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => (z.1.val,z.2.1.val)) hab
  have hcard := Fintype.card_le_of_injective φ hφ
  have hs := Paper170Geometry.sum_pairCrossings_card N.toAdmissibleDrawing
  simpa only [W, Fintype.card_coe, Fintype.card_sigma, hs] using hcard

end Paper170

end
end

section

/-! The local order in the tensor is the actual order of outward incident edges. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}

theorem Graph.common_endpoint_unique (G : Graph V E) (e f : E) (hef : e ≠ f)
    (i v : V) (hei : G.src e = i ∨ G.dst e = i) (hfi : G.src f = i ∨ G.dst f = i)
    (hev : G.src e = v ∨ G.dst e = v) (hfv : G.src f = v ∨ G.dst f = v) : v = i := by
  by_contra hvi
  apply hef
  apply G.simple e f
  rcases hei with hei | hei <;> rcases hfi with hfi | hfi <;>
    rcases hev with hev | hev <;> rcases hfv with hfv | hfv <;> simp_all

theorem endpointSign_eq_zero (G : Graph V E) (v : V) (e : E)
    (h : ¬(G.src e = v ∨ G.dst e = v)) : endpointSign G v e = 0 := by
  simp [endpointSign, (not_or.mp h).1, (not_or.mp h).2]

theorem endpointSign_sq (G : Graph V E) (v : V) (e : E)
    (h : G.src e = v ∨ G.dst e = v) : endpointSign G v e ^ 2 = 1 := by
  rcases h with h | h
  · simp [endpointSign, h]
  · by_cases hs : G.src e = v <;> simp [endpointSign, hs, h]

theorem adjacent_interiorIntersection_eq_zero (N : NormalizedDrawing G) (e f : E)
    (hef : e ≠ f) (i : V) (he : G.src e = i ∨ G.dst e = i)
    (hf : G.src f = i ∨ G.dst f = i) : interiorIntersection N e f = 0 := by
  have hadj : G.src e = G.src f ∨ G.src e = G.dst f ∨
      G.dst e = G.src f ∨ G.dst e = G.dst f := by
    rcases he with he | he <;> rcases hf with hf | hf <;> simp_all
  by_contra hn
  obtain ⟨x,hx⟩ := interiorIntersection_ne_zero_crossing N e f hn
  obtain ⟨_,_,hxe,hxf⟩ := Finset.mem_filter.mp hx
  exact Set.disjoint_left.mp (N.no_adjacent e f hef hadj) hxe hxf

theorem cycleIntersection_incident [Fintype V] (N : NormalizedDrawing G)
    (O : SpokeOrders N) (e f : E) (hef : e ≠ f) (i : V)
    (he : G.src e = i ∨ G.dst e = i) (hf : G.src f = i ∨ G.dst f = i) :
    cycleIntersection O e f = (1 / 2 : ℝ) *
      (endpointSign G i e * endpointSign G i f * spokeComparison O i e f) := by
  have hs : (∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f) =
      endpointSign G i e * endpointSign G i f * spokeComparison O i e f := by
    apply Finset.sum_eq_single i
    · intro v _ hvi
      by_cases hev : G.src e = v ∨ G.dst e = v
      · by_cases hfv : G.src f = v ∨ G.dst f = v
        · exact False.elim (hvi (G.common_endpoint_unique e f hef i v he hf hev hfv))
        · rw [endpointSign_eq_zero G v f hfv]
          ring
      · rw [endpointSign_eq_zero G v e hev]
        ring
    · simp
  simp only [cycleIntersection, hs, adjacent_interiorIntersection_eq_zero N e f hef i he hf,
    zero_add]

def completeIncidentEdge {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    (completeGraph n).IncidentEdge i :=
  if h : i < p.val then ⟨⟨(i,p.val),h⟩,Or.inl rfl⟩
  else ⟨⟨(p.val,i),lt_of_le_of_ne (le_of_not_gt h) p.property⟩,Or.inr rfl⟩

theorem completeIncidentEdge_neighbor {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    (if (completeIncidentEdge i p).val.val.1 = i then
      (completeIncidentEdge i p).val.val.2 else (completeIncidentEdge i p).val.val.1) = p.val := by
  by_cases h : i < p.val <;> simp [completeIncidentEdge, h, p.property]

theorem completeIncidentEdge_injective {n : ℕ} (i : Fin n) :
    Function.Injective (completeIncidentEdge i) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (fun e : (completeGraph n).IncidentEdge i =>
    if e.val.val.1 = i then e.val.val.2 else e.val.val.1) hpq
  simpa only [completeIncidentEdge_neighbor] using h

theorem completeEdgeVector_incident {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    completeEdgeVector i p.val =
      endpointSign (completeGraph n) i (completeIncidentEdge i p).val •
        Pi.single (completeIncidentEdge i p).val 1 := by
  by_cases h : i < p.val
  · simpa [completeIncidentEdge, h, endpointSign, completeGraph] using
      completeEdgeVector_endpoints (⟨(i,p.val),h⟩ : CompleteEdge n)
  · have hp : p.val < i := lt_of_le_of_ne (le_of_not_gt h) p.property
    have he := completeEdgeVector_reverse p.val i
    rw [show completeEdgeVector p.val i = Pi.single (⟨(p.val,i),hp⟩ : CompleteEdge n) 1 from
      completeEdgeVector_endpoints ⟨(p.val,i),hp⟩] at he
    simpa [completeIncidentEdge, h, endpointSign, completeGraph, p.property] using he

theorem edgePairing_smul_smul [Fintype E] (J : E → E → ℝ) (a b : ℝ) (z z' : E → ℝ) :
    edgePairing J (a • z) (b • z') = (a*b) * edgePairing J z z' := by
  simp only [edgePairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem halfOrder_self {ι : Type} (order : LinearOrder ι) (p : ι) :
    halfOrder order p p = 0 := by
  let _ : LinearOrder ι := order
  simp [halfOrder]

theorem complete_local_orders {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    ∃ orders : ∀ i : Fin n, LinearOrder {j : Fin n // j ≠ i},
      ∀ i (p q : {j : Fin n // j ≠ i}),
        rawCycleIntersection O i p.val i q.val = halfOrder (orders i) p q := by
  let orders (i : Fin n) : LinearOrder {j : Fin n // j ≠ i} :=
    @LinearOrder.lift' _ _ (O.order i) (completeIncidentEdge i) (completeIncidentEdge_injective i)
  refine ⟨orders,?_⟩
  intro i p q
  by_cases hpq : p = q
  · subst q
    have hh := (raw_cycle_symmetries N O).2.2.2.2 i p.val i p.val
    have hz : rawCycleIntersection O i p.val i p.val = 0 := by linarith
    rw [hz]
    exact (halfOrder_self (orders i) p).symm
  · let e := completeIncidentEdge i p
    let f := completeIncidentEdge i q
    have hef : e.val ≠ f.val := fun h =>
      hpq (completeIncidentEdge_injective i (Subtype.ext h))
    rw [rawCycleIntersection, completeEdgeVector_incident, completeEdgeVector_incident,
      edgePairing_smul_smul]
    have hsingle : edgePairing (cycleIntersection O) (Pi.single e.val 1) (Pi.single f.val 1) =
        cycleIntersection O e.val f.val := by
      simp [edgePairing, Pi.single_apply, ite_mul, mul_ite]
    change (endpointSign (completeGraph n) i e.val * endpointSign (completeGraph n) i f.val) *
      edgePairing (cycleIntersection O) (Pi.single e.val 1) (Pi.single f.val 1) = _
    rw [hsingle, cycleIntersection_incident N O e.val f.val hef i e.property f.property]
    calc
      _ = (1/2 : ℝ) * (endpointSign (completeGraph n) i e.val ^ 2) *
          (endpointSign (completeGraph n) i f.val ^ 2) * spokeComparison O i e.val f.val := by ring
      _ = (1/2 : ℝ) * spokeComparison O i e.val f.val := by
        rw [endpointSign_sq _ _ _ e.property, endpointSign_sq _ _ _ f.property]
        ring
      _ = halfOrder (orders i) p q := by
        unfold spokeComparison
        rw [dite_eq_left e.property, dite_eq_left f.property]
        change (1/2 : ℝ) *
          (if @LT.lt _ (O.order i).toLT e f then 1
            else if @LT.lt _ (O.order i).toLT f e then -1 else 0) =
          (if @LT.lt _ (O.order i).toLT e f then 1/2
            else if @LT.lt _ (O.order i).toLT f e then -(1/2) else 0)
        split_ifs <;> ring

end Paper170

end
end

section

/-! The directed complete-graph chains and the chosen unoriented edge representatives agree. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E A : Type} [Fintype E] [Fintype A]

theorem boundary_sum (G : Graph V E) (w : A → E → ℝ) (v : V) :
    boundary G (fun e => ∑ a, w a e) v = ∑ a, boundary G (w a) v := by
  simp only [boundary,Finset.sum_mul]
  exact Finset.sum_comm

theorem boundary_mul (G : Graph V E) (c : ℝ) (w : E → ℝ) (v : V) :
    boundary G (fun e => c*w e) v = c*boundary G w v := by
  simp only [boundary,Finset.mul_sum,mul_assoc]

theorem edgePairing_sum_left (J : E → E → ℝ) (w : A → E → ℝ) (z : E → ℝ) :
    edgePairing J (fun e => ∑ a, w a e) z = ∑ a, edgePairing J (w a) z := by
  simp only [edgePairing,Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun f a => w a _ * z f * J _ f)]
  exact Finset.sum_comm

theorem edgePairing_sum_right (J : E → E → ℝ) (z : E → ℝ) (w : A → E → ℝ) :
    edgePairing J z (fun e => ∑ a, w a e) = ∑ a, edgePairing J z (w a) := by
  simp only [edgePairing,Finset.mul_sum,Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun f a => z _ * w a f * J _ f)]
  exact Finset.sum_comm

theorem edgePairing_mul_left (J : E → E → ℝ) (c : ℝ) (z w : E → ℝ) :
    edgePairing J (fun e => c*z e) w = c*edgePairing J z w := by
  simp only [edgePairing,Finset.mul_sum,mul_assoc]

theorem edgePairing_mul_right (J : E → E → ℝ) (c : ℝ) (z w : E → ℝ) :
    edgePairing J z (fun e => c*w e) = c*edgePairing J z w := by
  simp only [edgePairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

omit [Fintype E] [Fintype A] in
theorem boundary_completeEdgeVector {n : ℕ} (i p v : Fin n) :
    boundary (completeGraph n) (completeEdgeVector i p) v =
      (if p=v then 1 else 0) - (if i=v then 1 else 0) := by
  rcases lt_trichotomy i p with hip | rfl | hpi
  · let e : CompleteEdge n := ⟨(i,p),hip⟩
    have hs := completeEdgeVector_endpoints e
    change completeEdgeVector i p = Pi.single e 1 at hs
    rw [hs]
    simp [boundary,Pi.single_apply,completeGraph,e]
    exact congrArg₂ (fun x y : ℝ => x-y)
      (ite_cond_congr rfl) (ite_cond_congr rfl)
  · rw [completeEdgeVector_self]
    simp [boundary]
  · let e : CompleteEdge n := ⟨(p,i),hpi⟩
    have hs := completeEdgeVector_endpoints e
    change completeEdgeVector p i = Pi.single e 1 at hs
    rw [completeEdgeVector_reverse,hs]
    simp [boundary,Pi.single_apply,completeGraph,e]
    exact congrArg₂ (fun x y : ℝ => x-y)
      (ite_cond_congr rfl) (ite_cond_congr rfl)

def liftedChain {n : ℕ} (z : Fin n → Fin n → ℝ) : CompleteEdge n → ℝ :=
  fun e => ∑ i, ∑ p, z i p * completeEdgeVector i p e

omit [Fintype E] [Fintype A] in
theorem boundary_liftedChain {n : ℕ} (z : Fin n → Fin n → ℝ) (v : Fin n) :
    boundary (completeGraph n) (liftedChain z) v = chainBoundary z v := by
  unfold liftedChain
  rw [boundary_sum]
  simp_rw [boundary_sum,boundary_mul,boundary_completeEdgeVector,mul_sub]
  simp [chainBoundary,Finset.sum_sub_distrib]

omit [Fintype E] [Fintype A] in
theorem chainPairing_rawCycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (z z' : Fin n → Fin n → ℝ) :
    chainPairing (rawCycleIntersection O) z z' =
      edgePairing (cycleIntersection O) (liftedChain z) (liftedChain z') := by
  unfold liftedChain
  simp_rw [edgePairing_sum_left,edgePairing_sum_right,edgePairing_mul_left,edgePairing_mul_right]
  unfold chainPairing rawCycleIntersection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro q _
  ring

end Paper170

end
end

section

/-! A bilinear edge pairing is determined on real cycles by oriented simple cycles. -/
noncomputable section
open scoped BigOperators
namespace Paper170
variable {V E : Type} [Fintype E]

theorem edgePairing_add_left (J : E → E → ℝ) (x y z : E → ℝ) :
    edgePairing J (x+y) z = edgePairing J x z + edgePairing J y z := by
  simp [edgePairing,add_mul,Finset.sum_add_distrib]

theorem edgePairing_add_right (J : E → E → ℝ) (x y z : E → ℝ) :
    edgePairing J x (y+z) = edgePairing J x y + edgePairing J x z := by
  simp [edgePairing,mul_add,add_mul,Finset.sum_add_distrib]

theorem edgePairing_smul_left (J : E → E → ℝ) (c : ℝ) (x y : E → ℝ) :
    edgePairing J (c•x) y = c*edgePairing J x y :=
  edgePairing_mul_left J c x y

theorem edgePairing_smul_right (J : E → E → ℝ) (c : ℝ) (x y : E → ℝ) :
    edgePairing J x (c•y) = c*edgePairing J x y :=
  edgePairing_mul_right J c x y

theorem edgePairing_eq_zero_of_simple_cycles [Fintype V] (G : Graph V E)
    (J : E → E → ℝ)
    (hcycles : ∀ C C' : SimpleCycle G, edgePairing J C.edgeChain C'.edgeChain = 0)
    (z z' : E → ℝ) (hz : ∀ v, boundary G z v = 0) (hz' : ∀ v, boundary G z' v = 0) :
    edgePairing J z z' = 0 := by
  have hy := (simple_cycles_span G z').mp hz'
  have hright (C : SimpleCycle G) : edgePairing J C.edgeChain z' = 0 := by
    clear hz'
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨C',rfl⟩ := hy
      exact hcycles C C'
    | zero => simp [edgePairing]
    | add x y _ _ hx hy => rw [edgePairing_add_right,hx,hy,add_zero]
    | smul c x _ hx => rw [edgePairing_smul_right,hx,mul_zero]
  have hx := (simple_cycles_span G z).mp hz
  clear hz
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C,rfl⟩ := hx
    exact hright C
  | zero => simp [edgePairing]
  | add x y _ _ hx hy => rw [edgePairing_add_left,hx,hy,add_zero]
  | smul c x _ hx => rw [edgePairing_smul_left,hx,mul_zero]

end Paper170

end
end

section

/-! Traversal sums of a simple cycle agree with the frozen edge-chain bilinear pairing. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
open Paper170Geometry
variable {V E : Type} {G : Graph V E}

namespace SimpleCycle

theorem cyclicDart_coe (C : SimpleCycle G) (i : Fin C.length) : C.cyclicDart i = C.dart i := by
  exact congrArg C.dart (Fin.ext (Nat.mod_eq_of_lt i.isLt))

theorem edgeChain_eq_dart_sum (C : SimpleCycle G) :
    C.edgeChain = fun e => ∑ i, dartSign (C.dart i) * (Pi.single (C.edge i) (1 : ℝ) : E → ℝ) e := by
  funext e
  unfold edgeChain
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : C.edge i = e
  · subst e
    simp [dart_sign]
  · simp [h]

end SimpleCycle

variable [Fintype E]

theorem edgePairing_single_single (J : E → E → ℝ) (e f : E) (a b : ℝ) :
    edgePairing J (Pi.single e a) (Pi.single f b) = a*b*J e f := by
  simp [edgePairing,Pi.single_apply]

theorem edgePairing_simple_cycles (J : E → E → ℝ) (C C' : SimpleCycle G) :
    edgePairing J C.edgeChain C'.edgeChain =
      ∑ i, ∑ j, dartSign (C.dart i) * dartSign (C'.dart j) * J (C.edge i) (C'.edge j) := by
  rw [C.edgeChain_eq_dart_sum,C'.edgeChain_eq_dart_sum]
  simp_rw [edgePairing_sum_left,edgePairing_sum_right,edgePairing_mul_left,
    edgePairing_mul_right,edgePairing_single_single]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem edgePairing_simple_cycles_range (J : E → E → ℝ) (C C' : SimpleCycle G) :
    edgePairing J C.edgeChain C'.edgeChain =
      ∑ i ∈ Finset.range C.length, ∑ j ∈ Finset.range C'.length,
        dartSign (C.cyclicDart i) * dartSign (C'.cyclicDart j) *
          J (C.cyclicDart i).edge (C'.cyclicDart j).edge := by
  rw [edgePairing_simple_cycles]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [SimpleCycle.cyclicDart_coe,SimpleCycle.dart_edge]

end Paper170

end
end

end OAI
