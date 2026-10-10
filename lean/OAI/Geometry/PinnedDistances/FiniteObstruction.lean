import OAI.Geometry.PinnedDistances.MeasureLimits

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
namespace WeakPinned.Bounded
lemma no_finite_expanded (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hind : Q.map (fun q => (q.1,q.2.2))=μ.prod (Q.map (fun q => q.2.2)))
    (hac₁ : Q.map (fun q => (q.1,q.2.2.1))≪μ.prod μ)
    (hac₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪ν.prod ν)
    (hz : ∀ᵐ r ∂  R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂  R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) : False := by
  have hbd : ∀ᵐ q ∂  Q,q.2.1≠q.2.2.2 :=
    (ae_map_iff (μ:=Q) (f:=fun q => (q.2.1,q.2.2.2)) (p:=fun p : ℂ × ℂ => p.1≠p.2) (by fun_prop)
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mp (hac₂.ae_le (ae_distinct_pair ν))
  have hsupp : ∀ᵐ q ∂  Q,q.2.2.1∈μ.support := by
    have hs : ∀ᵐ p ∂  μ.prod μ,p.2∈μ.support := by
      rw [Measure.ae_prod_iff_ae_ae (μ.isClosed_support.measurableSet.preimage measurable_snd)]
      exact Eventually.of_forall (fun _ => μ.support_mem_ae)
    exact (ae_map_iff (μ:=Q) (f:=fun q => (q.1,q.2.2.1)) (p:=fun p : ℂ × ℂ => p.2∈μ.support) (by fun_prop)
      (μ.isClosed_support.measurableSet.preimage measurable_snd)).mp (hac₁.ae_le hs)
  exact no_energy_law μ ν Q hind hsupp
    (expanded_energy_eq μ ν Q R hm₁ hm₂ (expanded_kernel_eq μ ν Q R he hm₁ hbd hz hw))
end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma no_sphere_expanded (β₁ β₂ : ProbabilityMeasure Sphere)
    [NullSingletonClass (β₁ : Measure Sphere)] [NullSingletonClass (β₂ : Measure Sphere)]
    (Q : Measure (Quad Sphere)) (R : Measure (Expanded Sphere))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod ((β₁:Measure Sphere).prod β₁))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod ((β₂:Measure Sphere).prod β₂))
    (hind : Q.map (fun q => (q.1,q.2.2))=(β₁:Measure Sphere).prod (Q.map (fun q => q.2.2)))
    (hac₁ : Q.map (fun q => (q.1,q.2.2.1))≪(β₁:Measure Sphere).prod β₁)
    (hac₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪(β₂:Measure Sphere).prod β₂)
    (hz : ∀ᵐ r ∂ R.comap expandedCoe,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂ R.comap expandedCoe,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) : False := by
  let μ := finitePart β₁
  let ν := finitePart β₂
  have hμ : μ.map OnePoint.some=(β₁:Measure Sphere) := finitePart_map β₁ (measure_singleton _)
  have hν : ν.map OnePoint.some=(β₂:Measure Sphere) := finitePart_map β₂ (measure_singleton _)
  let : IsProbabilityMeasure μ := finitePart_probability β₁ (measure_singleton _)
  let : IsProbabilityMeasure ν := finitePart_probability β₂ (measure_singleton _)
  let : NullSingletonClass μ := finitePart_nonatomic β₁
  let : NullSingletonClass ν := finitePart_nonatomic β₂
  have hQfin : ∀ᵐ q ∂ Q,q∈range quadCoe := sphere_quad_finite μ ν Q
    (by simpa only [hμ] using hac₁) (by simpa only [hν] using hac₂)
  let Qc := Q.comap quadCoe
  let : IsProbabilityMeasure Qc := chart_probability _ quadCoe_open.measurableEmbedding Q hQfin
  have hQ : Qc.map quadCoe=Q := chart_map_comap _ quadCoe_open.measurableEmbedding Q hQfin
  have hRfin : ∀ᵐ r ∂ R,r∈range expandedCoe := sphere_expanded_finite μ ν Qc R
    (by simpa only [hQ,hμ] using hm₁) (by simpa only [hQ,hν] using hm₂)
  let Rc := R.comap expandedCoe
  let : IsProbabilityMeasure Rc := chart_probability _ expandedCoe_open.measurableEmbedding R hRfin
  have hR : Rc.map expandedCoe=R := chart_map_comap _ expandedCoe_open.measurableEmbedding R hRfin
  have hec : Rc.map Prod.fst=Qc := by
    apply map_transport expandedCoe quadCoe expandedCoe_open.measurableEmbedding.measurable
      quadCoe_open.measurableEmbedding Prod.fst Prod.fst measurable_fst measurable_fst Rc Qc rfl
    rw [hR,hQ,he]
  have hm₁c : Rc.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Qc.prod (μ.prod μ) := by
    apply map_transport expandedCoe (Prod.map quadCoe pairCoe)
      expandedCoe_open.measurableEmbedding.measurable
      (quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding)
      (fun r => (r.1,(r.2.1.1,r.2.2.1))) (fun r => (r.1,(r.2.1.1,r.2.2.1)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (μ.prod μ)) rfl
    rw [hR,hm₁,← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      measurableEmbedding_sphere_coe.measurable measurableEmbedding_sphere_coe.measurable,hQ,hμ]
  have hm₂c : Rc.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Qc.prod (ν.prod ν) := by
    apply map_transport expandedCoe (Prod.map quadCoe pairCoe)
      expandedCoe_open.measurableEmbedding.measurable
      (quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding)
      (fun r => (r.1,(r.2.1.2,r.2.2.2))) (fun r => (r.1,(r.2.1.2,r.2.2.2)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (ν.prod ν)) rfl
    rw [hR,hm₂,← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      measurableEmbedding_sphere_coe.measurable measurableEmbedding_sphere_coe.measurable,hQ,hν]
  have htarget : (Qc.map (fun q => q.2.2)).map pairCoe=Q.map (fun q => q.2.2) := by
    rw [Measure.map_map pairCoe_open.measurableEmbedding.measurable (by fun_prop)]
    change Qc.map ((fun q : Quad Sphere => q.2.2) ∘ quadCoe)=_
    rw [← Measure.map_map (by fun_prop) quadCoe_open.measurableEmbedding.measurable,hQ]
  have hindc : Qc.map (fun q => (q.1,q.2.2))=μ.prod (Qc.map (fun q => q.2.2)) := by
    apply map_transport quadCoe (Prod.map OnePoint.some pairCoe)
      quadCoe_open.measurableEmbedding.measurable
      (measurableEmbedding_sphere_coe.prodMap pairCoe_open.measurableEmbedding)
      (fun q => (q.1,q.2.2)) (fun q => (q.1,q.2.2))
      (by fun_prop) (by fun_prop) Qc (μ.prod (Qc.map (fun q => q.2.2))) rfl
    rw [hQ,hind,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      pairCoe_open.measurableEmbedding.measurable,hμ,htarget]
  have hac₁c : Qc.map (fun q => (q.1,q.2.2.1))≪μ.prod μ := by
    apply map_transport_ac quadCoe pairCoe quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding (fun q => (q.1,q.2.2.1)) (fun q => (q.1,q.2.2.1))
      (by fun_prop) (by fun_prop) Qc (μ.prod μ) rfl
    rw [hQ,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      measurableEmbedding_sphere_coe.measurable,hμ]
    exact hac₁
  have hac₂c : Qc.map (fun q => (q.2.1,q.2.2.2))≪ν.prod ν := by
    apply map_transport_ac quadCoe pairCoe quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding (fun q => (q.2.1,q.2.2.2)) (fun q => (q.2.1,q.2.2.2))
      (by fun_prop) (by fun_prop) Qc (ν.prod ν) rfl
    rw [hQ,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      measurableEmbedding_sphere_coe.measurable,hν]
    exact hac₂
  exact no_finite_expanded μ ν Qc Rc hec hm₁c hm₂c hindc hac₁c hac₂c hz hw

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
local instance : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u1} {I : Type u2} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

def zEquation : Set (Expanded ℂ) := {r | (r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}
def wEquation : Set (Expanded ℂ) := {r | (r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}

lemma zEquation_closed : IsClosed zEquation := isClosed_eq (by fun_prop) (by fun_prop)
lemma wEquation_closed : IsClosed wEquation := isClosed_eq (by fun_prop) (by fun_prop)

omit [Fintype I] in
lemma tripleWeight_mem {r : I × V × V × V}
    (hr : tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0) :
    r.2.1∈G.targets r.1 ∧ r.2.2.1∈G.targets r.1 ∧ r.2.2.2∈G.targets r.1 := by
  refine ⟨?_,?_,?_⟩
  all_goals
    by_contra h
    simp [tripleWeight,prob,h] at hr

lemma expanded_chart_zero (U₁ U₂ : V → ℂ) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty)
    (hrel : ∀ e y z,y∈G.targets e → z∈G.targets e →
      (U₁ y-U₁ (G.source e))*(U₂ y-U₂ (G.source e))=
      (U₁ z-U₁ (G.source e))*(U₂ z-U₂ (G.source e))) :
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' zEquationᶜ)=0 ∧
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' wEquationᶜ)=0 := by
  have hzero (s : Set (Expanded ℂ))
      (hs : ∀ r,tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0 →
        tripleValue G.source U₁ U₂ r∈s) :
      (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
        Measure (Expanded Sphere)) (expandedCoe '' sᶜ)=0 := by
    have hh : ∀ᵐ r ∂  finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
        (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere))),
        r∉expandedCoe '' sᶜ := by
      apply finiteLaw_ae
      intro r hr
      rintro ⟨q,hq,hqe⟩
      have he : q=tripleValue G.source U₁ U₂ r := expandedCoe_open.injective hqe
      subst q
      exact hq (hs r hr)
    change (finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
      (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)))) (expandedCoe '' sᶜ)=0
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hh
  constructor
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.1 r.2.1 hm.2.1 hm.1
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.2 r.2.1 hm.2.2 hm.1

end WeakPinned.Bounded

end
end

end OAI
