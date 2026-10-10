import OAI.Probability.ClassicalON.PinnedBonds

namespace OAI

universe uA uC uD uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]
variable (A : V → Type uA) (label : V → K)

abbrev GroupedFamily := (k : K) → (v : {v // label v=k}) → A v.val

def groupedEquiv : GroupedFamily A label ≃ ((v : V) → A v) where
  toFun s v := s (label v) ⟨v,rfl⟩
  invFun s k v := s v.val
  left_inv s := by
    funext k v
    rcases v with ⟨v,h⟩
    subst k
    rfl
  right_inv _ := rfl

variable [∀ v,MeasurableSpace (A v)]

def groupedMeasurableEquiv : GroupedFamily A label ≃ᵐ ((v : V) → A v) where
  toEquiv := groupedEquiv A label
  measurable_toFun := Measurable.of_eval (fun v => (measurable_pi_apply (⟨v,rfl⟩ : {w // label w=label v})).comp (measurable_pi_apply (label v)))
  measurable_invFun := Measurable.of_eval (fun _ => Measurable.of_eval (fun v => measurable_pi_apply v.val))

theorem grouped_measurePreserving (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)] :
    MeasurePreserving (groupedMeasurableEquiv A label)
      (Measure.pi (fun k : K => Measure.pi (fun v : {v // label v=k} => μ v.val))) (Measure.pi μ) := by
  refine ⟨(groupedMeasurableEquiv A label).measurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (groupedMeasurableEquiv A label) ⁻¹' (Set.pi Set.univ s)=
      Set.pi Set.univ (fun k : K => Set.pi Set.univ (fun v : {v // label v=k} => s v.val)) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies]
    constructor
    · intro h k v
      have hv := h v.val
      rcases v with ⟨v,hv'⟩
      subst k
      exact hv
    · intro h v
      exact h (label v) ⟨v,rfl⟩
  rw [he,Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma (fun v : Σ k : K, {v // label v=k} => μ v.2.val (s v.2.val))]
  exact (Equiv.sigmaFiberEquiv label).prod_comp (fun v => μ v (s v))

theorem integral_grouped_product (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)]
    (f : (k : K) → ((v : {v // label v=k}) → A v.val) → ℝ) :
    (∫ s,(∏ k,f k (fun v => s v.val)) ∂Measure.pi μ)=
      ∏ k,∫ s,f k s ∂Measure.pi (fun v : {v // label v=k} => μ v.val) := by
  rw [← (grouped_measurePreserving A label μ).integral_comp']
  have he (s : GroupedFamily A label) :
      (∏ k,f k (fun v => groupedMeasurableEquiv A label s v.val))=∏ k,f k (s k) := by
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    funext v
    rcases v with ⟨v,h⟩
    subst k
    rfl
  simp_rw [he]
  exact integral_fintype_prod_eq_prod _

theorem sum_grouped_product {D : Type uD} [Fintype D] (elabel : D → K)
    {C : D → Type uC} [∀ e,Fintype (C e)]
    (f : (k : K) → ((e : {e // elabel e=k}) → C e.val) → ℝ) :
    (∑ η : (e : D) → C e,∏ k,f k (fun e => η e.val))=
      ∏ k,∑ η,f k η := by
  rw [← (groupedEquiv C elabel).sum_comp]
  have he (s : GroupedFamily C elabel) :
      (∏ k,f k (fun e => groupedEquiv C elabel s e.val))=∏ k,f k (s k) := by
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    funext e
    rcases e with ⟨e,h⟩
    subst k
    rfl
  simp_rw [he]
  exact (Fintype.prod_sum f).symm

end ClassicalON

end

end OAI
