import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Independence.Basic

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → α} {Y : Ω → β} {f : α × β → ℝ}

theorem condExp_independent_pair
    (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (hf : StronglyMeasurable f)
    (hfi : Integrable (fun ω => f (X ω, Y ω)) μ) :
    μ[fun ω => f (X ω, Y ω) | (inferInstance : MeasurableSpace α).comap X]
      =ᵐ[μ] fun ω => ∫ y, f (X ω, y) ∂(μ.map Y) := by
  have hmap := hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hfmap : Integrable f (μ.map fun ω => (X ω, Y ω)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (hX.aemeasurable.prodMk hY.aemeasurable)).mpr hfi
  have hfprod : Integrable f ((μ.map X).prod (μ.map Y)) := hmap ▸ hfmap
  have hg : StronglyMeasurable (fun x => ∫ y, f (x, y) ∂(μ.map Y)) :=
    hf.integral_prod_right'
  have hgi : Integrable (fun ω => ∫ y, f (X ω, y) ∂(μ.map Y)) μ :=
    (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mp
      hfprod.integral_prod_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hfi
    (fun s _ _ => hgi.integrableOn) ?_
    (hg.comp_measurable (comap_measurable X)).aestronglyMeasurable).symm
  rintro s ⟨t, ht, rfl⟩ _
  rw [← setIntegral_map ht hg.aestronglyMeasurable hX.aemeasurable]
  have hp := setIntegral_prod f (s := t) (t := Set.univ) hfprod.integrableOn
  simp only [Measure.restrict_univ] at hp
  rw [← hp, ← hmap]
  rw [setIntegral_map (ht.prod MeasurableSet.univ) hf.aestronglyMeasurable
    (hX.aemeasurable.prodMk hY.aemeasurable)]
  simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]

theorem condExp_independent_pair_ae
    (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ)
    (hfi : Integrable f (μ.map fun ω => (X ω, Y ω))) :
    μ[fun ω => f (X ω, Y ω) | (inferInstance : MeasurableSpace α).comap X]
      =ᵐ[μ] fun ω => ∫ y, f (X ω, y) ∂(μ.map Y) := by
  let f' := hfi.aestronglyMeasurable.mk f
  have hf' : StronglyMeasurable f' := hfi.aestronglyMeasurable.stronglyMeasurable_mk
  have heq : f =ᵐ[μ.map fun ω => (X ω, Y ω)] f' :=
    hfi.aestronglyMeasurable.ae_eq_mk
  have heqcomp : (fun ω => f (X ω, Y ω)) =ᵐ[μ] (fun ω => f' (X ω, Y ω)) :=
    ae_of_ae_map (hX.aemeasurable.prodMk hY.aemeasurable) heq
  have hf'int : Integrable (fun ω => f' (X ω, Y ω)) μ :=
    (integrable_map_measure hf'.aestronglyMeasurable
      (hX.aemeasurable.prodMk hY.aemeasurable)).mp (hfi.congr heq)
  have hmap := hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have heqprod : f =ᵐ[(μ.map X).prod (μ.map Y)] f' := hmap ▸ heq
  have hint : (fun x => ∫ y, f (x, y) ∂(μ.map Y))
      =ᵐ[μ.map X] (fun x => ∫ y, f' (x, y) ∂(μ.map Y)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod heqprod] with x hx
    exact integral_congr_ae hx
  exact (condExp_congr_ae heqcomp).trans
    ((condExp_independent_pair hX hY hind hf' hf'int).trans
      (Filter.EventuallyEq.symm (ae_of_ae_map hX.aemeasurable hint)))

section FiniteBlocks

variable {ι : Type*} {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
  {ξ : ∀ i, Ω → A i}

theorem condExp_independent_blocks (S T : Finset ι) (hST : Disjoint S T)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : (∀ i : S, A i) × (∀ i : T, A i) → ℝ)
    (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F ((fun i : S => ξ i ω),
      (fun i : T => ξ i ω))) μ) :
    μ[fun ω => F ((fun i : S => ξ i ω), (fun i : T => ξ i ω)) |
      (inferInstance : MeasurableSpace (∀ i : S, A i)).comap
        (fun ω (i : S) => ξ i ω)] =ᵐ[μ]
      fun ω => ∫ y, F ((fun i : S => ξ i ω), y)
        ∂(μ.map (fun ω (i : T) => ξ i ω)) := by
  exact condExp_independent_pair
    (Measurable.of_eval (fun index : S => hξ index))
    (Measurable.of_eval (fun index : T => hξ index))
    (hind.indepFun_finset S T hST hξ) hF hFi

omit [IsProbabilityMeasure μ] in

theorem independent_predicate_blocks [Fintype ι]
    (p : ι → Prop) [DecidablePred p]
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    IndepFun (fun ω (i : {i // p i}) => ξ i ω)
      (fun ω (i : {i // ¬p i}) => ξ i ω) μ := by
  classical
  have hdisj : Disjoint (Finset.univ.filter p) (Finset.univ.filter (fun i => ¬p i)) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ h hp => hp h
  have hbase := hind.indepFun_finset (Finset.univ.filter p)
    (Finset.univ.filter (fun i => ¬p i)) hdisj hξ
  let left : (∀ i : Finset.univ.filter p, A i) → ∀ i : {i // p i}, A i :=
    fun x i => x ⟨i, by simp [i.property]⟩
  let right : (∀ i : Finset.univ.filter (fun i => ¬p i), A i) →
      ∀ i : {i // ¬p i}, A i :=
    fun x i => x ⟨i, by simp [i.property]⟩
  exact hbase.comp
    (Measurable.of_eval (f := left) (fun _ => measurable_pi_apply _))
    (Measurable.of_eval (f := right) (fun _ => measurable_pi_apply _))

theorem condExp_independent_family [Fintype ι]
    (p : ι → Prop) [DecidablePred p]
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : (∀ i, A i) → ℝ) (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (fun i => ξ i ω)) μ) :
    μ[fun ω => F (fun i => ξ i ω) |
      (inferInstance : MeasurableSpace (∀ i : {i // p i}, A i)).comap
        (fun ω (i : {i // p i}) => ξ i ω)] =ᵐ[μ]
      fun ω => ∫ y, F ((MeasurableEquiv.piEquivPiSubtypeProd A p).symm
        ((fun i : {i // p i} => ξ i ω), y))
        ∂(μ.map (fun ω (i : {i // ¬p i}) => ξ i ω)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd A p
  have hreconstruct (ω : Ω) :
      e.symm ((fun i : {i // p i} => ξ i ω),
        (fun i : {i // ¬p i} => ξ i ω)) = (fun i => ξ i ω) := by
    exact e.symm_apply_apply (fun i => ξ i ω)
  have hFi' : Integrable (fun ω => (F ∘ e.symm)
      ((fun i : {i // p i} => ξ i ω), (fun i : {i // ¬p i} => ξ i ω))) μ := by
    simpa only [Function.comp_apply, hreconstruct] using hFi
  have hrep := condExp_independent_pair
    (Measurable.of_eval (fun index : {i // p i} => hξ index))
    (Measurable.of_eval (fun index : {i // ¬p i} => hξ index))
    (independent_predicate_blocks p hξ hind)
    (hF.comp_measurable e.symm.measurable) hFi'
  simpa only [Function.comp_apply, hreconstruct] using hrep

end FiniteBlocks

end Balanced.IndependentTrials

end OAI
