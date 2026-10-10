import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CentralQuotient01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open Topology
open scoped Pointwise
open Topology Set
open MeasureTheory Set Topology
namespace CentralFiberAverage
variable {K X Y : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [MulAction K X] [ContinuousSMul K X]

noncomputable def average (ν : Measure K) (f : C(X,ℝ)) (x : X) : ℝ :=
  ∫ k, f (k • x) ∂ν

variable {ν : Measure K}

omit [IsTopologicalGroup K] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_average [IsFiniteMeasure ν] (f : C(X,ℝ)) :
    Continuous (average ν f) := by
  change Continuous (fun x : X => ∫ k : K, f (k • x) ∂ν)
  have h : Continuous (Function.uncurry (fun x : X => fun k : K => f (k • x))) := by
    exact f.continuous.comp (continuous_snd.smul continuous_fst)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := ν) h isCompact_univ)

omit [CompactSpace K] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [ContinuousSMul K X] in
lemma average_smul [Measure.IsMulRightInvariant ν] (f : C(X,ℝ)) (k : K) (x : X) :
    average ν f (k • x) = average ν f x := by
  unfold average
  simp_rw [← mul_smul]
  exact integral_mul_right_eq_self (fun l : K => f (l • x)) k

omit [IsTopologicalGroup K] in
lemma integral_average [IsProbabilityMeasure ν] (μ : ProbabilityMeasure X)
    [SMulInvariantMeasure K X (μ : Measure X)] (f : C(X,ℝ)) :
    (∫ x, average ν f x ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X) := by
  have hc : Continuous (Function.uncurry (fun x : X => fun k : K => f (k • x))) :=
    f.continuous.comp (continuous_snd.smul continuous_fst)
  have hi : Integrable (Function.uncurry (fun x : X => fun k : K => f (k • x)))
      ((μ : Measure X).prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold average
  rw [integral_integral_swap hi]
  simp only [integral_smul_eq_self]
  simp

variable [TopologicalSpace Y] [T2Space Y]

 

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_average_descend (ν : Measure K) [IsProbabilityMeasure ν]
    [Measure.IsMulRightInvariant ν] (p : C(X,Y)) (hp : Function.Surjective p)
    (hfib : ∀ x z, p x = p z → ∃ k : K, k • x = z) (f : C(X,ℝ)) :
    ∃ F : C(Y,ℝ), ∀ x, F (p x) = average ν f x := by
  classical
  let s : Y → X := fun y => Classical.choose (hp y)
  have hs : ∀ y, p (s y) = y := fun y => Classical.choose_spec (hp y)
  let F : Y → ℝ := fun y => average ν f (s y)
  have he : F ∘ p = average ν f := by
    funext x
    obtain ⟨k,hk⟩ := hfib x (s (p x)) (hs (p x)).symm
    change average ν f (s (p x)) = average ν f x
    rw [← hk,average_smul]
  have hc : Continuous F :=
    (p.continuous.isClosedMap.isQuotientMap p.continuous hp).continuous_iff.mpr
      (he ▸ continuous_average f)
  exact ⟨⟨F,hc⟩,fun x => congrFun he x⟩

variable [MeasurableSpace Y] [BorelSpace Y] [HasOuterApproxClosed X]

 

theorem measure_eq_of_map_eq (ν : Measure K) [IsProbabilityMeasure ν]
    [Measure.IsMulRightInvariant ν] (p : C(X,Y)) (hp : Function.Surjective p)
    (hfib : ∀ x z, p x = p z → ∃ k : K, k • x = z)
    (μ₁ μ₂ : ProbabilityMeasure X)
    [SMulInvariantMeasure K X (μ₁ : Measure X)]
    [SMulInvariantMeasure K X (μ₂ : Measure X)]
    (he : Measure.map p (μ₁ : Measure X) = Measure.map p (μ₂ : Measure X)) :
    (μ₁ : Measure X) = (μ₂ : Measure X) := by
  have hfm : μ₁.toFiniteMeasure = μ₂.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    obtain ⟨F,hF⟩ := exists_average_descend ν p hp hfib f.toContinuousMap
    change (∫ x, f.toContinuousMap x ∂(μ₁ : Measure X)) =
      ∫ x, f.toContinuousMap x ∂(μ₂ : Measure X)
    rw [← integral_average (ν := ν) μ₁ f.toContinuousMap,
      ← integral_average (ν := ν) μ₂ f.toContinuousMap]
    simp_rw [← hF]
    rw [← integral_map p.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable,
      ← integral_map p.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable,he]
  exact congrArg (fun m : FiniteMeasure X => (m : Measure X)) hfm

 
theorem exists_right_probability : ∃ ν : Measure K, IsProbabilityMeasure ν ∧
    Measure.IsMulRightInvariant ν := by
  let U : TopologicalSpace.PositiveCompacts K := ⟨⟨univ,isCompact_univ⟩,by simp⟩
  let μ := Measure.haarMeasure U
  refine ⟨μ.inv,⟨?_⟩,inferInstance⟩
  rw [Measure.inv_apply]
  simp only [Set.inv_univ]
  exact Measure.haarMeasure_self

 

theorem ext_of_map_eq (p : C(X,Y)) (hp : Function.Surjective p)
    (hfib : ∀ x z, p x = p z → ∃ k : K, k • x = z)
    (μ₁ μ₂ : ProbabilityMeasure X)
    [SMulInvariantMeasure K X (μ₁ : Measure X)]
    [SMulInvariantMeasure K X (μ₂ : Measure X)]
    (he : Measure.map p (μ₁ : Measure X) = Measure.map p (μ₂ : Measure X)) :
    (μ₁ : Measure X) = (μ₂ : Measure X) := by
  obtain ⟨ν,hν,hνr⟩ := exists_right_probability (K := K)
  let := hν
  let := hνr
  exact measure_eq_of_map_eq ν p hp hfib μ₁ μ₂ he

end CentralFiberAverage

 

open MeasureTheory Topology Set
namespace RationalNilmanifoldMeasure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] in
lemma normal_of_central (N : Subgroup G) (hN : N ≤ Subgroup.center G) : N.Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_center_iff.mp (hN hn) g,mul_assoc,mul_inv_cancel,mul_one]
  exact hn

variable (N Γ : Subgroup G) [N.Normal]

 

theorem measure_eq_of_central_map_eq
    (hN : N ≤ Subgroup.center G)
    (hG : CompactGroupProducts.HasCompactReps ⊤ Γ)
    (hRN : CompactGroupProducts.HasCompactReps N Γ)
    (hΓ : IsDiscrete (Γ : Set G))
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    [MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))]
    [BorelSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))]
    (μ₁ μ₂ : ProbabilityMeasure (G ⧸ Γ))
    [SMulInvariantMeasure G (G ⧸ Γ) (μ₁ : Measure (G ⧸ Γ))]
    [SMulInvariantMeasure G (G ⧸ Γ) (μ₂ : Measure (G ⧸ Γ))]
    (he : Measure.map (RationalQuotientFunctions.quotientMap N Γ) (μ₁ : Measure (G ⧸ Γ)) =
      Measure.map (RationalQuotientFunctions.quotientMap N Γ) (μ₂ : Measure (G ⧸ Γ))) :
    (μ₁ : Measure (G ⧸ Γ)) = (μ₂ : Measure (G ⧸ Γ)) := by
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  let : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  let : IsClosed (N : Set G) := hRN.isClosed hΓ
  let : CompactSpace (G ⧸ Γ) := hG.quotient_compactSpace
  let : (Γ.comap N.subtype).Normal := CentralQuotientAction.central_kernel_normal N Γ hN
  let := CentralQuotientAction.action N Γ hN
  let := CentralQuotientAction.continuous_action N Γ hN
  let := CentralQuotientAction.compact_central_quotient N Γ hRN
  let : MeasurableSpace (N ⧸ Γ.comap N.subtype) := borel _
  let : BorelSpace (N ⧸ Γ.comap N.subtype) := ⟨rfl⟩
  let := CentralQuotientAction.invariant_central_action N Γ hN (μ₁ : Measure (G ⧸ Γ))
  let := CentralQuotientAction.invariant_central_action N Γ hN (μ₂ : Measure (G ⧸ Γ))
  let := hRN.discrete_map hΓ
  let : IsClosed (Γ.map (QuotientGroup.mk' N) : Set (G ⧸ N)) :=
    Subgroup.isClosed_of_discreteTopology
  exact CentralFiberAverage.ext_of_map_eq
    ⟨RationalQuotientFunctions.quotientMap N Γ,
      RationalQuotientFunctions.continuous_quotientMap N Γ⟩
    (RationalQuotientFunctions.quotientMap_surjective N Γ)
    (CentralQuotientAction.quotientMap_fibers N Γ hN) μ₁ μ₂ he

end RationalNilmanifoldMeasure

namespace CompactGroupProducts
open Set
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]

lemma HasCompactReps.map {H Γ : Subgroup G} (h : HasCompactReps H Γ)
    (φ : G →* K) (hφ : Continuous φ) : HasCompactReps (H.map φ) (Γ.map φ) := by
  obtain ⟨C,hC,hCH,hr⟩ := h
  refine ⟨φ '' C,hC.image hφ,?_,?_⟩
  · rintro y ⟨c,hc,rfl⟩
    exact ⟨c,hCH hc,rfl⟩
  · rintro y ⟨g,hg,rfl⟩
    obtain ⟨c,hc,hcg⟩ := hr g hg
    exact ⟨φ c,⟨c,hc,rfl⟩,⟨c⁻¹*g,hcg,by simp⟩⟩
end CompactGroupProducts

namespace RationalNilmanifoldMeasure
open scoped commutatorElement
universe u

 

theorem invariant_unique_of_series (n : ℕ)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G]
    (Γ : Subgroup G) (H : ℕ → Subgroup G)
    (h0 : H 0 = ⊤) (hn : H n = ⊥)
    (hc : ∀ i (g x : G), x ∈ H i → ⁅g,x⁆ ∈ H (i+1))
    (hr : ∀ i, CompactGroupProducts.HasCompactReps (H i) Γ)
    (hΓ : IsDiscrete (Γ : Set G))
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    (μ₁ μ₂ : ProbabilityMeasure (G ⧸ Γ))
    [SMulInvariantMeasure G (G ⧸ Γ) (μ₁ : Measure (G ⧸ Γ))]
    [SMulInvariantMeasure G (G ⧸ Γ) (μ₂ : Measure (G ⧸ Γ))] :
    (μ₁ : Measure (G ⧸ Γ)) = (μ₂ : Measure (G ⧸ Γ)) := by
  induction n generalizing G with
  | zero =>
    have ht : (⊤ : Subgroup G) = ⊥ := h0.symm.trans hn
    have hone : ∀ g : G, g = 1 := fun g =>
      Subgroup.mem_bot.mp (ht ▸ Subgroup.mem_top g)
    let : Subsingleton G := ⟨fun a b => (hone a).trans (hone b).symm⟩
    let : Subsingleton (G ⧸ Γ) := inferInstance
    apply Measure.ext
    intro s hs
    rcases Set.eq_empty_or_nonempty s with he | ⟨x,hx⟩
    · rw [he]
      simp
    · have he : s = Set.univ := Set.eq_univ_of_forall fun y =>
        (Subsingleton.elim x y) ▸ hx
      rw [he]
      simp
  | succ n ih =>
    let N := H n
    have hN : N ≤ Subgroup.center G := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      apply commutatorElement_eq_one_iff_mul_comm.mp
      exact Subgroup.mem_bot.mp (hn ▸ hc n g x hx)
    let : N.Normal := normal_of_central N hN
    have hRN : CompactGroupProducts.HasCompactReps N Γ := hr n
    have hG : CompactGroupProducts.HasCompactReps ⊤ Γ := by simpa only [h0] using hr 0
    let : IsClosed (N : Set G) := hRN.isClosed hΓ
    let φ : G →* G ⧸ N := QuotientGroup.mk' N
    let Γ' := Γ.map φ
    let H' : ℕ → Subgroup (G ⧸ N) := fun i => (H i).map φ
    have h0' : H' 0 = ⊤ := by
      dsimp [H']
      rw [h0,Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective N)]
    have hn' : H' n = ⊥ := by
      apply le_antisymm _ bot_le
      rintro y ⟨x,hx,rfl⟩
      exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)
    have hc' : ∀ i (g x : G ⧸ N), x ∈ H' i → ⁅g,x⁆ ∈ H' (i+1) := by
      intro i g x hx
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N g
      obtain ⟨b,hb,rfl⟩ := hx
      exact ⟨⁅a,b⁆,hc i a b hb,map_commutatorElement φ a b⟩
    have hr' : ∀ i, CompactGroupProducts.HasCompactReps (H' i) Γ' :=
      fun i => (hr i).map φ QuotientGroup.continuous_mk
    let : DiscreteTopology Γ' := hRN.discrete_map hΓ
    have hΓ' : IsDiscrete (Γ' : Set (G ⧸ N)) := isDiscrete_iff_discreteTopology.mpr inferInstance
    let : MeasurableSpace ((G ⧸ N) ⧸ Γ') := borel _
    let : BorelSpace ((G ⧸ N) ⧸ Γ') := ⟨rfl⟩
    let p := RationalQuotientFunctions.quotientMap N Γ
    let ν₁ : ProbabilityMeasure ((G ⧸ N) ⧸ Γ') := μ₁.map p
    let ν₂ : ProbabilityMeasure ((G ⧸ N) ⧸ Γ') := μ₂.map p
    let : SMulInvariantMeasure (G ⧸ N) _ (ν₁ : Measure ((G ⧸ N) ⧸ Γ')) :=
      CentralQuotientAction.invariant_quotientMap N Γ (μ₁ : Measure (G ⧸ Γ))
    let : SMulInvariantMeasure (G ⧸ N) _ (ν₂ : Measure ((G ⧸ N) ⧸ Γ')) :=
      CentralQuotientAction.invariant_quotientMap N Γ (μ₂ : Measure (G ⧸ Γ))
    have he := ih Γ' H' h0' hn' hc' hr' hΓ' ν₁ ν₂
    exact measure_eq_of_central_map_eq N Γ hN hG hRN hΓ μ₁ μ₂ he
end RationalNilmanifoldMeasure

end
end
end
end

end OAI
