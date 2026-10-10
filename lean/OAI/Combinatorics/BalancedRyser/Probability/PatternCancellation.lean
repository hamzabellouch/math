import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.Pattern

variable {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : I → Type*} [∀ i, MeasurableSpace (E i)]
variable {ξ : (i : I) → Ω → E i}

theorem indepFun_of_disjoint_supports
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (S T : Finset I) (hST : Disjoint S T)
    (f : ((i : S) → E i) → ℝ) (g : ((i : T) → E i) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω => f (fun i => ξ i ω))
      (fun ω => g (fun i => ξ i ω)) μ := by
  exact (hξ.indepFun_finset S T hST hξm).comp hf hg

theorem integral_centered_mul_eq_zero [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXY : IndepFun X Y μ)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ ω, (X ω - ∫ w, X w ∂μ) * Y ω ∂μ) = 0 := by
  have hcenter : IndepFun (fun ω => X ω - ∫ w, X w ∂μ) Y μ :=
    hXY.comp (measurable_id.sub_const _) measurable_id
  rw [hcenter.integral_fun_mul_eq_mul_integral (hX.sub (integrable_const _)).aestronglyMeasurable hY.aestronglyMeasurable]
  simp [integral_sub hX (integrable_const _)]

theorem integral_prod_eq_zero_of_isolated [IsProbabilityMeasure μ]
    {A : Type*} [DecidableEq A] (s : Finset A) {a : A} (ha : a ∈ s)
    (X : A → Ω → ℝ)
    (hind : IndepFun (X a) (fun ω => ∏ b ∈ s.erase a, X b ω) μ)
    (hX : AEStronglyMeasurable (X a) μ)
    (hrest : AEStronglyMeasurable (fun ω => ∏ b ∈ s.erase a, X b ω) μ)
    (hmean : (∫ ω, X a ω ∂μ) = 0) :
    (∫ ω, ∏ b ∈ s, X b ω ∂μ) = 0 := by
  have hprod (ω : Ω) : (∏ b ∈ s, X b ω) =
      X a ω * ∏ b ∈ s.erase a, X b ω :=
    (Finset.mul_prod_erase s (fun b => X b ω) ha).symm
  simp_rw [hprod]
  rw [hind.integral_fun_mul_eq_mul_integral hX hrest, hmean, zero_mul]

theorem indepFun_pattern_prod
    {A : Type*} [DecidableEq A] [DecidableEq I]
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (C : A → Finset I)
    (F : (a : A) → ((i : C a) → E i) → ℝ)
    (hF : ∀ a, Measurable (F a))
    (s : Finset A) (a : A)
    (hdisj : ∀ b ∈ s, Disjoint (C a) (C b)) :
    IndepFun (fun ω => F a (fun i => ξ i ω))
      (fun ω => ∏ b ∈ s, F b (fun i => ξ i ω)) μ := by
  let U : Finset I := s.biUnion C
  let G : ((i : U) → E i) → ℝ := fun z =>
    ∏ b : s, F b (fun i => z ⟨i, Finset.mem_biUnion.mpr
      ⟨b, b.property, i.property⟩⟩)
  have hU : Disjoint (C a) U := by
    apply Finset.disjoint_left.mpr
    intro i hi hiU
    obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp hiU
    exact Finset.disjoint_left.mp (hdisj b hb) hi hib
  have hG : Measurable G := by
    apply Finset.measurable_fun_prod
    intro b _
    exact (hF b).comp (Measurable.of_eval (fun _ => measurable_pi_apply _))
  have hind := indepFun_of_disjoint_supports hξ hξm (C a) U hU (F a) G (hF a) hG
  have hGeq : (fun ω => G (fun i => ξ i ω)) =
      (fun ω => ∏ b ∈ s, F b (fun i => ξ i ω)) := by
    funext ω
    exact Finset.prod_coe_sort s (fun b => F b (fun i => ξ i ω))
  rw [hGeq] at hind
  exact hind

theorem integral_centered_pattern_prod_eq_zero [IsProbabilityMeasure μ]
    {A : Type*} [DecidableEq A] [DecidableEq I]
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (C : A → Finset I)
    (F : (a : A) → ((i : C a) → E i) → ℝ)
    (hF : ∀ a, Measurable (F a))
    (hFi : ∀ a, Integrable (fun ω => F a (fun i => ξ i ω)) μ)
    (s : Finset A) {a : A} (ha : a ∈ s)
    (hdisj : ∀ b ∈ s.erase a, Disjoint (C a) (C b)) :
    (∫ ω, ∏ b ∈ s,
      (F b (fun i => ξ i ω) - ∫ w, F b (fun i => ξ i w) ∂μ) ∂μ) = 0 := by
  let p : A → ℝ := fun b => ∫ w, F b (fun i => ξ i w) ∂μ
  let Fc : (b : A) → ((i : C b) → E i) → ℝ := fun b z => F b z - p b
  have hFc : ∀ b, Measurable (Fc b) := fun b => (hF b).sub_const (p b)
  have hXm (b : A) : Measurable (fun ω => Fc b (fun i => ξ i ω)) :=
    (hFc b).comp (Measurable.of_eval (fun coordinate => hξm coordinate))
  apply integral_prod_eq_zero_of_isolated s ha (fun b ω => Fc b (fun i => ξ i ω))
  · exact indepFun_pattern_prod hξ hξm C Fc hFc (s.erase a) a hdisj
  · exact (hXm a).aestronglyMeasurable
  · exact (Finset.measurable_fun_prod _ (fun b _ => hXm b)).aestronglyMeasurable
  · simp [Fc, p, integral_sub (hFi a) (integrable_const _)]

end Balanced.Pattern

end OAI
