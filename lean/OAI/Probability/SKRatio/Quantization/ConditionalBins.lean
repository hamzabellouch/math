import Mathlib
import OAI.Probability.SKRatio.Quantization.BinTail
import OAI.Probability.SKRatio.Variational.ScalarCoherent

namespace OAI

noncomputable section
open scoped BigOperators Matrix ENNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable

lemma independent_finite_selection_bound
    {Ω A D : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → A} {X : Ω → D}
    (hX : Measurable X) (hRX : IndepFun R X μ)
    (E : D → Set A) (hE : ∀ d, MeasurableSet (E d))
    {B : ℝ} (hB : ∀ d, μ.real (R ⁻¹' E d) ≤ B) :
    μ.real {ω | R ω ∈ E (X ω)} ≤ B := by
  have hall : (⋃ d : D, X ⁻¹' {d}) = Set.univ := by
    ext ω
    simp
  have hdis : Pairwise (Function.onFun Disjoint (fun d : D => X ⁻¹' {d})) := by
    intro d e hde
    exact Set.disjoint_left.mpr (fun ω hd he => hde ((Set.mem_singleton_iff.mp hd).symm.trans
      (Set.mem_singleton_iff.mp he)))
  have hsum : (∑ d, μ.real (X ⁻¹' {d})) = 1 := by
    rw [←measureReal_iUnion_fintype hdis (fun d => (MeasurableSet.singleton d).preimage hX),hall]
    simp [Measure.real]
  have hb (d : D) : μ.real (R ⁻¹' E d ∩ X ⁻¹' {d}) ≤ B*μ.real (X ⁻¹' {d}) := by
    have hi := hRX.measure_inter_preimage_eq_mul (E d) {d} (hE d) (MeasurableSet.singleton d)
    change (μ _).toReal ≤ _
    rw [hi,ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_right (hB d) ENNReal.toReal_nonneg
  calc
    _ ≤ μ.real (⋃ d : D, R ⁻¹' E d ∩ X ⁻¹' {d}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      exact Set.mem_iUnion.mpr ⟨X ω,hω,rfl⟩
    _ ≤ ∑ d, μ.real (R ⁻¹' E d ∩ X ⁻¹' {d}) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ d, B*μ.real (X ⁻¹' {d}) := Finset.sum_le_sum (fun d _ => hb d)
    _ = B := by rw [←Finset.mul_sum,hsum,mul_one]

def residualFormBad {α : Type*} {n : ℕ} (β : ℝ) (h : α → ℝ)
    (σ : Fin n → α) (K C : ℝ) : Set ((Fin n × Fin n) → ℝ) :=
  {M | euclideanOpNorm (fun i j => M (i,j)) ≤ K ∧
    ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
      p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
        correctedForm β (fun i => h (σ i)) p}

lemma residualFormBad_measurable {α : Type*} {n : ℕ}
    (β : ℝ) (h : α → ℝ) (σ : Fin n → α) (K C : ℝ) :
    MeasurableSet (residualFormBad β h σ K C) := by
  have hc : Continuous (fun M : (Fin n × Fin n) → ℝ =>
      euclideanOpNorm (fun i j => M (i,j))) := by
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) :=
      IsBoundedSMul.continuousSMul
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      ContinuousLinearMap.continuousSMul
    exact continuous_norm.comp
      (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
        (by fun_prop))
  have ho : IsOpen {M : (Fin n × Fin n) → ℝ |
      ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
        p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
          correctedForm β (fun i => h (σ i)) p} := by
    have he : {M : (Fin n × Fin n) → ℝ | ∃ p : Fin n → ℝ, (∑ i, p i^2)=1 ∧ C <
        p ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p i))+
          correctedForm β (fun i => h (σ i)) p} =
        ⋃ p : {p : Fin n → ℝ // (∑ i, p i^2)=1}, {M | C <
        p.val ⬝ᵥ ((fun i j => M (i,j))*ᵥ (fun i => v (h (σ i))*p.val i))+
          correctedForm β (fun i => h (σ i)) p.val} := by
      ext M
      simp
    rw [he]
    apply isOpen_iUnion
    intro p
    apply isOpen_lt continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact (measurableSet_le hc.measurable measurable_const).inter ho.measurableSet

theorem random_binForm_tail {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {β K a C : ℝ} (hβ : 0<β) (hK : 0≤K) (ha : 0<a)
    (h : α → ℝ) (q : ℝ → α) (hq : Measurable q) :
    ∃ N : ℕ, ∀ {n : ℕ} (_hn : 0<n),
      (standardArrayLaw (Fin n × Fin n)).real {g |
        (∀ d, 2≤count (fun i => q (augmentedField β g i)) d) ∧
        (∀ z : Parameters α, finiteV β (binT (fun i => q (augmentedField β g i))) h z≤C) ∧
        g ∈ binFormBad β h (fun i => q (augmentedField β g i)) K (C+2*a)} ≤
      N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
  obtain ⟨N,hN⟩ := binForm_tail hβ hK ha h
  refine ⟨N,?_⟩
  intro n hn
  let μ := standardArrayLaw (Fin n × Fin n)
  let R := fun g : (Fin n × Fin n) → ℝ => fun p : Fin n × Fin n =>
    (fieldProjection n*(β • goe g)*fieldProjection n) p.1 p.2
  let X := fun g : (Fin n × Fin n) → ℝ => fun i => q (augmentedField β g i)
  let good := fun σ : Fin n → α => (∀ d, 2≤count σ d) ∧
    (∀ z : Parameters α, finiteV β (binT σ) h z≤C)
  let E := fun σ : Fin n → α => if good σ then residualFormBad β h σ K (C+2*a) else ∅
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    apply hq.comp
    unfold augmentedField augmented goe
    fun_prop
  have hi : IndepFun R X μ := by
    have ht := (field_residual_independent hn β).comp measurable_id
      (show Measurable (fun H : Fin n → ℝ => fun i => q (H i)) from
        Measurable.of_eval (fun i => hq.comp (measurable_pi_apply i)))
    exact ht
  have hE (σ : Fin n → α) : MeasurableSet (E σ) := by
    dsimp only [E]
    split_ifs
    · exact residualFormBad_measurable β h σ K (C+2*a)
    · exact MeasurableSet.empty
  have hb (σ : Fin n → α) : μ.real (R ⁻¹' E σ) ≤
      N*exp (-a^2*(n:ℝ)/(π^2*β^2)) := by
    dsimp only [E]
    split_ifs with hg
    · exact hN hn σ hg.1 C hg.2
    · simp only [Set.preimage_empty,measureReal_empty]
      positivity
  apply (measureReal_mono ?_ (measure_ne_top μ _)).trans
    (independent_finite_selection_bound hX hi E hE hb)
  intro g hg
  change R g ∈ E (X g)
  dsimp only [E]
  rw [ite_eq_left (show good (X g) from ⟨hg.1,hg.2.1⟩)]
  exact hg.2.2

end SKRatio.Bins

end

end OAI
