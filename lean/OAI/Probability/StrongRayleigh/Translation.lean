import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma measurable_leftTranslate {Γ : Type u_1} {α : Type u_2} [Group Γ] [MeasurableSpace α]
    (g : Γ) : Measurable (leftTranslate g : (Γ → α) → (Γ → α)) :=
  Measurable.of_eval (fun h => measurable_pi_apply (g⁻¹ * h))

def translatedLaw {Γ : Type u_3} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (g : Γ) : ProbabilityMeasure (Γ → Bool) :=
  μ.map (leftTranslate g)

@[simp] lemma translatedLaw_toMeasure {Γ : Type u_4} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (g : Γ) :
    (translatedLaw μ g : Measure (Γ → Bool)) =
      Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) := rfl

lemma measurableSet_inclusion {I : Type u_5} (A : Finset I) :
    MeasurableSet {x : I → Bool | ∀ i ∈ A, x i = true} := by
  classical
  have heq : {x : I → Bool | ∀ i ∈ A, x i = true} =
      ⋂ i : A, {x : I → Bool | x i.1 = true} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (measurable_pi_apply i.1) measurable_const

lemma translatedLaw_isDeterminantal {Γ : Type u_6} [Group Γ]
    {μ : ProbabilityMeasure (Γ → Bool)} {K : Γ → Γ → ℂ}
    (hμ : IsDeterminantalLaw μ K) (hK : TranslationInvariantKernel K) (g : Γ) :
    IsDeterminantalLaw (translatedLaw μ g) K := by
  classical
  intro A
  let e : Γ ≃ Γ := Equiv.mulLeft g⁻¹
  let B : Finset Γ := A.map e.toEmbedding
  let eA : A ≃ B := Equiv.subtypeEquiv e (by
    intro a
    simp [B])
  have hpre : leftTranslate g ⁻¹' {x : Γ → Bool | ∀ i ∈ A, x i = true} =
      {x : Γ → Bool | ∀ i ∈ B, x i = true} := by
    ext x
    change (∀ i ∈ A, x (g⁻¹ * i) = true) ↔ ∀ i ∈ A.map e.toEmbedding, x i = true
    rw [Finset.forall_mem_map]
    rfl
  rw [translatedLaw_toMeasure, Measure.map_apply (measurable_leftTranslate g)
    (measurableSet_inclusion A), hpre, hμ B]
  have hmatrix : Matrix.submatrix (fun i j : B => K i.1 j.1) eA eA =
      (fun i j : A => K i.1 j.1) := by
    funext i j
    change K (g⁻¹ * i.1) (g⁻¹ * j.1) = K i.1 j.1
    exact hK g⁻¹ i.1 j.1
  rw [← Matrix.det_submatrix_equiv_self eA (fun i j : B => K i.1 j.1), hmatrix]

end Problem336AdditiveD139

end

end OAI
