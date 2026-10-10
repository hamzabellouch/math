import OAI.Analysis.KadisonKastler.DirectIntegralUnitary
import OAI.Analysis.KadisonKastler.MeasurableImplementers

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RepresentsOperatorField (μ : Measure X) (F : X → H →L[ℂ] H)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) : Prop :=
  ∀ f : Lp H 2 μ, T f =ᵐ[μ] fun t => F t (f t)

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

structure OperatorFieldDecomposition (μ : Measure X) (M : X → VonNeumannAlgebra H)
    (A : VonNeumannAlgebra (Lp H 2 μ)) : Prop where
  decompose : ∀ T ∈ A, ∃ F : X → H →L[ℂ] H,
    (∀ x, AEStronglyMeasurable (fun t => F t x) μ) ∧
    (∀ᵐ t ∂μ, ‖F t‖ ≤ ‖T‖) ∧ (∀ᵐ t ∂μ, F t ∈ M t) ∧ RepresentsOperatorField μ F T
  reconstruct : ∀ (F : X → H →L[ℂ] H) (C : ℝ), 0 ≤ C →
    (∀ x, AEStronglyMeasurable (fun t => F t x) μ) →
    (∀ᵐ t ∂μ, ‖F t‖ ≤ C) → (∀ᵐ t ∂μ, F t ∈ M t) →
    ∃ T ∈ A, RepresentsOperatorField μ F T

theorem operatorField_conjugation_inclusion (μ : Measure X)
    {M N : X → VonNeumannAlgebra H} {A B : VonNeumannAlgebra (Lp H 2 μ)}
    (hA : OperatorFieldDecomposition μ M A) (hB : OperatorFieldDecomposition μ N B)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (u : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hu : ∀ f : Lp H 2 μ, (u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (U t : H →L[ℂ] H) (f t))
    (hus : ∀ f : Lp H 2 μ, (star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f =ᵐ[μ]
      fun t => (star (U t) : H →L[ℂ] H) (f t))
    (hconj : ∀ᵐ t ∂μ, Conjugates (U t) (M t) (N t)) :
    ∀ T ∈ A, unitaryConj u T ∈ B := by
  intro T hT
  obtain ⟨F, hFm, hFn, hFM, hFT⟩ := hA.decompose T hT
  let G : X → H →L[ℂ] H := fun t => unitaryConj (U t) (F t)
  have hGm (x : H) : AEStronglyMeasurable (fun t => G t x) μ := by
    exact aestronglyMeasurable_field_apply (fun t => (U t : H →L[ℂ] H)) hU _
      (aestronglyMeasurable_field_apply F hFm _ (hUs x))
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖T‖ := by
    filter_upwards [hFn] with t ht
    simpa only [G, norm_unitaryConj] using ht
  have hGN : ∀ᵐ t ∂μ, G t ∈ N t := by
    filter_upwards [hFM, hconj] with t ht hc
    exact hc.subset ⟨F t, ht, rfl⟩
  obtain ⟨S, hS, hSG⟩ := hB.reconstruct G ‖T‖ (norm_nonneg _) hGm hGn hGN
  have hG : RepresentsOperatorField μ G (unitaryConj u T) := by
    intro f
    filter_upwards [hu (T ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f)),
      hFT ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f), hus f] with t huv htf husf
    change ((u : Lp H 2 μ →L[ℂ] Lp H 2 μ)
      (T ((star u : Lp H 2 μ →L[ℂ] Lp H 2 μ) f))) t = _
    rw [huv, htf, husf]
    rfl
  rw [hG.unique hSG]
  exact hS

theorem conjugates_regularUnitaryField (μ : Measure X)
    {M N : X → VonNeumannAlgebra H} {A B : VonNeumannAlgebra (Lp H 2 μ)}
    (hA : OperatorFieldDecomposition μ M A) (hB : OperatorFieldDecomposition μ N B)
    (U : X → unitary (H →L[ℂ] H))
    (hU : ∀ x, AEStronglyMeasurable (fun t => (U t : H →L[ℂ] H) x) μ)
    (hUs : ∀ x, AEStronglyMeasurable (fun t => (star (U t) : H →L[ℂ] H) x) μ)
    (hconj : ∀ᵐ t ∂μ, Conjugates (U t) (M t) (N t)) :
    Conjugates (regularUnitaryField μ U hU hUs) A B := by
  let u := regularUnitaryField μ U hU hUs
  have hu := regularUnitaryField_apply_ae μ U hU hUs
  have hus := regularUnitaryField_star_apply_ae μ U hU hUs
  have hforward := operatorField_conjugation_inclusion μ hA hB U hU hUs u hu hus hconj
  have hreverse : ∀ S ∈ B, unitaryConj (star u) S ∈ A :=
    operatorField_conjugation_inclusion μ hB hA (fun t => star (U t)) hUs
      (fun x => by simpa only [Unitary.coe_star, star_star] using hU x) (star u) hus
      (fun f => by simpa only [Unitary.coe_star, star_star] using hu f)
      (hconj.mono fun _ h => h.symm)
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hforward T hT
  · intro S hS
    refine ⟨unitaryConj (star u) S, hreverse S hS, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj (star u) S

end

end KadisonKastler

end OAI
