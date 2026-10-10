import OAI.Analysis.KadisonKastler.CenteredTestCommutatorWitness

namespace OAI

/-! # The quantitative Haagerup premise from constructed modular data

The uniform constant is six. This is the sufficient condition appearing
in AHHM, arXiv:1804.05706v2, Theorem 7.2, specialized to a fixed faithful
cyclic vector. The implication to scalar bicentralizers is not assumed here.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

def HaagerupCommutatorWitnesses (d : ModularConjugationData M Ω) : Prop :=
  ∀ a : Algebra M, a.val Ω=d.rightAction (star a) Ω →
    productVectorState Ω a.val=0 → ‖a.val Ω‖=1 →
    ∀ δ : ℝ, 0 < δ → ∃ b : Algebra M,
      ‖b.val Ω‖+‖(b*a).val Ω‖ < 6*‖(a*b-b*a).val Ω‖ ∧
      ‖b.val Ω-d.rightAction b Ω‖ < δ*‖(a*b-b*a).val Ω‖

theorem haagerupCommutatorWitnesses_of_modular_product
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (S : ModularSpectralResolution M Ω)
    (hcuts : ∀ r, S.upperCut r=modularUpperCut M J Ω r)
    (hunit : ‖Ω‖=1)
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (hprod : ∀ a ∈ M, ∀ b ∈ M.commutant,
      ψ (a*b)=productVectorState Ω a*productVectorState Ω b)
    (hremote : ∀ t : ℝ, 0 < t → t < 1 → ∃ v : ℕ → Algebra M,
      (∀ n, v n*star (v n)=1) ∧
      Tendsto (fun n => (v n).val Ω-(t : ℂ) • d.rightAction (v n) Ω) atTop (𝓝 0) ∧
      ∀ (b : Algebra M) (η : H),
        Tendsto (fun n => (v n*b*star (v n)).val η) atTop (𝓝 (b.val η))) :
    HaagerupCommutatorWitnesses d := by
  intro a ha hzero hnorm δ hδ
  apply centeredTest_commutator_witness d a ha _ hδ
  intro ε hε
  apply centeredTest_approximate_central_vectors J hsep hcyc d hd S hcuts ψ hψ hinv hremote a _ hε
  rw [modularCenteredTest_product_value d hunit ψ hprod a hzero hnorm]
  norm_num

end

end KadisonKastler

end OAI
