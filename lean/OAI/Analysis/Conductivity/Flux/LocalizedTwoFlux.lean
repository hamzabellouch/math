import Mathlib
import OAI.Analysis.Conductivity.Flux.TwoFluxDivergence
import OAI.Analysis.Conductivity.Variational.LocalizedFirstPotential

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

theorem uniform_zero_const_mul {X I : Type*} {l : Filter I}
    {f : I → X → ℝ} (c : ℝ) (hf : TendstoUniformly f (fun _ => 0) l) :
    TendstoUniformly (fun i x => c * f i x) (fun _ => 0) l := by
  simpa [Function.comp_def] using
    (uniformContinuous_const_smul (X := ℝ) c).comp_tendstoUniformly hf

theorem uniform_zero_add {X I : Type*} {l : Filter I} {f g : I → X → ℝ}
    (hf : TendstoUniformly f (fun _ => 0) l)
    (hg : TendstoUniformly g (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x + g i x) (fun _ => 0) l := by
  have hh := hf.add hg
  change TendstoUniformly (fun i x => f i x + g i x) (fun _ => (0 : ℝ) + 0) l at hh
  simpa only [add_zero] using hh

theorem uniform_zero_sub {X I : Type*} {l : Filter I} {f g : I → X → ℝ}
    (hf : TendstoUniformly f (fun _ => 0) l)
    (hg : TendstoUniformly g (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x - g i x) (fun _ => 0) l := by
  have hh := hf.sub hg
  change TendstoUniformly (fun i x => f i x - g i x) (fun _ => (0 : ℝ) - 0) l at hh
  simpa only [sub_zero] using hh

def localizedTwoFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) : Fin 5 → SmoothScalar E :=
  α • airyFlux v (localizedSecondPotential χ L H₂ k) +
    transverseFlux v (p • localizedFirstPotential χ L H₁ k)
      (q • localizedFirstPotential χ L H₁ k)
      (r • localizedFirstPotential χ L H₁ k)

theorem twoFluxDivergence_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (F G : Fin 5 → SmoothScalar E) :
    twoFluxDivergence v (F + G) = twoFluxDivergence v F + twoFluxDivergence v G := by
  funext i
  fin_cases i <;> simp [twoFluxDivergence] <;> abel

theorem twoFluxDivergence_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (c : ℝ) (F : Fin 5 → SmoothScalar E) :
    twoFluxDivergence v (c • F) = c • twoFluxDivergence v F := by
  funext i
  fin_cases i <;> simp [twoFluxDivergence, smul_add]

theorem localizedTwoFlux_divergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) :
    twoFluxDivergence v (localizedTwoFlux v χ L H₁ H₂ α p q r k) = 0 := by
  rw [localizedTwoFlux, twoFluxDivergence_add, twoFluxDivergence_smul,
    airyFlux_divergence, transverseFlux_divergence, smul_zero, zero_add]

theorem localizedTwoFlux_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (h H₁ H₂ : SmoothScalar ℝ) (α p q r : ℝ)
    (hχ : HasCompactSupport χ.val)
    (h₁ : smoothDirection 1 H₁ = h) (h₂ : smoothDirection 1 H₂ = H₁)
    (hB₁ : ∃ C : ℝ, ∀ t, |H₁.val t| ≤ C)
    (hB₂ : ∃ C : ℝ, ∀ t, |H₂.val t| ≤ C) (i : Fin 5) :
    TendstoUniformly
      (fun k x => (localizedTwoFlux v χ L H₁ H₂ α p q r k i).val x -
        (α • airySymbol (fun j => L (v j)) +
          transverseSymbol (fun j => L (v j)) p q r) i *
            (χ.val x * h.val (k * L x))) (fun _ => 0) atTop := by
  have hfirst (j : Fin 3) :=
    localizedFirstPotential_error_tendsto (v j) χ L H₁ hχ hB₁
  simp only [h₁] at hfirst
  have hsecond (j l : Fin 3) :=
    localizedSecondPotential_error_tendsto (v j) (v l) χ L H₂ hχ hB₂
      (by simpa only [h₂] using hB₁)
  simp only [h₂, h₁] at hsecond
  fin_cases i
  · convert uniform_zero_add (uniform_zero_const_mul α (hsecond 1 1))
      (uniform_zero_const_mul p (hfirst 2)) using 1
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_add (uniform_zero_const_mul (-α) (hsecond 0 1))
      (uniform_zero_const_mul q (hfirst 2)) using 1
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_add (uniform_zero_const_mul α (hsecond 0 0))
      (uniform_zero_const_mul r (hfirst 2)) using 1
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_sub (uniform_zero_const_mul (-p) (hfirst 0))
      (uniform_zero_const_mul q (hfirst 1)) using 1
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul]
    ring
  · convert uniform_zero_sub (uniform_zero_const_mul (-q) (hfirst 0))
      (uniform_zero_const_mul r (hfirst 1)) using 1
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul]
    ring

end ScalarConductivity

end

end OAI
