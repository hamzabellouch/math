import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalForcingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInverseOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitFieldLimit

namespace OAI

/-! Actual outgoing solutions along the singular profile limit. The finite
initial indices are immaterial; the same weighted inverse supplies the
solutions and their convergence. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_canonical_circular_solution_limit
    (ν m νp νm : ℕ → ℂ) (ν₀ m₀ νp₀ νm₀ η : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hn : Tendsto νm atTop (𝓝 νm₀))
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (j : ℕ) (hj : radialExteriorMatrixBound ν₀ < 2*(j : ℝ))
    (hgap : circularFieldBound νp₀ νm₀ η 1 0 < 2*(j : ℝ)) (c : ℂ × ℂ) :
    let U := fun n => spectralOutgoingPolynomial (νp n) (νm n) η n
      (radialExteriorExpansion (ν n) n (m n) j) c j
    let U₀ := spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j
    ∃ T ρ : ℝ, 0 ≤ T ∧ L ≤ T ∧ 0 < ρ ∧ ρ < 1 ∧
      ∃ v : ℕ → CircularTailSpace, ∃ w : CircularTailSpace,
        Tendsto v atTop (𝓝 w) ∧
        let Y := fun n t => circularPolynomialJet (U n) t+circularUnweight (2*(j : ℝ)) (v n) t
        let Y₀ := fun t => circularPolynomialJet U₀ t+circularUnweight (2*(j : ℝ)) w t
        TendstoUniformlyOn Y Y₀ atTop (Ici (0 : ℝ)) ∧
        (∀ n, Tendsto (Y n) atTop (𝓝 ((c.1,0),(c.2,0)))) ∧
        Tendsto Y₀ atTop (𝓝 ((c.1,0),(c.2,0))) ∧
        (∀ᶠ n in atTop, circularFieldBound (νp n) (νm n) η n ρ < 2*(j : ℝ) ∧
          ∀ t, T ≤ t → ‖(radialExteriorCanonical (ν n) n (m n) L t).1‖ ≤ ρ ∧
            HasDerivAt (Y n)
              (circularLeadingField t (Y n t)+circularBoundedField (νp n) (νm n) η n
                (radialExteriorCanonical (ν n) n (m n) L t).1 (Y n t)) t) ∧
        ∀ t, T ≤ t → HasDerivAt Y₀
          (circularLeadingField t (Y₀ t)+circularBoundedField νp₀ νm₀ η 1 0 (Y₀ t)) t := by
  intro U U₀
  let κ := 2*(j : ℝ)
  have hκ : 0 < κ := (radialExteriorMatrixBound_pos ν₀).trans hj
  obtain ⟨T,ρ,hT,hLT,hρ,hρ1,q,f,f₀,hqb,hf,hdata,hfree⟩ :=
    exists_canonical_circular_forcing_limit ν m νp νm ν₀ m₀ νp₀ νm₀ η
      hν hm hp hn δ L hδ hsmall hX j hj c
  let N := fun n : ℕ => max 1 n
  have hN (n : ℕ) : 1 ≤ N n := le_max_left _ _
  have hNlim : Tendsto N atTop atTop := tendsto_atTop_mono (fun n => le_max_right 1 n) tendsto_id
  let ε := fun n => (2*(N n : ℝ)+1)*ρ^(2*N n)
  have hε (n : ℕ) : 0 ≤ ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := (spectralSubunitCoefficient_decay ρ hρ.le hρ1).comp hNlim
  have hcoeff : ∀ᶠ n in atTop, ∀ t,
      ‖spectralDiagonalCoefficient (N n) (q n t)‖+
        ‖spectralCrossCoefficient (N n) (q n t)‖ ≤ ε n :=
    Eventually.of_forall (fun n t => spectralCoefficient_subunit_bound (N n) (hN n) _ ρ (hqb n t))
  let v := fun n => circularInverseCorrection κ hκ (νp n) (νm n) η (N n) (hN n) (q n) (f n)
  let w := circularInverseCorrection κ hκ νp₀ νm₀ η 1 (by omega) 0 f₀
  have hgap' : circularFieldBound νp₀ νm₀ η 1 ‖(0 : ℝ →ᵇ ℂ)‖ < κ := by
    simpa only [norm_zero] using hgap
  have hv : Tendsto v atTop (𝓝 w) := circularInverseCorrection_free_tendsto κ hκ
    νp νm νp₀ νm₀ η hp hn N hN q ε hε hε0 hcoeff hgap' f f₀ hf
  have hu₀ := circularCorrection_isUnit κ hκ νp₀ νm₀ η 1 (by omega) 0 hgap'
  have hB := circularFieldOperator_free_tendsto νp νm νp₀ νm₀ η hp hn N hN q ε hε hε0 hcoeff
  have hu := spectralCorrectionInverse_eventually_unit (circularTailCLM κ hκ) _ _ hB hu₀
  have hm01 : ‖m₀‖ < 1 := by linarith
  let P := fun n => radialExteriorExpansion (ν n) n (m n) j
  let Q := radialFreeExpansion ν₀ m₀ j
  have hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ j :=
    Eventually.of_forall (fun _ => radialExteriorExpansion_degree _ _ _ _)
  have hP (k : ℕ) : Tendsto (fun n => (P n).coeff k) atTop (𝓝 (Q.coeff k)) :=
    radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm01 j k
  have hQ : ‖Q.coeff 0‖ < 1 := by simpa only [Q,radialFreeExpansion_constant] using hm01
  have hgaps : ∀ᶠ n in atTop, circularFieldBound (νp n) (νm n) η n ρ < κ :=
    (circularFieldBound_subunit_tendsto νp νm νp₀ νm₀ η hp hn (fun n => n)
      tendsto_id ρ hρ.le hρ1).eventually (gt_mem_nhds hgap)
  refine ⟨T,ρ,hT,hLT,hρ,hρ1,v,w,hv,?_,?_,?_,?_,?_⟩
  · exact spectralOutgoing_corrected_jet_uniform_limit νp νm νp₀ νm₀ η hp hn
      P Q j hdeg (fun k _ => hP k) hQ c j κ hκ.le v w hv
  · intro n
    have hh := (circularPolynomialJet_tendsto (U n)).add (circularUnweight_tendsto κ hκ (v n))
    have hc : (U n).1.coeff 0=c.1 ∧ (U n).2.coeff 0=c.2 :=
      spectralOutgoingPolynomial_constant (νp n) (νm n) η n (P n) c j
    simpa only [hc.1,hc.2,add_zero] using hh
  · have hh := (circularPolynomialJet_tendsto U₀).add (circularUnweight_tendsto κ hκ w)
    have hc := spectralOutgoingPolynomial_constant νp₀ νm₀ η 1 0 c j
    simpa only [U₀,hc.1,hc.2,add_zero] using hh
  · filter_upwards [hdata,hu,hgaps,eventually_ge_atTop 1] with n hd hun hg hnn
    refine ⟨hg,?_⟩
    intro t ht
    refine ⟨?_,?_⟩
    · rw [← (hd t ht).1]
      exact hqb n t
    have hNeq : N n=n := max_eq_right hnn
    have hun' : IsUnit (1-circularTailCLM κ hκ*circularFieldOperator (νp n) (νm n) η n hnn (q n)) := by
      simpa only [hNeq] using hun
    have hd' := circularInversePolynomial_hasDerivAt κ hκ (νp n) (νm n) η n hnn (q n)
      (P n) (U n) (f n) hun' t (hd t ht).2
    have hvn : v n=circularInverseCorrection κ hκ (νp n) (νm n) η n hnn (q n) (f n) := by
      simp only [v,hNeq]
    rw [← hvn] at hd'
    simpa only [(hd t ht).1] using hd'
  · intro t ht
    have hr : Real.exp (-κ*t) • circularTailEvaluation f₀ t=
        (circularBoundedField νp₀ νm₀ η 1 0 (circularPolynomialJet U₀ t)-
         circularBoundedField νp₀ νm₀ η 1 (radialExteriorPolynomialFunction 0 t)
          (circularPolynomialJet U₀ t))-circularPolynomialResidualJet νp₀ νm₀ η 1 0 U₀ t := by
      simpa only [radialExteriorPolynomialFunction,
        eval_zero,sub_self,zero_sub] using hfree t ht
    exact circularInversePolynomial_hasDerivAt κ hκ νp₀ νm₀ η 1 (by omega) 0 0 U₀ f₀ hu₀ t hr

end DefocusingNLS

end OAI
