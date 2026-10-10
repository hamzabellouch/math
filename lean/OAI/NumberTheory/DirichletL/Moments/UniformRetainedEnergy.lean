import OAI.NumberTheory.DirichletL.Moments.UniformReflectionChoices
import OAI.NumberTheory.DirichletL.Moments.RetainedComparisonEnergy
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformRetainedEnergy
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionChoices CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentReflectedUniformPair
open CenteredMomentReflectedNormalization

lemma twisted_zero (W:ℝ→ℂ) : CompletedHeight.normTwistedSource W 0=W := by
  funext x
  simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]

lemma normalized_zero (G:𝓢(ℝ,ℂ)) (B:ℕ) (s:ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow G B 0 s 0=
      (fun x=>(annulus x:ℂ)*((1+s)^B:ℂ)*paperRadialFourier G (s*x)) := by
  funext x
  simp only [normalizedReflected,heightScale,pow_zero,div_one,twisted_zero,actual_log_window]
  push_cast
  rfl

lemma retained_zero (χ ψ:Character) (G:𝓢(ℝ,ℂ)) (X R:ℝ) :
    retainedOriginal χ ψ G X R 0=retainedSchwartz χ ψ G X R := by
  unfold retainedOriginal retainedSchwartz
  rw [twisted_zero]

theorem actual_retained_uniform_energy (epsilon : ℝ)
    (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(X R ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high D E Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := actual_independent_choices B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R ly omega Wshort c d lo hi low high D E Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp G χ P s Y keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hD hE hGD henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (P' i) (u i)‖^2)≤
        Cp*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,normalized_zero,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun i=>(G i:ℝ→ℂ)) X R (fun _=>0) hX (fun _=>B) 0 P' (fun _=>hB)
    0 Rcap _ le_rfl (fun _=>by simp) hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [retained_zero,P',Nat.mul_zero,pow_zero,mul_one,←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentUniformRetainedEnergy

end

end OAI
