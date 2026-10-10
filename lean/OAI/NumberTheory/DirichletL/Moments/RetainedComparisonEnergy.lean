import OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
import OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentRetainedComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedChoiceEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_retained_fixed_profile_energy (a b epsilon : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(χ ψ : ι→Character)(P : ι→ℂ)(X R t ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high E T Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (X i) (R i) (t i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := actual_independent_profile_choices a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cp,hCp,hp⟩ := hn Wlong hs hW
  refine ⟨Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ χ ψ P X R t ly omega Wshort c d lo hi low high E T Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hE hT ht hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp χ P s Y keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hE henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) Wlong (X i) (R i) (t i) (hX i) B n (P' i) (u i)‖^2)≤
        Cp*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun _=>Wlong) X R t hX (fun _=>B) n P' (fun _=>hB)
    T Rcap _ hT ht hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [P',←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentRetainedComparisonEnergy

end

end OAI
