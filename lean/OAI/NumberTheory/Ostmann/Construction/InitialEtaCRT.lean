import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTGuard
import OAI.NumberTheory.Ostmann.Construction.InitialEtaStatePhysical
import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

theorem distinctContribution_eq_decompositionAmplitude
    (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {k : ℕ} (aux : AuxiliaryIndex k → PrimeSource) (b s : ℕ) (tb td : ℤ)
    (V : ℕ → ℕ) (X G : ℝ) (hX : 0 < X)
    (hV : ∀ x : JointSample giant bulk spectator aux b s,
      (jointPrior giant bulk spectator aux b s).mass x ≠ 0 →
      Function.Injective (tupleValues x) → tupleBins tb td x ≠ 0 →
      (tuplePeriod x:ℝ)/(4*X) ≤ V 0) :
    distinctContribution d P giant bulk spectator aux b s tb td X =
      decompositionAmplitude d P (initialSources bulk aux b) V giant spectator X G b s k tb td 0 := by
  classical
  let F : SourceSample giant bulk spectator aux b s → ℂ := fun y =>
    ∑ freq : AllowedFrequency V 0,
      let a := outerState (initialSources bulk aux b) (Template.initial (2*b) k) giant y.2 freq.val
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        (spectatorList spectator y.1) a *
      actualCoefficient (initialSources bulk aux b) (Template.initial (2*b) k) V X G
        (residueTransform d) (Arithmetic.sourceStateBins b s tb td)
        (spectatorList spectator y.1) 0 a
  calc
    _ = (jointPrior giant bulk spectator aux b s).cmean
        (fun x => F (sourceEquiv giant bulk spectator aux x)) := by
      apply FinitePrior.cmean_congr_support
      intro x hm
      have hcut (hd : ((jointState x 0).values ++ jointOutside x).Nodup)
          (hb : Arithmetic.sourceStateBins b s tb td (jointOutside x) (jointState x 0) ≠ 0) :
          ((outsideProduct (jointOutside x)*(jointState x 0).product:ℕ):ℝ)/(4*X) ≤ V 0 := by
        rw [jointState_period]
        exact hV x hm ((jointState_nodup_iff x 0).mp hd) (by simpa only [jointState_bins] using hb)
      have hh := distinct_state_physical_eq_canonical d P (initialSources bulk aux b)
        (Template.initial (2*b) k) V G b s tb td (jointState x 0) (jointOutside x)
        (jointState_prime x 0) (jointState_templateAt x 0) hX hcut
      simp only [jointState_nodup_iff] at hh
      rw [← tuplePhysical_eq_state d P x 0 tb td X] at hh
      simpa only [F,stateAtFrequency,jointState,jointOutside,outerState] using hh
    _ = _ := by
      simpa +instances only [F,decompositionAmplitude,actualAmplitude,Template.current] using
        sourceEquiv_cmean giant bulk spectator aux F

end Ostmann.Construction.InitialEta

end

end OAI
