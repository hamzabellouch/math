import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet

open MainAlgorithm

/-- The source safety guarantee, including the literal constants, all listed
groups, global independent comparison set, and the harmless unlisted zero case. -/
def SafeSampleClaim : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)), M.Indep Y →
    exitThreshold / 4 *
        ((d.D : Set (Fin n)) ∩ (Y ∩ (trueGroup M d s i : Set (Fin n)))).ncard -
        (d.D ∩ trueGroup M d s i).card / densityThreshold ≤
      bitsExpectation (fun _ => thinningRate) Finset.univ (fun C =>
        bitsExpectation (fun _ => thinningRate) Finset.univ (fun T =>
          fairParityExpectation (fun p =>
            (listedSafeStatistic M hE (2 ^ 100) (withMasks d d.D C T) s i Y
              (boolParity p) : ℝ))))

end MatroidProphet

end OAI
