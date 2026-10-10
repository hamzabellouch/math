import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
import OAI.NumberTheory.DirichletL.Moments.SourceRow

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstEnergy
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentHeckeExpansion HeckeFamily ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK

end SevenEighths.CenteredMomentFirstEnergy

end

end OAI
