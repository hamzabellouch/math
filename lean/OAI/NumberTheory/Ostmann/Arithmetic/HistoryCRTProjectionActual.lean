import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjection

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTProjection
open Construction ResidueHaar HistoryCRTIntegration HistoryPairRepresentatives
open HistoryRepresentativeSourceSeparation
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem actual_unit_joint_average_enlarged (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    {M : ℕ} [NeZero M] (hd : (∏ i,historyModuli h g outside n i)∣M)
    (F : (∀ i,UnitPair (historyModuli h g outside n i)) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : UnitPair M => F (unitPairEquiv _
      (historyModuli_pairwise h g hp n) (unitPairMap hd z)))=average F := by
  let := historyModuliNeZero h g hs gs hout n
  exact (unit_pair_average hd _).trans (actual_unit_joint_average h g hs gs hout hp n F)

theorem actual_mixed_joint_average_enlarged (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    {M : ℕ} [NeZero M] (hd : (∏ i,historyModuli h g outside n i)∣M)
    (F : (∀ i,MixedPair (historyModuli h g outside n i)) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : MixedPair M => F (mixedPairEquiv _
      (historyModuli_pairwise h g hp n) (mixedPairMap hd z)))=average F := by
  let := historyModuliNeZero h g hs gs hout n
  exact (mixed_pair_average hd _).trans (actual_mixed_joint_average h g hs gs hout hp n F)

theorem representative_unit_joint_average_enlarged (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside) {M : ℕ} [NeZero M]
    (hd : (∏ r : Representative h g,(prime h g r)^2)∣M)
    (F : (∀ r : Representative h g,UnitPair ((prime h g r)^2)) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : UnitPair M => F (unitPairEquiv _ hp.2.1 (unitPairMap hd z)))=
      average F := by
  let := representativeSquaresNeZero h g hs gs
  exact (unit_pair_average hd _).trans (representative_unit_joint_average h g hs gs hp F)

theorem representative_mixed_joint_average_enlarged (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : PairAdmissible h g outside) {M : ℕ} [NeZero M]
    (hd : (∏ r : Representative h g,(prime h g r)^2)∣M)
    (F : (∀ r : Representative h g,MixedPair ((prime h g r)^2)) → ℂ) :
    letI := representativeSquaresNeZero h g hs gs
    average (fun z : MixedPair M => F (mixedPairEquiv _ hp.2.1 (mixedPairMap hd z)))=
      average F := by
  let := representativeSquaresNeZero h g hs gs
  exact (mixed_pair_average hd _).trans (representative_mixed_joint_average h g hs gs hp F)

end Ostmann.Arithmetic.HistoryCRTProjection

end

end OAI
