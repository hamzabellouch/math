import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open Construction ResidueHaar HistoryPairRepresentatives HistoryRepresentativeSourceSeparation
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem actual_unit_joint_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    (F : (∀ i,UnitPair (historyModuli h g outside n i)) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : UnitPair (∏ i,historyModuli h g outside n i) =>
      F (unitPairEquiv _ (historyModuli_pairwise h g hp n) z)) = average F := by
  let := historyModuliNeZero h g hs gs hout n
  exact unit_joint_average _ _ F

theorem actual_mixed_joint_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    (F : (∀ i,MixedPair (historyModuli h g outside n i)) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : MixedPair (∏ i,historyModuli h g outside n i) =>
      F (mixedPairEquiv _ (historyModuli_pairwise h g hp n) z)) = average F := by
  let := historyModuliNeZero h g hs gs hout n
  exact mixed_joint_average _ _ F

theorem actual_unit_product_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    (f : ∀ i,UnitPair (historyModuli h g outside n i) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : UnitPair (∏ i,historyModuli h g outside n i) =>
      ∏ i,f i (unitPairEquiv _ (historyModuli_pairwise h g hp n) z i)) =
      ∏ i,average (f i) := by
  let := historyModuliNeZero h g hs gs hout n
  exact unit_product_average _ _ f

theorem actual_mixed_product_average (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (hp : PairAdmissible h g outside) (n : ℕ)
    (f : ∀ i,MixedPair (historyModuli h g outside n i) → ℂ) :
    letI := historyModuliNeZero h g hs gs hout n
    average (fun z : MixedPair (∏ i,historyModuli h g outside n i) =>
      ∏ i,f i (mixedPairEquiv _ (historyModuli_pairwise h g hp n) z i)) =
      ∏ i,average (f i) := by
  let := historyModuliNeZero h g hs gs hout n
  exact mixed_product_average _ _ f

theorem actual_unit_card (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (n : ℕ) :
    letI := historyModuliNeZero h g hs gs hout n
    Fintype.card (UnitPair (∏ i,historyModuli h g outside n i))=
      (rootModulus h*outsideModulus outside*frequencyModulus h g n*representativeModulus h g).totient^2 := by
  let := historyModuliNeZero h g hs gs hout n
  rw [unitPair_card,historyModuli_prod]

theorem actual_mixed_card (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (n : ℕ) :
    letI := historyModuliNeZero h g hs gs hout n
    Fintype.card (MixedPair (∏ i,historyModuli h g outside n i))=
      (rootModulus h*outsideModulus outside*frequencyModulus h g n*representativeModulus h g)*
      (rootModulus h*outsideModulus outside*frequencyModulus h g n*representativeModulus h g).totient := by
  let := historyModuliNeZero h g hs gs hout n
  rw [mixedPair_card,historyModuli_prod]

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
