import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportMaskBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryPairPattern HistoryCRTIntegration HistorySignedSpectatorCRT
open HistoryBulkReferenceTests HistoryBulkResidueNormSum HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryGiantWeightedPriorReplacement HistoryBulkReferenceNewModuli
variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma new_A_dvd (newh h k : History l) (outside : List ℕ) (K : ℕ) :
    rootModulus newh∣newComparisonModulus newh h k outside K := by
  refine ⟨outside.prod*frequencyModulus h k (K+2)*representativeModulus h k,?_⟩
  unfold newComparisonModulus
  ring

lemma new_D_dvd (newh h k : History l) (outside : List ℕ) (K : ℕ) :
    outside.prod∣newComparisonModulus newh h k outside K := by
  refine ⟨rootModulus newh*frequencyModulus h k (K+2)*representativeModulus h k,?_⟩
  unfold newComparisonModulus
  ring

lemma new_R_dvd (newh h k : History l) (outside : List ℕ) (K : ℕ) :
    frequencyModulus h k (K+2)∣newComparisonModulus newh h k outside K := by
  refine ⟨rootModulus newh*outside.prod*representativeModulus h k,?_⟩
  unfold newComparisonModulus
  ring

lemma new_B_dvd (newh h k : History l) (outside : List ℕ) (K : ℕ) :
    representativeModulus h k∣newComparisonModulus newh h k outside K := by
  refine ⟨rootModulus newh*outside.prod*frequencyModulus h k (K+2),?_⟩
  unfold newComparisonModulus
  ring

def newReferenceResidueTest (d : Decomposition) (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (newh newk : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ) :
    ZMod (newComparisonModulus newh h k outside K)×ZMod (newComparisonModulus newh h k outside K)→ℂ :=
  referenceResidueTest K h k hs ks newh newk (residueTransform d) σ x v
    (newComparisonModulus newh h k outside K) (new_A_dvd newh h k outside K)
    (new_D_dvd newh h k outside K) (new_R_dvd newh h k outside K) (new_B_dvd newh h k outside K) fA

theorem new_reference_test_budget (d : Decomposition) (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (newh newk : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ)
    (hout : ∀q∈outside,q.Prime)
    [NeZero (newComparisonModulus newh h k outside K)]
    (hW : ∀z,‖fA z‖≤(rootModulus newh:ℝ)) :
    let M := newComparisonModulus newh h k outside K
    let R := newReferenceResidueTest d K h k hs ks newh newk σ x v fA
    (∀z,‖R z‖≤(M:ℝ)^(3+2^(l+1))) ∧
    (∑u : Bool→(ZMod M)ˣ,‖primeTest R u‖)≤(M:ℝ)^(3+2^(l+1)) ∧
    (∑r : ZMod M,∑u : Unit→(ZMod M)ˣ,‖mixedTest R r u‖)≤(M:ℝ)^(3+2^(l+1)) := by
  apply reference_test_budget d K h k hs ks newh newk σ x v _ _ _ _ _ fA hout
  intro z
  exact (hW z).trans (by exact_mod_cast Nat.le_of_dvd (NeZero.pos _) (new_A_dvd newh h k outside K))

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
