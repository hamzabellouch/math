import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairFlags HistoryPairKernelReplacement PolynomialFlagReplacementFinite
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem representative_sample_eq_toNat (sources : SourceFamily) (h k : History l)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples sources h k x)
    (r : Representative h k) :
    x (representativeMap h k r) = ((x (representativeMap h k r)).toNat : ℤ) := by
  obtain ⟨i,rfl⟩ := label_surjective h k r
  rcases i with i | i
  · obtain ⟨n,hn,_⟩ := hx.1 (.inr i)
    change x (leftMap h k (.inr (.inr i))) = ((x (leftMap h k (.inr (.inr i)))).toNat : ℤ)
    rw [hn,Int.toNat_natCast]
  · obtain ⟨n,hn,_⟩ := hx.2 (.inr i)
    change x (rightMap h k (.inr (.inr i))) = ((x (rightMap h k (.inr (.inr i)))).toNat : ℤ)
    rw [hn,Int.toNat_natCast]

theorem product_error_of_source_samples
    {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (mixed : Bool) (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples C.sources h k x)
    (p : Representative h k → ℕ) (hp : ∀r, x (representativeMap h k r) = (p r : ℤ))
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) :
    (∏r, (p r : ℝ)) * |(∏r, actualProbability mixed h k hs ks r (p r) x) -
      ∏r, symbolicKernel mixed h k hs ks r (p r)| ≤
      4*2^(Fintype.card (Representative h k)) *
        ∑r, ∑j : Index h k r, flagError (polynomial h k hs ks r j) x (p r) := by
  have hprime (r : Representative h k) := new_sample_prime C.sources h k x hx r (p r) (hp r)
  have hactual (r : Representative h k) := actualProbability_le_two_div mixed h k hs ks r
    (p r) (hprime r) x
    (new_sample_family_nonzero C hsep h k hh kh hs ks x hx r (p r) (hprime r) (hp r) hV)
  have hsymbolic (r : Representative h k) := symbolicKernel_le_two_div mixed h k hs ks r (p r) (hprime r)
  apply weighted_product_error (fun r => (p r : ℝ))
    (fun r => actualProbability mixed h k hs ks r (p r) x)
    (fun r => symbolicKernel mixed h k hs ks r (p r))
    (fun r => ∑j : Index h k r, flagError (polynomial h k hs ks r j) x (p r))
  · exact fun r => Nat.cast_nonneg _
  · exact fun r => (hactual r).1
  · exact fun r => (hsymbolic r).1
  · intro r
    have hpos : (0 : ℝ) < p r := by exact_mod_cast (hprime r).pos
    simpa only [mul_comm] using (le_div_iff₀ hpos).mp (hactual r).2
  · intro r
    have hpos : (0 : ℝ) < p r := by exact_mod_cast (hprime r).pos
    simpa only [mul_comm] using (le_div_iff₀ hpos).mp (hsymbolic r).2
  · intro r
    exact Finset.sum_nonneg (fun j _ => flagError_nonneg _ _ _)
  · exact fun r => scaled_error_of_source_samples C hsep mixed h k hh kh hs ks hroot
      x hx r (p r) (hp r) hV

theorem sampled_product_error_of_source_samples
    {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (mixed : Bool) (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples C.sources h k x)
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) :
    (∏r : Representative h k, ((x (representativeMap h k r)).toNat : ℝ)) *
      |(∏r, actualProbability mixed h k hs ks r (x (representativeMap h k r)).toNat x) -
        ∏r, symbolicKernel mixed h k hs ks r (x (representativeMap h k r)).toNat| ≤
      4*2^(Fintype.card (Representative h k)) * ∑r, ∑j : Index h k r,
        flagError (polynomial h k hs ks r j) x (x (representativeMap h k r)).toNat :=
  product_error_of_source_samples C hsep mixed h k hh kh hs ks hroot x hx _
    (representative_sample_eq_toNat C.sources h k x hx) hV

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
