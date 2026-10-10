import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementUnnormalizedExact

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairFlags PolynomialFlagReplacementFinite Filter
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem new_sample_prime (sources : SourceFamily) (h k : History l)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples sources h k x)
    (r : Representative h k) (p : ℕ) (hp : x (representativeMap h k r)=(p:ℤ)) : p.Prime := by
  obtain ⟨i,rfl⟩ := label_surjective h k r
  rcases i with i | i
  · obtain ⟨n,hn,hm⟩ := hx.1 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hp
    subst n
    exact resampledSlot_prime hm
  · obtain ⟨n,hn,hm⟩ := hx.2 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hp
    subst n
    exact resampledSlot_prime hm

theorem scaled_error_of_source_samples
    {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (mixed : Bool) (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples C.sources h k x)
    (r : Representative h k) (p : ℕ) (hp : x (representativeMap h k r)=(p:ℤ))
    (hV : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j)) :
    (p:ℝ)*|actualProbability mixed h k hs ks r p x-symbolicKernel mixed h k hs ks r p| ≤
      4*∑j : Index h k r,flagError (polynomial h k hs ks r j) x p := by
  have hp' := new_sample_prime C.sources h k x hx r p hp
  exact actualProbability_scaled_error_le mixed h k hs ks hroot r p hp' x
    (new_sample_family_nonzero C hsep h k hh kh hs ks x hx r p hp' hp hV)

theorem selected_new_sample_scaled_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {depth : ℕ} (hdepth : 0 < depth) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀l,l ≤ depth → ∀outside : List ℕ,∀mixed : Bool,∀h k : History l,
      TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h →
      TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k →
      ∀(hs : h.Supported (Conclusion.frequencyBound Bs BD Bz depth L) outside)
        (ks : k.Supported (Conclusion.frequencyBound Bs BD Bz depth L) outside),
      RootGiantsAgree h k → ∀(x : PairKey h k → ℤ)(r : Representative h k)(p : ℕ),
      SmallSourceSamples C.sources h k (Function.update x (representativeMap h k r) (p:ℤ)) →
      (p:ℝ)*|actualProbability mixed h k hs ks r p
        (Function.update x (representativeMap h k r) (p:ℤ))-symbolicKernel mixed h k hs ks r p| ≤
        4*∑j : Index h k r,flagError (polynomial h k hs ks r j)
          (Function.update x (representativeMap h k r) (p:ℤ)) p := by
  classical
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hdepth,
    initial_sources_above_frequencies_eventually d Bs BD Bz hdepth] with L hsep hfreq
  intro E C hG hc hcu hb hd spectator hspec l hl outside mixed h k hh kh hs ks hroot x r p hx
  exact scaled_error_of_source_samples C (hsep E C hG hc hcu hb hd spectator hspec)
    mixed h k hh kh hs ks hroot _ hx r p (by simp only [Function.update_self])
    (fun j hj=>(hfreq E C hG hc hcu hb hd j (hj.trans hl)).2)

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
