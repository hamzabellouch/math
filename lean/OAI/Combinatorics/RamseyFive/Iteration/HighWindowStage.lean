import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.HistoryPrivateStream
import OAI.Combinatorics.RamseyFive.Marking.HighFourPreRound
import OAI.Combinatorics.RamseyFive.Streams.HighActualExtraction

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hwsBDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hwsTDE : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hwsIDE : DecidableEq (Slots 1 n) := Classical.decEq _

def oneMiddleEmbedding (n : ℕ) : Fin (2*n)↪o Fin (1*(4*n)) :=
  OrderEmbedding.ofStrictMono (fun t=>slotEmbedding (Sum.inr ((0:Fin 1),t)))
    (fun _ _ h=>middle_order 0 _ _ h)

variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin 1×Bool→Finset (Fin n)) (steps r' : ℕ) (s : ℝ) (h : ℕ)

def highSampleStream :=
  ((historyStream S ctx elig steps).reindex (oneMiddleEmbedding n)).augment
    (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h
      (actualWindowHistory ctx steps z))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma highSampleStream_loss_mean :
    mean (highSampleStream S ctx elig steps r' s h).law
      (fun z=>((coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z)
        (highDomain z.2))ᶜ.card:ℝ))=
    mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ)) := by
  dsimp only [highSampleStream,SelectedStream.augment,SelectedStream.reindex]
  rw [historyStream_law,mean_adaptive]
  have he:=originalHistory_mean S.law ctx (windowTuple S) elig steps
    (fun z x=>mean (highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z)
      (fun v=>((coveredPositions (fun t=>x (Sum.inr (0,t))) (highDomain v))ᶜ.card:ℝ)))
  simp only [preRoundTupleLaw,mean_adaptive]
  convert he using 1
  apply congrArg (mean _)
  funext z
  rfl

omit [Finite K] [Fintype (ℙ K (Dual K (Dual K V)))] in
theorem highSampleStream_extract (hdim : finrank K V=5) {l : ℕ} (hl : l<2*n)
    (hloss : mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
        ((2*n:ℝ)-l)/10) :
    ∃ hE : 0<eventMass (highSampleStream S ctx elig steps r' s h).law
      (Finset.univ.filter fun z=>l≤(coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z)
        (highDomain z.2)).card),
      let S':=((highSampleStream S ctx elig steps r' s h).restrict _ hE).extract hl.le
        (fun z=>coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z) (highDomain z.2))
      S'.density≤(10/9)*S.density ∧
      entropy (map S'.law S'.tuple)≤3*h*Real.log (Fintype.card (FlagPair K V))+
        l*Real.log (Fintype.card (ℙ K (Dual K V))) := by
  let T:=highSampleStream S ctx elig steps r' s h
  let E:=Finset.univ.filter (fun z=>l≤(coveredPositions (T.tuple z) (highDomain z.2)).card)
  have hp : (9:ℝ)/10≤eventMass T.law E := by
    apply extraction_probability _ _ hl
    convert (highSampleStream_loss_mean S ctx elig steps r' s h).trans_le hloss using 1
    simp only [Nat.cast_mul,Nat.cast_ofNat]
  have hE : 0<eventMass T.law E := lt_of_lt_of_le (by norm_num) hp
  refine ⟨hE,?_,?_⟩
  · change S.density/eventMass T.law E≤(10/9)*S.density
    calc
      _ ≤S.density/(9/10) := div_le_div_of_nonneg_left S.density_nonneg (by norm_num) hp
      _ =_ := by ring
  · convert high_extracted_entropy hdim hl.le T.law T.tuple (fun z=>z.2) hE using 1
    congr 1
    exact Subsingleton.elim _ _
end
end SharpRamseyFive.SelectedTuple

end OAI
