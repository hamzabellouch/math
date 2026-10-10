import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GenericFreshCost

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev BaseMessage (U : Finset (ℙ K V)) (P τ : ℝ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) × baseAlphabet U n P τ
abbrev BaseTable (U : Finset (ℙ K V)) (P τ : ℝ) := BaseMessage U P τ→Finset (ℙ K V)

noncomputable def baseTableLaw (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (BaseTable U P τ) :=
  publicTableLaw (α:=BaseMessage U P τ) (β:=Finset (ℙ K V))
    (Ω:=BaseTape U P τ R) (baseTapeMeasure U P τ R L₀) (baseMessageDecoded U P τ R L₀)

noncomputable def baseTableEncoded (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) : Option (baseAlphabet U S.card P τ) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  chooseMessage (fun (u : BaseTable U P τ) m=>
    let W := u ⟨n,m⟩
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) t

noncomputable def baseFiniteEncoded (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) : Option (BaseMessage U P τ) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  (baseTableEncoded S U P τ t).map (fun m=>⟨n,m⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_exact (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    (baseFiniteEncoded S U P τ (baseMessageDecoded U P τ R L₀ t)).map
        (baseMessageDecoded U P τ R L₀ t)=baseOutcome S U P τ R L₀ t := by
  simp only [baseFiniteEncoded,baseTableEncoded,baseOutcome,Option.map_map]
  rfl

omit [Finite K] [FiniteDimensional K V] in
theorem baseFinite_law (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    map (baseTableLaw U P τ R L₀) (fun t=>(baseFiniteEncoded S U P τ t).map t)=
      baseCaptureLaw S U P τ R L₀ := by
  rw [baseTableLaw,publicTableLaw,finiteImageLaw_map]
  unfold baseCaptureLaw
  congr 1
  funext t
  exact baseFinite_exact S U P τ R L₀ t

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_header (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) : m.1.val=S.card := by
  obtain ⟨x,hx,he⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun z : BaseMessage U P τ=>z.1.val) he.symm
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoredEncoded (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) : Option (ScoredMessage U σ P τ) :=
  (chooseMessage (fun (u : BaseTape U P τ R)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := publicDecoded U (messageOwn code) (messageBase code L₀) m.2 (u n m.1)
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map
      (fun m=>⟨n,code,m⟩)

omit [Fintype V] in
lemma scoredEncoded_exact (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) :
    (scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t)=
      scoredOutcome X U n (messageOwn code) (messageBase code L₀) P τ c a R t := by
  simp only [scoredEncoded,scoredOutcome,Option.map_map]
  rfl

lemma scoredEncoded_law (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) :
    finiteImageLaw (baseTapeMeasure U P τ R L₀)
      (fun t=>(scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t))=
      scoredCaptureLaw X U n (messageOwn code) (messageBase code L₀) P τ c a R L₀ := by
  simp only [scoredEncoded_exact,scoredCaptureLaw]

omit [Fintype V] in
lemma scoredEncoded_header (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) (m : ScoredMessage U σ P τ)
    (hm : scoredEncoded X U n σ P τ c a R L₀ code t=some m) :
    m.1=n := by
  obtain ⟨z,_,hz⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun y : ScoredMessage U σ P τ=>y.1) hz.symm

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev ScoreTable (U : Finset (ℙ K V)) (σ P τ : ℝ) :=
  ScoredMessage U σ P τ→Finset (ℙ K V)
noncomputable def scoreTableLaw (U : Finset (ℙ K V)) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ScoreTable U σ P τ) :=
  publicTableLaw (Ω:=BaseTape U P τ R) (α:=ScoredMessage U σ P τ) (β:=Finset (ℙ K V))
    (baseTapeMeasure U P τ R L₀) (scoredMessageDecoded U σ P τ R L₀)

noncomputable def scoreFiniteEncoded (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : ScoreTable U σ P τ) : Option (ScoredMessage U σ P τ) :=
  (chooseMessage (fun (u : ScoreTable U σ P τ)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := u ⟨n,code,m⟩
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map
      (fun m=>⟨n,code,m⟩)

omit [Fintype V] in
lemma scoreFinite_exact (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) :
    scoreFiniteEncoded X U n σ P τ c a code (scoredMessageDecoded U σ P τ R L₀ t)=
      scoredEncoded X U n σ P τ c a R L₀ code t := by
  rfl

theorem scoreFinite_law (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) :
    map (scoreTableLaw U σ P τ R L₀)
      (fun t=>(scoreFiniteEncoded X U n σ P τ c a code t).map t)=
      scoredCaptureLaw X U n (messageOwn code) (messageBase code L₀) P τ c a R L₀ := by
  rw [scoreTableLaw,publicTableLaw,finiteImageLaw_map]
  exact scoredEncoded_law X U n σ P τ c a R L₀ code
end SharpRamseyFive.ScoreGeometry

end OAI
