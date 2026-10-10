import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.DimensionThreePublic
import OAI.Combinatorics.RamseyFive.Geometry.BasePublicFamily
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy
open MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseOutcome (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) : Option (Finset (ℙ K V)) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  let dec := fun m : baseAlphabet U S.card P τ=>baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
  (chooseMessage (fun (u : BaseTape U P τ R) (m : baseAlphabet U S.card P τ) =>
    let W := baseMessageDecoded U P τ R L₀ u ⟨n,m⟩
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) t).map dec

noncomputable def baseCaptureLaw (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (Option (Finset (ℙ K V))) :=
  finiteImageLaw (baseTapeMeasure U P τ R L₀) (baseOutcome S U P τ R L₀)

omit [Finite K] [FiniteDimensional K V] in
lemma baseOutcome_none (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    baseOutcome S U P τ R L₀ t=none ↔
      ¬∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  simp only [baseOutcome,Option.map_eq_none_iff,chooseMessage_none]

omit [Finite K] [FiniteDimensional K V] in
lemma baseCaptureLaw_positive (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (W : Finset (ℙ K V)) (hW : 0<baseCaptureLaw S U P τ R L₀ (some W)) :
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  obtain ⟨t,ht⟩ := finiteImageLaw_positive (baseTapeMeasure U P τ R L₀)
    (baseOutcome S U P τ R L₀) (some W) hW
  dsimp only [baseOutcome] at ht
  obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp ht
  have hs := chooseMessage_sound _ t m hm
  simpa only [he] using hs

omit [Finite K] [FiniteDimensional K V] in
lemma baseCaptureLaw_failure (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (E : Set (BaseTape U P τ R)) (ε : ℝ)
    (hE : (baseTapeMeasure U P τ R L₀).real Eᶜ≤ε)
    (hs : ∀t∈E,∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) :
    baseCaptureLaw S U P τ R L₀ none≤ε := by
  apply (measureReal_mono (μ:=baseTapeMeasure U P τ R L₀)
    (show {t | baseOutcome S U P τ R L₀ t=none}⊆Eᶜ from ?_)).trans hE
  intro t ht he
  exact (baseOutcome_none S U P τ R L₀ t).mp ht (hs t he)

end

section
open Module ProjectiveIncidence FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoredOutcome (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (t : BaseTape U P τ R) :
    Option (Finset (ℙ K V)) :=
  let dec := fun m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) =>
    publicDecoded U Own Base m.2 (t n m.1)
  (chooseMessage (fun (u : BaseTape U P τ R)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := publicDecoded U Own Base m.2 (u n m.1)
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map dec

noncomputable def scoredCaptureLaw (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (Option (Finset (ℙ K V))) :=
  finiteImageLaw (baseTapeMeasure U P τ R L₀) (scoredOutcome X U n Own Base P τ c a R)

omit [Finite K] [FiniteDimensional K V] in
lemma scoredCaptureLaw_positive (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (W : Finset (ℙ K V)) (hW : 0<scoredCaptureLaw X U n Own Base P τ c a R L₀ (some W)) :
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ) := by
  obtain ⟨t,ht⟩ := finiteImageLaw_positive (baseTapeMeasure U P τ R L₀)
    (scoredOutcome X U n Own Base P τ c a R) (some W) hW
  dsimp only [scoredOutcome] at ht
  obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp ht
  have hs := chooseMessage_sound _ t m hm
  simpa only [he] using hs

omit [Finite K] [FiniteDimensional K V] in
lemma scoredCaptureLaw_failure (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (E : Set (Fin (sizeScoreCutoff U n P τ)→Fin R→ℙ K V→ℕ)) (ε : ℝ)
    (hE : (baseRowMeasure U n P τ R L₀).real Eᶜ≤ε)
    (hs : ∀t∈E,∃i : Fin (sizeScoreCutoff U n P τ),∃z : Fin (Fintype.card (ℙ K (Dual K V))+1),
      let W := publicDecoded U Own Base z (t i)
      W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) :
    scoredCaptureLaw X U n Own Base P τ c a R L₀ none≤ε := by
  have hm := baseTape_marginal U P τ R L₀ n Eᶜ
  have hsub : {t | scoredOutcome X U n Own Base P τ c a R t=none}⊆{t : BaseTape U P τ R | t n∈Eᶜ} := by
    intro t ht he
    obtain ⟨i,z,hgood⟩ := hs (t n) he
    have hn : ¬∃m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1),
        let W := publicDecoded U Own Base m.2 (t n m.1)
        W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ) := by
      simpa only [Set.mem_ofPred_eq,scoredOutcome,Option.map_eq_none_iff,chooseMessage_none] using ht
    exact hn ⟨(i,z),hgood⟩
  exact (measureReal_mono (μ:=baseTapeMeasure U P τ R L₀) hsub).trans (hm.trans_le hE)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_public_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    (∀i,(C i).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p := scoredCaptureLaw X U n (messageOwn c) (messageBase c L₀)
      (P η σ D R) τ (9/20) 10 R L₀
    p none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/20:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_three_public_predictor hη hη' Cb hCb] with σ hh
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  obtain ⟨hcost,hN,c,E,hE,hd⟩ := hh D b τ g R L₀ q K I J F hF Flat X U T
    hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover hsmall
  let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  have hf := scoredCaptureLaw_failure X U n (messageOwn c) (messageBase c L₀)
    (P η σ D R) τ (9/20) 10 R L₀ E (Real.exp (-(Nat.card K:ℝ))) hE hd
  have hg := scoredCaptureLaw_positive X U n (messageOwn c) (messageBase c L₀)
    (P η σ D R) τ (9/20) 10 R L₀
  exact ⟨hcost,hN,c,hf,hg⟩

end SharpRamseyFive.ScoreGeometry

end OAI
