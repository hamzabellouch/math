import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GeneralReversedCode

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=4) (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let pred := threeFinitePredictor hd σ U UT (P η σ D R) τ R L₀
        let p := pred.output X T
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,pred.encoded X T t=some m → pred.cost t m≤
          4100*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_three_coordinates_certified hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact hh D b τ R L₀ q K V e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def orientedFinitePredictor
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (d H : ℕ) (q P c B : ℝ) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) where
  Tape := f.Tape × GeneralReversedTape r.Tape K V H q
  tapeFintype := inferInstance
  Message := fun t=>f.Message t.1 ⊕ GeneralReversedMessage r.Message r.decoded H q t.2
  messageFintype := fun _=>inferInstance
  tapeLaw := adaptiveLaw f.tapeLaw (fun _=>adaptiveLaw r.tapeLaw (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
  decoded := fun t m=>match m with
    | .inl m=>f.decoded t.1 m
    | .inr m=>generalReversedDecoded r.Message r.decoded U H q t.2 m
  encoded := fun S T t=>if S.card≤T.card then (f.encoded S T t.1).map Sum.inl else
    if hn : reverseLength q (Real.log ((U.card:ℝ)/S.card))≤H then
      (generalReversedEncoded r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT H
        ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P)) c t.2).map Sum.inr
    else none
  cost := fun t m=>Real.log 2 + match m with
    | .inl m=>f.cost t.1 m
    | .inr m=>generalReversedCost r.Message r.decoded r.cost H q t.2 m

omit [Finite K] in
lemma orientedFinite_output
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (d H : ℕ) (q P c B : ℝ) (hc : 0<c)
    (hn : reverseLength q (Real.log ((U.card:ℝ)/S.card))≤H) :
    (orientedFinitePredictor f r U UT d H q P c B).output S T=
      if S.card≤T.card then f.output S T else
        optionCompose (r.output T (S.map bidualPoint.toEmbedding))
          (generalNextCapLaw S U T UT hT c hc
            (reverseLength q (Real.log ((U.card:ℝ)/S.card))) q
            ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P))) := by
  by_cases h : S.card≤T.card
  · simp only [FinitePredictor.output,orientedFinitePredictor,ite_eq_left h,Option.map_map,Function.comp_def]
    exact map_independent_left _ _ (fun t=>(f.encoded S T t).map (f.decoded t))
  · simp only [FinitePredictor.output,orientedFinitePredictor,ite_eq_right h,dite_eq_left hn,Option.map_map,Function.comp_def]
    exact (map_independent_right _ _ (fun t=>
      (generalReversedEncoded r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT H
        ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P)) c t).map
          (generalReversedDecoded r.Message r.decoded U H q t))).trans
      (generalReversed_law r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) r.tapeLaw
        S U T UT hT H ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card)
          ((T.card:ℝ)*Real.exp (B*P)) c hc)
end SharpRamseyFive.ScoreGeometry

end OAI
