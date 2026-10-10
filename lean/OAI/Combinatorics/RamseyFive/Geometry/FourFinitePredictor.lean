import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FourHeader

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def fourFinitePredictor (hd : finrank K V=5) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Fintype K := Fintype.ofFinite _
  letI : Finite (Dual K (Fin 5→K)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Fin 5→K)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Fin 5→K))) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Finite (Dual K A) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 5→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 5→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact (fourCertifiedPredictor (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀).transform
      (projectiveEquiv e).symm.toEmbedding
      (fun X T=>(X.map (projectiveEquiv e).toEmbedding,T.map (projectiveEquiv e.symm.dualMap).toEmbedding))

theorem eventually_four_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let pred := fourFinitePredictor hd σ U UT (P η σ D R) τ R L₀
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound X U (9/100000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,pred.encoded X T t=some m → pred.cost t m≤
          30100*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_four_certified hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 5→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 5→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 5→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let (x : ℙ K (Fin 5→K)) : Fintype (RadialLine x) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 5→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  let X' := X.map (projectiveEquiv e).toEmbedding
  let U' := U.map (projectiveEquiv e).toEmbedding
  let T' := T.map (projectiveEquiv e.symm.dualMap).toEmbedding
  let UT' := UT.map (projectiveEquiv e.symm.dualMap).toEmbedding
  have hXU' : X'⊆U' := Finset.map_subset_map.mpr hXU
  have hTU' : T'⊆UT' := Finset.map_subset_map.mpr hTU
  have hdens' : (Nat.card K:ℝ)*(incidences X' T':ℝ)≤τ*X'.card*T'.card := by
    simpa only [X',T',incidences_coordinates,Finset.card_map] using hdens
  have hprod' : (Nat.card K:ℝ)^5*Real.exp (-b)≤(X'.card:ℝ)*T'.card := by
    simpa only [X',T',Finset.card_map] using hprod
  obtain ⟨hf,hg,hc⟩ := hh D b τ R L₀ q K X' U' T' UT' hcard hσq hr hL hb hbhi hτ hτhi hXU' hTU'
    (by simpa only [X',T',Finset.card_map] using hXT) hdens' hprod'
  let pp := fourCertifiedPredictor U' UT' σ (P η σ D R) τ R L₀
  change (pp.transform _ _).output X T _≤_ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · rw [FinitePredictor.transform_output,map_option_none]
    exact hf
  · intro W hW
    change 0<(pp.transform (projectiveEquiv e).symm.toEmbedding
      (fun X T=>(X.map (projectiveEquiv e).toEmbedding,T.map (projectiveEquiv e.symm.dualMap).toEmbedding))).output X T (some W) at hW
    rw [FinitePredictor.transform_output] at hW
    obtain ⟨Z,hZ,he⟩ := map_positive (pp.output X' T')
      (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding) (some W) hW
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (projectiveEquiv e).symm.toEmbedding=W := Option.some.inj he
      subst W
      have hz := hg Z hZ
      obtain ⟨hU,hcard',hcap⟩ := decoded_coordinates e U X Z hz.1
      refine ⟨hU,?_,?_⟩
      · simpa only [hcard',X',Finset.card_map] using hz.2.1
      · rw [Finset.inter_comm X _,hcap]
        simpa only [X',Finset.card_map] using hz.2.2
  · intro t m hm
    change pp.cost t m≤_
    have hh := hc t m hm
    simpa only [U',X',T',UT',Finset.card_map] using hh
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev FiniteNodeTape (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) :=
  pred.Tape × AmbientPairTape K V H q
noncomputable def finiteNodeTapeLaw (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) :
    Law (FiniteNodeTape pred H q) :=
  adaptiveLaw pred.tapeLaw (fun _=>ambientPairTapeLaw H q)
abbrev FiniteNodeMessage (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q) :=
  (m : pred.Message t.1) × AmbientPairMessage UB (pred.decoded t.1 m) H q t.2
noncomputable def finiteNodeDecoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t) : Finset (ℙ K (Dual K V)) × Finset (ℙ K V) :=
  ambientPairDecoded UB (pred.decoded t.1 m.1) H q t.2 m.2
noncomputable def finiteNodeEncoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q) :
    Option (FiniteNodeMessage pred UB H q t) :=
  (pred.encoded A B t.1).bind fun m=>
    if _hc : CaptureBound A UA c M (pred.decoded t.1 m) then
      (ambientPairEncoded A UA B UB (pred.decoded t.1 m) H nA nB q MA MB t.2).map (fun f=>⟨m,f⟩)
    else none
noncomputable def finiteNodeCost (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t) : ℝ :=
  pred.cost t.1 m.1+ambientPairCost UB (pred.decoded t.1 m.1) H q t.2 m.2
noncomputable def finiteNodeNextOut (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (W : Option (Finset (ℙ K V))) (t : AmbientPairTape K V H q) :
    Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V)) :=
  W.bind fun W=>if _hc : CaptureBound A UA c M W then
    (ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t)
    else none
noncomputable def finiteNodeNextLaw (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (W : Option (Finset (ℙ K V))) : Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  map (ambientPairTapeLaw H q) (finiteNodeNextOut A UA B UB H nA nB q MA MB c M W)
noncomputable def finiteNodeOutput (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  map (finiteNodeTapeLaw pred H q) (fun t=>
    (finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t).map (finiteNodeDecoded pred UB H q t))

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_exact (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q) :
    (finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t).map (finiteNodeDecoded pred UB H q t)=
      finiteNodeNextOut A UA B UB H nA nB q MA MB c M ((pred.encoded A B t.1).map (pred.decoded t.1)) t.2 := by
  cases hm : pred.encoded A B t.1 with
  | none => simp [finiteNodeEncoded,hm,finiteNodeNextOut]
  | some m =>
    simp only [finiteNodeEncoded,hm,Option.bind_some,Option.map_some,finiteNodeNextOut]
    split_ifs <;> simp only [Option.map_none,Option.map_map,Function.comp_def,finiteNodeDecoded]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) :
    finiteNodeOutput pred A UA B UB H nA nB q MA MB c M=
      optionCompose (pred.output A B) (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) := by
  rw [optionCompose_eq_second _ _ (by exact map_const _ none)]
  unfold finiteNodeOutput
  simp only [finiteNode_exact]
  exact public_composition pred.tapeLaw (ambientPairTapeLaw H q)
    (fun t=>(pred.encoded A B t).map (pred.decoded t))
    (finiteNodeNextOut A UA B UB H nA nB q MA MB c M)
    (finiteNodeNextLaw A UA B UB H nA nB q MA MB c M) (fun _=>rfl)

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_prefixes (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    pred.encoded A B t.1=some m.1 ∧ CaptureBound A UA c M (pred.decoded t.1 m.1) ∧
    ambientPairEncoded A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2=some m.2 := by
  unfold finiteNodeEncoded at hm
  cases hf : pred.encoded A B t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hc : CaptureBound A UA c M _ then _ else none)=some m at hm
    split_ifs at hm with hc
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hc,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
