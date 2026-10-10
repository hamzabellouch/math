import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeFiniteOriented

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open FiniteEntropy
open scoped Classical
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
noncomputable def FinitePredictor.family (p : I→FinitePredictor A B)
    (choose : Finset A→Finset B→I) : FinitePredictor A B where
  Tape := ∀i,(p i).Tape
  tapeFintype := inferInstance
  Message := fun t=>(i : I)×(p i).Message (t i)
  messageFintype := fun _=>inferInstance
  tapeLaw := piLaw (fun i=>(p i).tapeLaw)
  decoded := branchDecoded (fun i=>(p i).decoded)
  encoded := fun S T=>branchEncoded (choose S T) ((p (choose S T)).encoded S T)
  cost := fun t m=>Real.log (Fintype.card I:ℝ)+(p m.1).cost (t m.1) m.2
lemma FinitePredictor.family_output (p : I→FinitePredictor A B)
    (choose : Finset A→Finset B→I) (S : Finset A) (T : Finset B) :
    (FinitePredictor.family p choose).output S T=(p (choose S T)).output S T := by
  unfold FinitePredictor.output FinitePredictor.family
  exact branch_output_law (fun i=>(p i).tapeLaw) (choose S T) ((p (choose S T)).encoded S T) (fun i=>(p i).decoded)
lemma FinitePredictor.family_cost (p : I→FinitePredictor A B)
    (choose : Finset A→Finset B→I) (S : Finset A) (T : Finset B) (C : ℝ)
    (hc : ∀t m,(p (choose S T)).encoded S T t=some m→(p (choose S T)).cost t m≤C)
    (t) (m) (hm : (FinitePredictor.family p choose).encoded S T t=some m) :
    (FinitePredictor.family p choose).cost t m≤Real.log (Fintype.card I:ℝ)+C := by
  obtain ⟨z,hz,rfl⟩ := branch_sent _ _ t m hm
  change Real.log (Fintype.card I:ℝ)+(p (choose S T)).cost (t (choose S T)) z≤_
  exact add_le_add (le_refl _) (hc _ _ hz)
end

section
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]
abbrev FourPublicIndex (K : Type) [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 5→K))] (σ : ℝ) :=
  FourBranch (K:=K) (I:=Fin 5) σ (flatIndices (K:=K) (V:=Fin 5→K) 3)
    (flatIndices (K:=K) (V:=Fin 5→K) 4)

noncomputable def fourLocalPredictor (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    FourPublicIndex K σ→FinitePredictor (ℙ K (Fin 5→K)) (ℙ K (Dual K (Fin 5→K)))
  | .inl _ => {
      Tape := BaseTable U P τ
      tapeFintype := inferInstance
      Message := fun _=>BaseMessage U P τ
      messageFintype := fun _=>inferInstance
      tapeLaw := baseTableLaw U P τ R L₀
      decoded := fun t=>t
      encoded := fun X _=>baseFiniteEncoded X U P τ
      cost := fun _=>baseFiniteCost U P τ }
  | .inr (.inl c) => {
      Tape := ScoreTable U σ P τ
      tapeFintype := inferInstance
      Message := fun _=>ScoredMessage U σ P τ
      messageFintype := fun _=>inferInstance
      tapeLaw := scoreTableLaw U σ P τ R L₀
      decoded := fun t=>t
      encoded := fun X _=>scoreFiniteEncoded X U c.2.1 σ P τ (if c.1 then 9/20 else 9/40) 10 c.2.2
      cost := fun _=>scoreFiniteCost U σ P τ }
  | .inr (.inr (.inl a)) => {
      Tape := PlanePublicTape (flatEnumeration a.1.1) U UT P τ a.2
      tapeFintype := inferInstance
      Message := PlanePublicMessage (flatEnumeration a.1.1) U UT P τ a.2
      messageFintype := fun _=>inferInstance
      tapeLaw := planePublicLaw (flatEnumeration a.1.1) U UT P τ R L₀ a.2
      decoded := planePublicDecoded (flatEnumeration a.1.1) U UT P τ a.2
      encoded := fun X T=>planePublicEncoded (flatEnumeration a.1.1) X U T UT P τ a.2
      cost := planePublicCost (flatEnumeration a.1.1) U UT P τ a.2 }
  | .inr (.inr (.inr a)) => threeFlatFinitePredictor (flatEnumeration a.1.1)
      (flatIndices_rank 4 a.1.1 a.1.2) σ U UT τ P R L₀ a.2
end

section
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]

def FourCertified (X U : Finset (ℙ K (Fin 5→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : FourPublicIndex K σ) : Prop :=
  let pred := fourLocalPredictor U UT σ P τ R L₀ br
  let p := pred.output X T
  p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
  (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P) ∧
    (9/100000:ℝ)*X.card≤(W∩X).card) ∧
  (∀t m,pred.encoded X T t=some m→pred.cost t m≤
    30000*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P))
noncomputable def fourCertifiedBranch (X U : Finset (ℙ K (Fin 5→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FourPublicIndex K σ :=
  if h : ∃br,FourCertified X U T UT σ P τ R L₀ br then h.choose else .inl ()
lemma fourCertifiedBranch_spec (X U : Finset (ℙ K (Fin 5→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (h : ∃br,FourCertified X U T UT σ P τ R L₀ br) :
    FourCertified X U T UT σ P τ R L₀ (fourCertifiedBranch X U T UT σ P τ R L₀) := by
  unfold fourCertifiedBranch
  rw [dite_eq_left h]
  exact h.choose_spec
noncomputable def fourCertifiedPredictor (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    FinitePredictor (ℙ K (Fin 5→K)) (ℙ K (Dual K (Fin 5→K))) :=
  FinitePredictor.family (fourLocalPredictor U UT σ P τ R L₀)
    (fun X T=>fourCertifiedBranch X U T UT σ P τ R L₀)
end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_low_protocol {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (X.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
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
    Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
        100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p₀ := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
      (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/20) 10 R L₀ c t).map
        (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
    p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/20:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_four_low_public_law hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hLow hFlat hcover
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  obtain ⟨hcost,hN,code,hfail,hgood⟩ := hh D b τ g R L₀ q K I J F hF Flat X U T
    hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hLow hFlat hcover hsmall
  have hSX : S⊆X := peel_subset _ _ _ _ _ _ _
  have hret : X.card≤2*S.card := peel_half _ _ _ _ _ _ _
  have hSn : (0:ℝ)<S.card := by
    have hh : (X.card:ℝ)≤2*S.card := by exact_mod_cast hret
    nlinarith only [hh,hX,Real.exp_pos (3*σ/2+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hτ1 : τ≤1 := hτhi.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    (by have hb' := beta_pos hη; nlinarith))
  have htotal := scoredMessage_cost σ (P η σ D R) τ hσ (hσq.trans (by rw [hcard]))
    (by rw [Module.finrank_pi,hI]) hP hτ.le hτ1 X S U hS hSX hXU (by omega) hN
  refine ⟨hcost,hN,htotal,code,?_⟩
  dsimp only
  rw [scoredEncoded_law]
  exact ⟨hfail,hgood⟩

end SharpRamseyFive.ScoreGeometry

end OAI
