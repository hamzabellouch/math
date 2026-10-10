import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ScoreFiniteCost
import OAI.Combinatorics.RamseyFive.Geometry.PlanePublicDefs

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

abbrev ThreePublicIndex (K : Type) [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] (σ : ℝ) :=
  ThreeBranch (K:=K) (I:=Fin 4) σ (flatIndices (K:=K) (V:=Fin 4→K) 3)

noncomputable def ThreeLocalTape (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) : ThreePublicIndex K σ→Type _
  | .inl _ => BaseTable U P τ
  | .inr (.inl _) => ScoreTable U σ P τ
  | .inr (.inr a) => PlanePublicTape (flatEnumeration a.1.1) U UT P τ a.2
noncomputable instance (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ) :
    Fintype (ThreeLocalTape U UT σ P τ br) := by
  rcases br with b|b
  · dsimp only [ThreeLocalTape];infer_instance
  · rcases b with b|b <;> dsimp only [ThreeLocalTape] <;> infer_instance

noncomputable def ThreeLocalMessage (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→ThreeLocalTape U UT σ P τ br→Type _
  | .inl _,_ => BaseMessage U P τ
  | .inr (.inl _),_ => ScoredMessage U σ P τ
  | .inr (.inr a),t => PlanePublicMessage (flatEnumeration a.1.1) U UT P τ a.2 t

noncomputable def threeLocalLaw (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (br : ThreePublicIndex K σ)→Law (ThreeLocalTape U UT σ P τ br)
  | .inl _ => baseTableLaw U P τ R L₀
  | .inr (.inl _) => scoreTableLaw U σ P τ R L₀
  | .inr (.inr a) => planePublicLaw (flatEnumeration a.1.1) U UT P τ R L₀ a.2

noncomputable def threeLocalDecoded (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      ThreeLocalMessage U UT σ P τ br t→Finset (ℙ K (Fin 4→K))
  | .inl _,t,m => t m
  | .inr (.inl _),t,m => t m
  | .inr (.inr a),t,m => planePublicDecoded (flatEnumeration a.1.1) U UT P τ a.2 t m

noncomputable def threeLocalEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      Option (ThreeLocalMessage U UT σ P τ br t)
  | .inl _,t => baseFiniteEncoded X U P τ t
  | .inr (.inl c),t => scoreFiniteEncoded X U c.1 σ P τ (9/20) 10 c.2 t
  | .inr (.inr a),t => planePublicEncoded (flatEnumeration a.1.1) X U T UT P τ a.2 t

noncomputable def threeLocalCost (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      ThreeLocalMessage U UT σ P τ br t→ℝ
  | .inl _,_,m => baseFiniteCost U P τ m
  | .inr (.inl _),_,m => scoreFiniteCost U σ P τ m
  | .inr (.inr a),t,m => planePublicCost (flatEnumeration a.1.1) U UT P τ a.2 t m

abbrev ThreePublicTape (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :=
  (br : ThreePublicIndex K σ)→ThreeLocalTape U UT σ P τ br
noncomputable def threePublicLaw (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ThreePublicTape U UT σ P τ) := piLaw (threeLocalLaw U UT σ P τ R L₀)
abbrev ThreePublicMessage (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (t : ThreePublicTape U UT σ P τ) :=
  (br : ThreePublicIndex K σ)×ThreeLocalMessage U UT σ P τ br (t br)
noncomputable def threePublicEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ)
    (t : ThreePublicTape U UT σ P τ) : Option (ThreePublicMessage U UT σ P τ t) :=
  branchEncoded br (threeLocalEncoded X U T UT σ P τ br) t
noncomputable def threePublicDecoded (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) (m : ThreePublicMessage U UT σ P τ t) : Finset (ℙ K (Fin 4→K)) :=
  branchDecoded (threeLocalDecoded U UT σ P τ) t m
noncomputable def threePublicCost (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) (m : ThreePublicMessage U UT σ P τ t) : ℝ :=
  Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)+threeLocalCost U UT σ P τ m.1 (t m.1) m.2

lemma threePublic_law (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (br : ThreePublicIndex K σ) :
    map (threePublicLaw U UT σ P τ R L₀)
      (fun t=>(threePublicEncoded X U T UT σ P τ br t).map (threePublicDecoded U UT σ P τ t))=
    map (threeLocalLaw U UT σ P τ R L₀ br)
      (fun t=>(threeLocalEncoded X U T UT σ P τ br t).map (threeLocalDecoded U UT σ P τ br t)) :=
  branch_output_law _ br _ _
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_small_protocol {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
    Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
        100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
      (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/20) 10 R L₀ c t).map
        (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
    p none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/20:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_three_public_law hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  obtain ⟨hcost,hN,code,hfail,hgood⟩ := hh D b τ g R L₀ q K I J F hF Flat X U T
    hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover hsmall
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
    (by rw [Module.finrank_pi,hI]; norm_num) hP hτ.le hτ1 X S U hS hSX hXU (by omega) hN
  refine ⟨hcost,hN,htotal,code,?_⟩
  dsimp only
  rw [scoredEncoded_law]
  exact ⟨hfail,hgood⟩

end SharpRamseyFive.ScoreGeometry

end OAI
