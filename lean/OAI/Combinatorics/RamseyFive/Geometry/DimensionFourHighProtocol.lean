import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FiniteFamily

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_protocol {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    let _hyperQueries := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
    let _flatQueries := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
        100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p₀ := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
      (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/40) 10 R L₀ c t).map
        (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
    p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/40:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_four_high_public_law hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover
  let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
  let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
  change (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) → _
  intro hsmallH hsmallP
  obtain ⟨hcost,hN,code,hfail,hgood⟩ := hh D b τ g R L₀ q K I J F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover hsmallH hsmallP
  have hXHX : XH⊆X := peel_subset _ _ _ _ _ _ _
  have hSXH : S⊆XH := peel_subset _ _ _ _ _ _ _
  have hSX : S⊆X := hSXH.trans hXHX
  have hretH : X.card≤2*XH.card := peel_half _ _ _ _ _ _ _
  have hretP : XH.card≤2*S.card := peel_half _ _ _ _ _ _ _
  have hret : X.card≤4*S.card := by omega
  have hSn : (0:ℝ)<S.card := by
    have hh : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
    nlinarith only [hh,hX,Real.exp_pos (2*σ+g)]
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

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction ReverseCap
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
theorem eventually_four_local_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
      [∀x : ℙ K (Fin 5→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 5→K))) (T UT : Finset (ℙ K (Dual K (Fin 5→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      ∃br : FourPublicIndex K σ,
        let pred := fourLocalPredictor U UT σ (P η σ D R) τ R L₀ br
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_four_low_protocol hη hη' Cb hCb,
    eventually_four_high_protocol hη hη' Cb hCb,
    eventually_plane_public hη hη' Cb hCb,
    eventually_three_flat_finite_predictor hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hlow hhigh hplane hthree hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  have hσ1 : 1≤σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ1 (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hd : finrank K (Fin 5→K)=5 := by simp
  have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
  have hX : X.Nonempty := by
    have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^5*Real.exp (-b)) hprod
    exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
  have hτ400 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1
    (by have := beta_pos hη;linarith : -800*beta η≤-400*beta η))
  have hτ200 := hτ400.trans (Real.rpow_le_rpow_of_exponent_le hσ1
    (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
  let F := flatIndices (K:=K) (V:=Fin 5→K) 3
  have hF : F.Nonempty := flatIndices_nonempty 3 (by omega)
  let Flat := flatEnumeration (K:=K) (V:=Fin 5→K)
  have hFlat : ∀j∈F,finrank K (Flat j)=3 := flatIndices_rank 3
  have hcover : ∀A : Submodule K (Fin 5→K),finrank K A=3 → ∃j∈F,Flat j=A := flatIndices_cover 3
  let H := flatIndices (K:=K) (V:=Fin 5→K) 4
  have hH : H.Nonempty := flatIndices_nonempty 4 (by omega)
  let Hyper := flatEnumeration (K:=K) (V:=Fin 5→K)
  have hHyper : ∀j∈H,finrank K (Hyper j)=4 := flatIndices_rank 4
  have hHcover : ∀A : Submodule K (Fin 5→K),finrank K A=4 → ∃j∈H,Hyper j=A := flatIndices_cover 4
  let : Finite (Dual K (Dual K (Fin 5→K))) := Module.finite_of_finite K
  let : Fintype (ℙ K (Dual K (Dual K (Fin 5→K)))) := Fintype.ofFinite _
  have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := by
    exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr
      (by simpa only [one_mul] using (show (X.card:ℝ)≤U.card from by exact_mod_cast Finset.card_le_card hXU)))
  have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := by
    exact Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr
      (by simpa only [one_mul] using (show (T.card:ℝ)≤UT.card from by exact_mod_cast Finset.card_le_card hTU)))
  have hcost_le (C : ℝ) (hC : 0≤C) (hC' : C≤30000) :
      C*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R)≤
      30000*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' hqpos.le) (by linarith)) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have plane_branch : ∀a∈F,(X.card:ℝ)≤100*(X∩flatPoints (Flat a)).card →
      ∃br : FourPublicIndex K σ,
        let pred := fourLocalPredictor U UT σ (P η σ D R) τ R L₀ br
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
    intro a ha hlarge
    let : Finite (Dual K (Flat a)) := Module.finite_of_finite K
    let : ∀ x : ℙ K (Flat a),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
    let : ∀ x : ℙ K (Dual K (Flat a)),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
    obtain ⟨k,hk,hf,hg,hc⟩ := hplane D b τ R L₀ K (Fin 5→K) (Flat a) X U T UT
      (hFlat a ha) (by omega) hq hr hL hb hbhi hτ hτ400 hX hT hXU hTU hdens (by simpa only [hd] using hprod) hlarge
    have hk' : k≤Nat.log 2 ((Nat.card K)^2) := by simpa only [hd,hFlat a ha,Nat.reduceSub] using hk
    refine ⟨.inr (.inr (.inl (⟨a,ha⟩,⟨k,Nat.lt_succ_of_le hk'⟩))),?_,?_,?_⟩
    · exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
    · intro W hW
      obtain ⟨hWU,hsize,hcap⟩ := hg W hW
      refine ⟨hWU,hsize.trans ?_,?_⟩
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/100000:ℝ)≤9/1000) (Nat.cast_nonneg _)).trans hcap
    · intro t m hm
      have hh := hc t m hm
      have hx : 0≤(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by positivity
      change planePublicCost (Flat a) U UT (P η σ D R) τ k t m≤_
      nlinarith only [hh,hx]
  by_cases hn : (X.card:ℝ)≤100*(Nat.card K:ℝ)*P η σ D R
  · refine ⟨.inl (),?_,?_,?_⟩
    · change (map (baseTableLaw U (P η σ D R) τ R L₀) (fun t=>(baseFiniteEncoded X U (P η σ D R) τ t).map t)) none ≤ _
      rw [baseFinite_law]
      exact (baseSmallLaw X U hXU (P η σ D R) τ hP hn R L₀).1.trans (by positivity)
    · change ∀W,0 < (map (baseTableLaw U (P η σ D R) τ R L₀) (fun t=>(baseFiniteEncoded X U (P η σ D R) τ t).map t)) (some W) → _
      rw [baseFinite_law]
      intro W hW
      have hw := baseCaptureLaw_positive X U (P η σ D R) τ R L₀ W hW
      refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/100000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
    · intro t m hm
      exact (smallFinite_cost σ hσ1 hq.symm (by omega) X U hX hXU _ τ hP hn t m hm).trans (hcost_le 110 (by norm_num) (by norm_num))
  by_cases hLow : (X.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000)
  · let g := Real.log (X.card:ℝ)-3*σ/2
    have hXexp : (X.card:ℝ)=Real.exp (3*σ/2+g) := by
      dsimp only [g]
      rw [show 3*σ/2+(Real.log (X.card:ℝ)-3*σ/2)=Real.log (X.card:ℝ) by ring,Real.exp_log (by exact_mod_cast hX.card_pos)]
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    have ht : 0<t := by dsimp [t];positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    by_cases hsmall : ∀i,(C i).card≤(S.card:ℝ)/25
    · obtain ⟨_,_,hc,c,hf,hg⟩ := hlow D b τ g R L₀ q K (Fin 5) _ F hF Flat X U T
        hcard hσq (by simp) hr hL hb hbhi hτ hτ200 hXU hXT hdens hprod hXexp (lt_of_not_ge hn) hLow hFlat hcover hsmall
      let n : Fin (Fintype.card (ℙ K (Fin 5→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
      have he : map (scoreTableLaw U σ (P η σ D R) τ R L₀)
          (fun t => (scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)=
        finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
          (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/20) 10 R L₀ c t).map
            (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t)) := by
        rw [scoreFinite_law,scoredEncoded_law]
      refine ⟨.inr (.inl (true,n,c)),?_,?_,?_⟩
      · change (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) none ≤ _
        rw [he]
        exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
      · change ∀W,0 < (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) (some W) → _
        rw [he]
        intro W hW
        obtain ⟨hWU,hsize,hcap⟩ := hg W hW
        exact ⟨hWU,hsize,(mul_le_mul_of_nonneg_right (by norm_num : (9/100000:ℝ)≤9/20) (Nat.cast_nonneg _)).trans hcap⟩
      · intro t z hz
        exact (scoreFinite_cost_of_header X U n σ (P η σ D R) τ (9/20) 10 _ c hc t z hz).trans (hcost_le 100 (by norm_num) (by norm_num))
    · have hSX : S⊆X := peel_subset _ F hF _ X _ _
      have hret' : X.card≤2*S.card := peel_half _ F hF _ X _ _
      have hret : X.card≤4*S.card := by omega
      obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S X hSX hret F hF (fun j=>flatPoints (Flat j)) m hsmall
      exact plane_branch a ha hlarge
  · let g := Real.log (X.card:ℝ)-2*σ
    have hXexp : (X.card:ℝ)=Real.exp (2*σ+g) := by
      dsimp only [g]
      rw [show 2*σ+(Real.log (X.card:ℝ)-2*σ)=Real.log (X.card:ℝ) by ring,Real.exp_log (by exact_mod_cast hX.card_pos)]
    have hg : P η σ D R/10000<g := by
      have hlt := lt_of_not_ge hLow
      rw [hXexp,hq,←Real.exp_nat_mul,←Real.exp_add] at hlt
      exact (add_lt_add_iff_left (2*σ)).mp (Real.exp_lt_exp.mp hlt)
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    have ht : 0<t := by dsimp [t];positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    have hSXH : S⊆XH := peel_subset _ F hF _ XH _ _
    have hXHX : XH⊆X := peel_subset _ H hH _ X _ _
    have hSX : S⊆X := hSXH.trans hXHX
    have hret : X.card≤4*S.card := by
      have h1 : X.card≤2*XH.card := peel_half _ H hH _ X _ _
      have h2 : XH.card≤2*S.card := peel_half _ F hF _ XH _ _
      omega
    by_cases hsmallH : ∀i,(CH i).card≤(S.card:ℝ)/25
    · by_cases hsmallP : ∀i,(CP i).card≤(S.card:ℝ)/25
      · obtain ⟨_,_,hc,c,hf,hgood⟩ := hhigh D b τ g R L₀ q K (Fin 5) _ F hF Flat H hH Hyper X U T
          hcard hσq (by simp) hr hL hb hbhi hτ hτ200 hXU hXT hdens hprod hXexp (lt_of_not_ge hn) hg hFlat hcover hHyper hHcover hsmallH hsmallP
        let n : Fin (Fintype.card (ℙ K (Fin 5→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        have he : map (scoreTableLaw U σ (P η σ D R) τ R L₀)
            (fun t => (scoreFiniteEncoded X U n σ (P η σ D R) τ (9/40) 10 c t).map t)=
          finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
            (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/40) 10 R L₀ c t).map
              (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t)) := by
          rw [scoreFinite_law,scoredEncoded_law]
        refine ⟨.inr (.inl (false,n,c)),?_,?_,?_⟩
        · change (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/40) 10 c t).map t)) none ≤ _
          rw [he]
          exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
        · change ∀W,0 < (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/40) 10 c t).map t)) (some W) → _
          rw [he]
          intro W hW
          obtain ⟨hWU,hsize,hcap⟩ := hgood W hW
          exact ⟨hWU,hsize,(mul_le_mul_of_nonneg_right (by norm_num : (9/100000:ℝ)≤9/40) (Nat.cast_nonneg _)).trans hcap⟩
        · intro t z hz
          exact (scoreFinite_cost_of_header X U n σ (P η σ D R) τ (9/40) 10 _ c hc t z hz).trans (hcost_le 100 (by norm_num) (by norm_num))
      · obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S XH hSX hret F hF (fun j=>flatPoints (Flat j)) p hsmallP
        exact plane_branch a ha hlarge
    · obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S X hSX hret H hH (fun j=>flatPoints (Hyper j)) h hsmallH
      obtain ⟨k,hk,hf,hgood,hc⟩ := hthree D b τ R L₀ q K (Fin 5→K) (Hyper a) (hHyper a ha) X U T UT
        (by omega) hcard hσq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens (by simpa only [hd] using hprod) hlarge
      have hk' : k≤Nat.log 2 (Nat.card K) := by simpa only [hd,hHyper a ha,Nat.reduceSub,pow_one] using hk
      refine ⟨.inr (.inr (.inr (⟨a,ha⟩,⟨k,Nat.lt_succ_of_le hk'⟩))),?_⟩
      exact ⟨hf,hgood,hc⟩

end SharpRamseyFive.ScoreGeometry

end OAI
