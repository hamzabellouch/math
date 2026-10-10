import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SmallFiniteCost
import OAI.Combinatorics.RamseyFive.Geometry.ThreePublicDefs

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_local_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      ∃br : ThreePublicIndex K σ,
        let P₀ := P η σ D R
        let p := map (threeLocalLaw U UT σ P₀ τ R L₀ br)
          (fun t=>(threeLocalEncoded X U T UT σ P₀ τ br t).map (threeLocalDecoded U UT σ P₀ τ br t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threeLocalEncoded X U T UT σ P₀ τ br t=some m →
          threeLocalCost U UT σ P₀ τ br t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_small_protocol hη hη' Cb hCb,
    eventually_plane_public hη hη' Cb hCb,eventually_ge_atTop (100000:ℝ)] with σ hscore hplane hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  have hσ1 : 1≤σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ1 (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := by linarith
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hd : finrank K (Fin 4→K)=4 := by rw [Module.finrank_pi];simp
  have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
  have hX : X.Nonempty := by
    have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^4*Real.exp (-b)) hprod
    exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
  have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
      simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
  have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
      simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
  have hcost_le (C : ℝ) (hC : 0≤C) (hC' : C≤4000) :
      C*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R)≤
      4000*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' hqpos.le) hP0) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
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
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
    · intro t m hm
      exact (smallFinite_cost σ hσ1 hq.symm (by omega) X U hX hXU _ τ hP hn t m hm).trans (hcost_le 110 (by norm_num) (by norm_num))
  · let F := flatIndices (K:=K) (V:=Fin 4→K) 3
    have hF : F.Nonempty := flatIndices_nonempty 3 (by omega)
    let Flat := flatEnumeration (K:=K) (V:=Fin 4→K)
    have hFlat : ∀j∈F,finrank K (Flat j)=3 := flatIndices_rank 3
    have hcover : ∀A : Submodule K (Fin 4→K),finrank K A=3 → ∃j∈F,Flat j=A := flatIndices_cover 3
    let g := Real.log (X.card:ℝ)-3*σ/2
    have hXexp : (X.card:ℝ)=Real.exp (3*σ/2+g) := by
      dsimp only [g]
      rw [show 3*σ/2+(Real.log (X.card:ℝ)-3*σ/2)=Real.log (X.card:ℝ) by ring,Real.exp_log (by exact_mod_cast hX.card_pos)]
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    have ht : 0<t := by dsimp [t];positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    by_cases hsmall : ∀i,(C i).card≤(S.card:ℝ)/25
    · have hτhi' := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1
        (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
      obtain ⟨_,_,hc,c,hf,hg⟩ := hscore D b τ g R L₀ q K (Fin 4) _ F hF Flat X U T
        hcard hσq (by simp) hr hL hb hbhi hτ hτhi' hXU hXT hdens hprod hXexp (lt_of_not_ge hn) hFlat hcover hsmall
      let n : Fin (Fintype.card (ℙ K (Fin 4→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
      have he : map (scoreTableLaw U σ (P η σ D R) τ R L₀)
          (fun t => (scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)=
        finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
          (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/20) 10 R L₀ c t).map
            (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t)) := by
        rw [scoreFinite_law,scoredEncoded_law]
      refine ⟨.inr (.inl (n,c)),?_,?_,?_⟩
      · change (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) none ≤ _
        rw [he]
        exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
      · change ∀W,0 < (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) (some W) → _
        rw [he]
        intro W hW
        obtain ⟨hWU,hsize,hcap⟩ := hg W hW
        exact ⟨hWU,hsize,(mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/20) (Nat.cast_nonneg _)).trans hcap⟩
      · intro t z hz
        exact (scoreFinite_cost_of_header X U n σ (P η σ D R) τ (9/20) 10 _ c hc t z hz).trans (hcost_le 100 (by norm_num) (by norm_num))
    · have hSX : S⊆X := peel_subset _ F hF _ X _ _
      have hret' : X.card≤2*S.card := peel_half _ F hF _ X _ _
      have hret : X.card≤4*S.card := by omega
      obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S X hSX hret F hF (fun j=>flatPoints (Flat j)) m hsmall
      let : Finite (Dual K (Flat a)) := Module.finite_of_finite K
      let : ∀ x : ℙ K (Flat a),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
      let : ∀ x : ℙ K (Dual K (Flat a)),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
      obtain ⟨k,hk,hf,hg,hc⟩ := hplane D b τ R L₀ K (Fin 4→K) (Flat a) X U T UT
        (hFlat a ha) (by omega) hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens (by simpa only [hd] using hprod) hlarge
      have hk' : k≤Nat.log 2 (Nat.card K) := by simpa only [hd,hFlat a ha,Nat.reduceSub,pow_one] using hk
      refine ⟨.inr (.inr (⟨a,ha⟩,⟨k,Nat.lt_succ_of_le hk'⟩)),hf,?_,hc⟩
      intro W hW
      obtain ⟨hWU,hsize,hcap⟩ := hg W hW
      refine ⟨hWU,hsize.trans ?_,hcap⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
end SharpRamseyFive.ScoreGeometry

end OAI
