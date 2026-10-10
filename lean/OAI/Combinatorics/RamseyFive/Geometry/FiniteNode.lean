import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FiniteNodeCost

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Metadata Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_finite_node {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → A⊆UA → B⊆UB → A.card≤B.card →
      (Nat.card K:ℝ)*(incidences A B:ℝ)≤τ*A.card*B.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card →
      ∃(hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))≤1000*(Nat.card K)^2)
       (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))≤1000*(Nat.card K)^2),
        let pred := fourFinitePredictor hd σ UA UB (P η σ D R) τ R L₀
        let H := 1000*(Nat.card K)^2
        let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
        let MB := (320/((9:ℝ)/100000)+320)*(Nat.card K:ℝ)^5/A.card
        let p := finiteNodeOutput pred A UA B UB H ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
          (Nat.card K) MA MB (9/100000) ((A.card:ℝ)*Real.exp (10*P η σ D R))
        p none≤5*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀Y Z,0<p (some (Y,Z))→
          ValidCap B UB MB (UB∩Y) ∧ ValidCap A UA MA (UA∩Z) ∧
          (incidences (UA∩Z) (UB∩Y):ℝ)≤
            2*((320/((9:ℝ)/10)+320)*(320/((9:ℝ)/100000)+320))*(Nat.card K:ℝ)^4*Real.exp b) ∧
        (∀t m,finiteNodeEncoded pred A UA B UB H ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩
          (Nat.card K) MA MB (9/100000) ((A.card:ℝ)*Real.exp (10*P η σ D R)) t=some m →
          finiteNodeCost pred UB H (Nat.card K) t m≤
            (32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10)))*(Nat.card K:ℝ)*(P η σ D R)*
              (Real.log ((UA.card:ℝ)/A.card)+Real.log ((UB.card:ℝ)/B.card)+(P η σ D R))) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-800*beta η)<(9:ℝ)/100000000 := by
    have hp : 0<800*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const (by norm_num : (0:ℝ)<9/100000000)
  have hc := eventually_power_absorption hη hη' (320/((9:ℝ)/100000)+320) 0 1
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_four_finite_predictor hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,hc,ht,eventually_ge_atTop (10:ℝ)] with σ hh hv hc ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ hd A UA B UB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hq3 : 3≤Nat.card K := by
    have he : (3:ℝ)≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
    rw [←hq] at he
    exact_mod_cast he
  have hab : 0<(A.card:ℝ)*B.card := lt_of_lt_of_le (by rw [hq];positivity) hprod
  have hA : A.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hab (Nat.cast_nonneg _)))
  have hB : B.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_right hab (Nat.cast_nonneg _)))
  have hσ1 : 1≤σ := by linarith only [hσ]
  have hnA := reverseLength_universal_bound σ hσ1 hq.symm (by omega : finrank K V≤5) A UA hA hAU
  have hnB := reverseLength_universal_bound σ hσ1 hq.symm (show finrank K (Dual K V)≤5 by simpa using hd.le) B UB hB hBU
  refine ⟨hnA,hnB,?_⟩
  let pred := fourFinitePredictor hd σ UA UB (P η σ D R) τ R L₀
  let H := 1000*(Nat.card K)^2
  let nA : Fin (H+1) := ⟨_,Nat.lt_succ_of_le hnA⟩
  let nB : Fin (H+1) := ⟨_,Nat.lt_succ_of_le hnB⟩
  let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
  let MB := (320/((9:ℝ)/100000)+320)*(Nat.card K:ℝ)^5/A.card
  let next := finiteNodeNextLaw A UA B UB H nA nB (Nat.card K) MA MB (9/100000)
    ((A.card:ℝ)*Real.exp (10*P η σ D R))
  obtain ⟨hf,hgood,hcost⟩ := hh D b τ R L₀ q K V hd A UA B UB hcard hσq hr hL hb hbhi hτ hτhi hAU hBU hAB hdens hprod
  have hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/100000*A.card*B.card := by
    have hτc : 1000*τ≤(9:ℝ)/100000 := by linarith only [hτhi,ht]
    have h1 := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
    have h2 := mul_le_mul_of_nonneg_right hτc (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    nlinarith only [h1,h2]
  have hnext (W) (hW : 0<pred.output A B (some W)) : next (some W)=producedPairLaw A UA B UB hB (9/100000) (some W) :=
    finiteNodeNextLaw_produced A UA B UB hA hB (9/100000) _ (by norm_num) W (hgood W hW) H _ _
  have hs (W) (hW : 0<pred.output A B (some W)) :=
    producedPairLaw_spec hd hq3 A UA B UB hA hB hAU hBU (9/100000) _ (by norm_num) (by norm_num) W (hgood W hW) hsparse
  change finiteNodeOutput pred A UA B UB H nA nB (Nat.card K) MA MB _ _ none≤_ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · rw [finiteNode_law]
    have hfresh : ∀W,0<pred.output A B (some W)→next (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) := by
      intro W hW
      rw [hnext W hW]
      exact (hs W hW).1
    have hh := optionCompose_failure (pred.output A B) next (3*Real.exp (-(Nat.card K:ℝ)))
      (2*Real.exp (-(Nat.card K:ℝ))) (by positivity) hf hfresh
    simpa only [show (3:ℝ)*Real.exp (-(Nat.card K:ℝ))+2*Real.exp (-(Nat.card K:ℝ))=5*Real.exp (-(Nat.card K:ℝ)) by ring] using hh
  · intro Y Z hYZ
    rw [finiteNode_law] at hYZ
    obtain ⟨W,hW,hout⟩ := optionCompose_positive (pred.output A B) next (Y,Z) hYZ
    rw [hnext W hW] at hout
    obtain ⟨hy,hz⟩ := (hs W hW).2 Y Z hout
    exact ⟨hy,hz,validated_caps_flags hd A UA (UA∩Z) B UB (UB∩Y) hA hB (9/100000) b (by norm_num) hb hprod hz hy⟩
  · intro t m hm
    have hτ200 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1 (by have := beta_pos hη;linarith : -800*beta η≤-200*beta η))
    obtain ⟨hP,hbP,_⟩ := hv D R b τ hr hbhi hτ.le hτ200
    have hcoef : 320/((9:ℝ)/100000)+320≤Real.exp (P η σ D R) := by
      simpa only [Real.rpow_zero,mul_one,one_mul] using hc D R hr
    have hh := finiteNode_cost pred σ hσ1 hq.symm hd.le A UA B UB hA hAU hB hBU
      (9/100000) (P η σ D R) b 30100 (by norm_num) (by norm_num) hP hbP hprod hcoef hcost hnA hnB t m hm
    norm_num only [show (30100:ℝ)+2020=32120 by norm_num] at hh
    exact hh
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def OriginalNodeReady (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) : Prop :=
  δ*A₀.card≤(A₀∩UA).card ∧ δ*B₀.card≤(B₀∩UB).card ∧
    (Nat.card K:ℝ)*incidences A₀ B₀≤τ*A₀.card*B₀.card

lemma nonempty_of_positive_trim {α : Type*} (A A₀ : Finset α) (hA₀ : A₀.Nonempty)
    (δ : ℝ) (hδ : 0<δ) (htrim : δ*A₀.card≤A.card) : A.Nonempty := by
  exact Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le
    (mul_pos hδ (by exact_mod_cast hA₀.card_pos)) htrim))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma original_ready_sparse (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (c δ τ : ℝ) (hc : 0≤c) (hδ : 0≤δ) (hτ : 1000*τ≤c*δ^2)
    (hr : OriginalNodeReady A₀ UA B₀ UB δ τ) :
    1000*(Nat.card K:ℝ)*incidences (A₀∩UA) (B₀∩UB)≤c*(A₀∩UA).card*(B₀∩UB).card := by
  have hi : incidences (A₀∩UA) (B₀∩UB)≤ incidences A₀ B₀ := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.product_subset_product Finset.inter_subset_left Finset.inter_subset_left
  have hp := mul_le_mul hr.1 hr.2.1 (mul_nonneg hδ (Nat.cast_nonneg B₀.card))
    (Nat.cast_nonneg (A₀∩UA).card)
  have hp' : δ^2*(A₀.card:ℝ)*B₀.card≤(A₀∩UA).card*(B₀∩UB).card := by nlinarith only [hp]
  have h₁ := mul_le_mul_of_nonneg_left (show (incidences (A₀∩UA) (B₀∩UB):ℝ)≤ incidences A₀ B₀ by exact_mod_cast hi)
    (show (0:ℝ)≤1000*(Nat.card K:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hr.2.2 (by norm_num : (0:ℝ)≤1000)
  have h₃ := mul_le_mul_of_nonneg_right hτ (show (0:ℝ)≤(A₀.card:ℝ)*B₀.card by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hp' hc
  nlinarith only [h₁,h₂,h₃,h₄]

noncomputable def guardedNodeLaw (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Fintype V := Fintype.ofFinite _
  letI : Finite (Dual K V) := Module.finite_of_finite K
  letI : Fintype (Dual K V) := Fintype.ofFinite _
  letI : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  exact if hr : OriginalNodeReady A₀ UA B₀ UB δ τ then
    let hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    let hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    let hnA := reverseLength_universal_bound σ hσ hq hd (A₀∩UA) UA hA Finset.inter_subset_right
    let hnB := reverseLength_universal_bound σ hσ hq (show finrank K (Dual K V)≤5 by simpa using hd)
      (B₀∩UB) UB hB Finset.inter_subset_right
    finiteNodeOutput pred (A₀∩UA) UA (B₀∩UB) UB (1000*(Nat.card K)^2)
      ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card) c M
  else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
