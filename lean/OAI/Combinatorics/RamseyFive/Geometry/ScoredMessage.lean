import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.MetadataCodec
import OAI.Combinatorics.RamseyFive.Entropy.UniformCutoff
import OAI.Combinatorics.RamseyFive.Geometry.BasePublicFamily

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev ScoredPayload (U : Finset (ℙ K V)) (n : ℕ) (σ P τ : ℝ) :=
  TrainingCode V (listCap σ) (productCap σ) (Nat.card V) ×
    (Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1))
abbrev ScoredMessage (U : Finset (ℙ K V)) (σ P τ : ℝ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) × ScoredPayload U n σ P τ

noncomputable def scoredMessageDecoded (U : Finset (ℙ K V)) (σ P τ : ℝ)
    (R : ℕ) (L₀ : ℝ≥0) (t : BaseTape U P τ R) (m : ScoredMessage U σ P τ) :
    Finset (ℙ K V) :=
  publicDecoded U (messageOwn m.2.1) (messageBase m.2.1 L₀) m.2.2.2 (t m.1 m.2.2.1)

omit [Fintype V] in
lemma scoredMessageDecoded_inputs (U : Finset (ℙ K V)) (σ P τ : ℝ)
    (R : ℕ) (L₀ : ℝ≥0) (t : BaseTape U P τ R)
    (n : Fin (Fintype.card (ℙ K V)+1))
    (c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (i : Fin (sizeScoreCutoff U n P τ)) (z : Fin (Fintype.card (ℙ K (Dual K V))+1)) :
    scoredMessageDecoded U σ P τ R L₀ t ⟨n,c,i,z⟩=
      publicDecoded U (messageOwn c) (messageBase c L₀) z (t n i) := rfl

omit [Finite K] [FiniteDimensional K V] [Fintype V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma score_training_gap (X S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSX : S⊆X) (hXU : X⊆U) (hret : X.card≤4*S.card) :
    Real.log ((U.card:ℝ)/S.card)≤Real.log ((U.card:ℝ)/X.card)+Real.log 4 := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hx : (0:ℝ)<X.card := hs.trans_le (by exact_mod_cast Finset.card_le_card hSX)
  have hu : (0:ℝ)<U.card := hx.trans_le (by exact_mod_cast Finset.card_le_card hXU)
  have hr : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
  have hh : (U.card:ℝ)/S.card≤((U.card:ℝ)/X.card)*4 := by
    apply (div_le_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_left hr (div_nonneg hu.le hx.le)
    field_simp at hh ⊢
    nlinarith
  have hl := Real.log_le_log (div_pos hu hs) hh
  rw [Real.log_mul (div_pos hu hx).ne' (by norm_num)] at hl
  exact hl

omit [Fintype (ℙ K (Dual K V))] in

lemma projective_header_le (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)≤6*(Nat.card K:ℝ) := by
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hp : (Fintype.card (ℙ K V):ℝ)≤Nat.card V := by
    exact_mod_cast projective_card_le_vectors (Finset.univ : Finset (ℙ K V))
  have he : Real.exp (5*σ)+1≤Real.exp (6*σ) := by
    have h1 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by linarith)
    have h2 : 2≤Real.exp σ := (by linarith : (2:ℝ)≤σ+1).trans (Real.add_one_le_exp σ)
    have hx : Real.exp (6*σ)=Real.exp (5*σ)*Real.exp σ := by
      rw [←Real.exp_add];congr 1;ring
    rw [hx]
    nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1)
    (show (Fintype.card (ℙ K V)+1:ℝ)≤Real.exp (6*σ) by linarith)
  rw [Real.log_exp] at hl
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  linarith

lemma scored_cost_scalar (q P gap τ : ℝ) (hq : 2≤q) (hP : 1≤P)
    (hgap : 0≤gap) (_hτ : 0≤τ) (hτ1 : τ≤1) :
    13*q+Real.log (2*q)+(gap+Real.log 4)*(2*q*P)+(8*P*τ+Real.log 4)≤
      100*q*P*(gap+P) := by
  have hqp : 0<q := by linarith
  have hp : 0≤P := by linarith
  have hL : Real.log (2*q)≤2*q-1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (4:ℝ)≤3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4) using 1; norm_num
  have ht := mul_le_mul_of_nonneg_left hτ1 (show 0≤8*P by positivity)
  have hh := mul_le_mul_of_nonneg_right h4 (show 0≤2*q*P by positivity)
  have h₁ : q≤q*P := by nlinarith
  have h₂ : q*P≤q*P*P := by nlinarith
  have h₃ : P≤q*P := by nlinarith
  have h₄ : 0≤q*P*gap := by positivity
  nlinarith

theorem scoredMessage_cost (σ P τ : ℝ) (hσ : 100000≤σ)
    (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1)
    (X S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSX : S⊆X)
    (hXU : X⊆U) (hret : X.card≤4*S.card)
    (hN : Real.log (scoreCutoff S U P τ)≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ P τ):ℝ)≤
        100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+P) := by
  have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hp := projective_header_le σ (by linarith) hq hd
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hz := projective_header_le (K:=K) (V:=Dual K V) σ (by linarith) hq (by simpa using hd)
  have hc := log_card_training_le (V:=V) σ hσ (vector_card_le_exp σ hq hd)
  rw [hq] at hc
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hx : (0:ℝ)<X.card := hs.trans_le (by exact_mod_cast Finset.card_le_card hSX)
  have hgap : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg ((le_div_iff₀ hx).mpr (by
    simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
  have hg := score_training_gap X S U hS hSX hXU hret
  have hn0 : (0:ℝ)<scoreCutoff S U P τ := by exact_mod_cast scoreCutoff_pos S U P τ
  have hc0 : (0:ℝ)<Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) := by
    exact_mod_cast Nat.card_pos (α:=TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
  have hcard : Real.log (Fintype.card (ScoredPayload U S.card σ P τ):ℝ)=
      Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))+
      (Real.log (scoreCutoff S U P τ)+Real.log (Fintype.card (ℙ K (Dual K V))+1:ℝ)) := by
    have he : sizeScoreCutoff U S.card P τ=scoreCutoff S U P τ := rfl
    simp only [ScoredPayload,Fintype.card_prod,Fintype.card_fin,he,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [←Nat.card_eq_fintype_card (α:=TrainingCode V (listCap σ) (productCap σ) (Nat.card V))]
    rw [Real.log_mul (by exact hc0.ne') (mul_ne_zero hn0.ne' (by positivity)),
      Real.log_mul hn0.ne' (by positivity)]
  rw [hcard]
  have hg' := mul_le_mul_of_nonneg_right hg (show 0≤2*(Nat.card K:ℝ)*P by positivity)
  have hsc := scored_cost_scalar (Nat.card K) P (Real.log ((U.card:ℝ)/X.card)) τ hq2 hP hgap hτ hτ1
  unfold scoreSearchCost at hN
  linarith
end SharpRamseyFive.ScoreGeometry

end OAI
