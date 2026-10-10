import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.ReverseParameters
import OAI.Combinatorics.RamseyFive.Decoding.FreshPublicValidation
import OAI.Combinatorics.RamseyFive.Geometry.ScoredMessage

namespace OAI

namespace SharpRamseyFive.ReverseCap
open Module ScoreGeometry Metadata ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in
lemma projective_enclosure_gap (σ : ℝ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    0≤Real.log ((U.card:ℝ)/S.card) ∧ Real.log ((U.card:ℝ)/S.card)≤5*σ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hs1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hsu : (S.card:ℝ)≤U.card := by exact_mod_cast Finset.card_le_card hSU
  have hu : (0:ℝ)<U.card := hs.trans_le hsu
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hU : (U.card:ℝ)≤Nat.card V := by exact_mod_cast projective_card_le_vectors U
  have hdiv : (U.card:ℝ)/S.card≤Real.exp (5*σ) :=
    (div_le_self hu.le hs1).trans (hU.trans hv)
  refine ⟨Real.log_nonneg ((le_div_iff₀ hs).mpr (by simpa using hsu)),?_⟩
  simpa only [Real.log_exp] using Real.log_le_log (div_pos hu hs) hdiv

omit [Fintype (ℙ K (Dual K V))] in
lemma reverseLength_universal_bound (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2 := by
  have hs := projective_enclosure_gap σ hq hd S U hS hSU
  have hq1 : (1:ℝ)≤Nat.card K := by rw [←hq];exact Real.one_le_exp_iff.mpr (by linarith)
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  have hn := (reverseLength_spec (Nat.card K) _ hq1 hs.1).2.2
  have hgb : Real.log ((U.card:ℝ)/S.card)+1≤6*(Nat.card K:ℝ) := by linarith only [hs.2,hσq,hq1]
  have hm := mul_le_mul_of_nonneg_left hgb (show (0:ℝ)≤21*(Nat.card K:ℝ) by positivity)
  have hres : (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)):ℝ)≤1000*(Nat.card K:ℝ)^2 := by
    nlinarith only [hn,hm,sq_nonneg (Nat.card K:ℝ)]
  exact_mod_cast hres

lemma length_header_cost (q : ℕ) (hq : 1≤q) :
    Real.log (1000*q^2+1:ℝ)≤1002*(q:ℝ) := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hq0 : (0:ℝ)<q := by linarith
  have hb : (1000*q^2+1:ℝ)≤1001*(q:ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<1000*q^2+1) hb
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),Real.log_pow] at hl
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1001)
  have hlog := Real.log_le_sub_one_of_pos hq0
  norm_num at hl
  linarith

lemma general_reverse_cost_scalar (q P gap c B n : ℝ) (hq : 1≤q) (hP : 1≤P)
    (hg : 0≤gap) (hc : 0<c) (hc1 : c≤1) (hB : 0≤B)
    (hn : 0≤n) (hnhi : n≤21*q*(gap+1)) :
    1008*q+Real.log (2*q)-Real.log ((9:ℝ)/10)+n*(B*P-Real.log c)≤
      (1010+21*(B-Real.log c))*q*P*(gap+P) := by
  have hq0 : 0<q := by linarith
  have hP0 : 0≤P := by linarith
  have hlc : Real.log c≤0 := Real.log_nonpos hc.le hc1
  have hln := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/10)
  norm_num at hln
  have hlq := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hcP : B*P-Real.log c≤(B-Real.log c)*P := by nlinarith only [hP,hlc]
  have hnP := mul_le_mul_of_nonneg_left hcP hn
  have hnn := mul_le_mul_of_nonneg_right hnhi (mul_nonneg (by linarith : 0≤B-Real.log c) hP0)
  have hBc : 0≤B-Real.log c := by linarith
  have hgg := mul_le_mul_of_nonneg_left (by linarith : gap+1≤gap+P)
    (show 0≤21*q*(B-Real.log c)*P by positivity)
  have hqp : q≤q*P := by nlinarith
  have hqpp : q*P≤q*P*(gap+P) := by nlinarith
  nlinarith only [hlq,hln,hnP,hnn,hgg,hqp,hqpp]

theorem general_reverse_message_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT W : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (c B P : ℝ) (hc : 0<c) (hc1 : c≤1) (hB : 0≤B) (hP : 1≤P)
    (hv : CaptureBound T UT c ((T.card:ℝ)*Real.exp (B*P)) W) :
    let n := reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))
    Real.log (1000*(Nat.card K)^2+1:ℝ)+Real.log (W.card+1:ℝ)+
      Real.log (Fintype.card (Fin (cardCutoff (Nat.card K) (T∩W).card W.card n)):ℝ)≤
      (1010+21*(B-Real.log c))*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hgap := projective_enclosure_gap σ hq hd S U hS hSU
  have hlen := (reverseLength_spec (Nat.card K) _ hq1 hgap.1).2.2
  have hhead := length_header_cost (Nat.card K) (Nat.card_pos (α:=K))
  have hproj := projective_header_le (K:=K) (V:=Dual K V) σ hσ hq (by simpa using hd)
  have hWhead : Real.log (W.card+1:ℝ)≤6*(Nat.card K:ℝ) := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (Finset.card_le_univ W) 1)).trans hproj
  have hcost := general_reverse_payload T UT W hT c B P hc hv (Nat.card K) hq1
    (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)))
  have hh := general_reverse_cost_scalar (Nat.card K) P _ c B _ hq1 hP hgap.1 hc hc1 hB
    (Nat.cast_nonneg _) hlen
  dsimp only
  linarith
end SharpRamseyFive.ReverseCap

end OAI
