import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.ScoreDegreeLowNormalized

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma training_line_card (X : Finset {y : ℙ K V // x≠y}) (l : RadialLine x) :
    (RadialLine.trainingOnLine X l).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let f (y : RadialLine.trainingOnLine X l) : {p : ℙ K V // p.submodule ≤ l.val} :=
    ⟨y.val.val,(Finset.mem_filter.mp y.property).2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {p : ℙ K V // p.submodule ≤ l.val} => u.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [card_subspacePoints,l.property.1,Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  simpa [Finset.sum_range_succ,Nat.add_comm] using hc

theorem score_degree_uniform_normalized (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n a χ : ℝ) (hn : 0 < n) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hm : mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcap : n ≤ (Nat.card K:ℝ)^3) (hscale : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ)) :
    ((Finset.univ.filter fun H' : F => H≠H' ∧ a ≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0 < Nat.card K)
  by_cases hsmall : a ≤ 2*(δ:ℝ)*((Nat.card K:ℝ)+1)
  · apply ScoreScalars.normalized_degree_small (C := 16) (zero_lt_one.trans_le hq) hn ha ha2 hcap ?_ (by convert hchi using 1; norm_num)
      (ScoreScalars.degree_power_two_hundred hq (mass_nonneg _ _) hm ha
        (score_degree_four x hdim X δ hδ F hF H a ha))
    · calc
        n*a ≤ n*(2*(δ:ℝ)*((Nat.card K:ℝ)+1)) := mul_le_mul_of_nonneg_left hsmall hn.le
        _ = 2*(n*(δ:ℝ))*((Nat.card K:ℝ)+1) := by ring
        _ ≤ 2*(4*Nat.card K)*(2*Nat.card K) := mul_le_mul
          (mul_le_mul_of_nonneg_left hscale (by norm_num)) (by linarith) (by positivity) (by positivity)
        _ = 16*(Nat.card K:ℝ)^2 := by ring
  · apply ScoreScalars.normalized_degree_truncated hq hn ha ha2 hcap
        (le_trans (by norm_num) hchi)
    have hline (l : RadialLine x) : (radialWeight x X δ l:ℝ) < a/2 := by
      have hc := mul_le_mul_of_nonneg_left (show ((RadialLine.trainingOnLine X l).card:ℝ) ≤
        (Nat.card K:ℝ)+1 by exact_mod_cast training_line_card x X l) δ.coe_nonneg
      have hh : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*((Nat.card K:ℝ)+1) := by
        simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hc
      linarith
    have hd := score_degree_truncated x hdim X δ hδ F hF H a ha hline
    have hs : (mass (radialWeight x X δ) (pencilLines x F H))^2 ≤ 4 := by
      have h0 := mass_nonneg (radialWeight x X δ) (pencilLines x F H)
      nlinarith
    apply hd.trans
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem score_row_uniform_moment (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n χ : ℝ) (hn : 0 < n)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcap : n ≤ (Nat.card K:ℝ)^3) (hscale : n*(δ:ℝ) ≤ 4*Nat.card K)
    (hchi : (208*2^198:ℝ) ≤ Real.exp (2*χ)) :
    (∑ H',offRow x X δ F H H'^200) ≤
      2^200*(Nat.clog 2 X.card+1)*(((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) := by
  apply (moment_polynomial_tail _ (fun i : ℕ => (δ:ℝ)*2^i)
    (boundedOverlapDyads x X δ 2) 200 (by norm_num)
    (((Nat.card K:ℝ)^4/n)*Real.exp (2*χ)) (offRow_nonneg x X δ F H)
    (by intro i _; positivity) (offRow_bounded_cover x X δ hδ F hF 2 hm H) ?_).trans
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast boundedOverlapDyads_card x X δ 2) (by positivity)) (by positivity)
  intro i hi
  have ha : 0 < (δ:ℝ)*2^i := by positivity
  have he : (Finset.univ.filter (fun H' : F => (δ:ℝ)*2^i ≤ offRow x X δ F H H'))=
      Finset.univ.filter (fun H' : F => H≠H' ∧ (δ:ℝ)*2^i ≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) := by
    apply Finset.filter_congr
    intro H' _
    by_cases h : H=H'
    · simp [offRow,h,not_le.mpr ha]
    · simp [offRow,h]
  rw [he]
  exact score_degree_uniform_normalized x hdim X δ hδ F hF H n _ χ hn ha.le
    (Finset.mem_filter.mp hi).2 (hm H) hcap hscale hchi

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def highCertificateMajorant (Q M B b L : ℝ) (p R k N₂ : ℕ) : ℝ :=
  B*(1+(((p:ℝ)*(Q*p)/B)/b^8+
    ((p:ℝ)^3*(N₂*p)*((k:ℝ)*p+R*(2*L))^2/B)*b+
    (p:ℝ)^2*((p:ℝ)^2*((R*L)^k*M+Q*(R*(2*L))^k))/B^2))

lemma highCertificateMajorant_nonneg (Q M B b L : ℝ) (p R k N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hB : 0 ≤ B) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ highCertificateMajorant Q M B b L p R k N₂ := by
  unfold highCertificateMajorant
  positivity

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in

theorem score_high_certificate_majorant (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p R k N₂ : ℕ) (Q M B b : ℝ)
    (hB : 0 < B) (_hb : 0 ≤ b) (hQ : (F.card:ℝ) ≤ Q) (_hM : 0 ≤ M)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : F × Fin p => pencilLines x F z.1) (fun l => L*radialWeight x X δ l)
      B b (2*(L:ℝ)) k 0 (N₂*p) false) ≤
      highCertificateMajorant Q M B b L p R k N₂ := by
  have hmass (H : F) : (∑ l∈pencilLines x F H,((L*radialWeight x X δ l:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using hh
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg F.card).trans hQ
  have hpair := SingletonEnumeration.pairMoment_labelled_le (V := Fin p) (B := Fin R)
    (pencilLines x F) (fun l => L*radialWeight x X δ l) k (2*(L:ℝ)) (by positivity) hmass
  simp only [Fintype.card_fin,Fintype.card_coe] at hpair
  rw [certificate_pair_eq_power] at hpair
  have hpair' : pairMoment (B := Fin R) (fun z : F × Fin p => pencilLines x F z.1)
      (fun l => L*radialWeight x X δ l) k ≤
      (p:ℝ)^2*(((R:ℝ)*(L:ℝ))^k*M+Q*((R:ℝ)*(2*(L:ℝ)))^k) := by
    apply hpair.trans
    gcongr
  unfold highCertificateMajorant
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply add_le_add_right
  unfold branchingBound uniformAnchorBudget
  simp only [Bool.false_eq_true,ite_false,add_zero,Fintype.card_fin,Fintype.card_prod,Fintype.card_coe,
    Nat.cast_mul]
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
