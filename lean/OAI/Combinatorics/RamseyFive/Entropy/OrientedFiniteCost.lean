import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeFinitePredictor

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem orientedFinite_cost
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hdim : finrank K V≤5)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P : ℝ) (hP : 1≤P) (d : ℕ)
    (hf : S.card≤T.card → ∀t m,f.encoded S T t=some m →
      f.cost t m≤4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P))
    (hr : T.card≤S.card → ∀t m,r.encoded T (S.map bidualPoint.toEmbedding) t=some m →
      r.cost t m≤4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P))
    (t : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).Tape)
    (m : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).Message t)
    (hm : (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).encoded S T t=some m) :
    (orientedFinitePredictor f r U UT d (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10).cost t m≤
      9000*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hgs := (projective_enclosure_gap σ hq hdim S U hS hSU).1
  have hgt := (projective_enclosure_gap σ hq (by simpa using hdim) T UT hT hTU).1
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hqp : 1≤(Nat.card K:ℝ)*P := by nlinarith [mul_nonneg (show 0≤(Nat.card K:ℝ)-1 by linarith) (show 0≤P-1 by linarith)]
  have hh : 1≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) :=
    by nlinarith [mul_nonneg (show 0≤(Nat.card K:ℝ)*P-1 by linarith) (show 0≤Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P-1 by linarith)]
  have hlog2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hn := reverseLength_universal_bound σ hσ hq hdim S U hS hSU
  dsimp only [orientedFinitePredictor] at hm ⊢
  by_cases hST : S.card≤T.card
  · rw [ite_eq_left hST] at hm
    obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hb := hf hST t.1 m' hm'
    dsimp only
    nlinarith only [hb,hh,hlog2]
  · rw [ite_eq_right hST,dite_eq_left hn] at hm
    obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    obtain ⟨hpre,_,_⟩ := generalReversed_prefixes r.Message r.decoded
      (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT _ _ _ _ _ _ t.2 m' hm'
    have hb := hr (by omega) t.2.1 m'.1 hpre
    have hc := generalReversed_cost r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) r.cost
      σ hσ hq hdim S U hS hSU T UT hT P (9/1000) 10
      ((320/((9:ℝ)/1000)+320)*(Nat.card K:ℝ)^d/T.card) hP (by norm_num) (by norm_num) (by norm_num)
      hn t.2 m' hm'
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/1000)
    norm_num at hl
    have hco : 1010+21*((10:ℝ)-Real.log (9/1000))≤3600 := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hco (show 0≤(Nat.card K:ℝ)*P by positivity))
      (show 0≤Real.log ((U.card:ℝ)/S.card)+P by linarith)
    have hmon := mul_nonneg (show 0≤(Nat.card K:ℝ)*P by positivity) hgt
    dsimp only
    nlinarith only [hb,hc,hmul,hmon,hh,hlog2]
end SharpRamseyFive.ScoreGeometry

end OAI
