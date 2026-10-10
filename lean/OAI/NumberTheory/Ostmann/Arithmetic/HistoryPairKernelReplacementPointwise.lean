import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open scoped BigOperators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem flagError_eq_one_of_modular_disagreement {ι : Type*}
    (P : MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ)
    (hn : ¬ (eval₂ (Int.castRingHom (ZMod b)) (fun i => (x i : ZMod b)) P=0 ↔ P=0)) :
    flagError P x b=1 := by
  classical
  rw [Expr.eval₂_cast_int_zmod_eq_zero_iff] at hn
  by_cases hP : P=0
  · subst P
    simp only [map_zero,dvd_zero,iff_self,not_true_eq_false] at hn
  · have hd : (b:ℤ) ∣ eval x P := by tauto
    simp only [flagError,divisibilityIndicator,hP,hd,ite_true,ite_false,sub_zero,abs_one]

theorem abs_sub_le_flag_errors {ι κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ) (u v : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (heq : (∀ j, eval₂ (Int.castRingHom (ZMod b)) (fun i => (x i : ZMod b)) (P j)=0 ↔
      P j=0) → u=v) :
    |u-v| ≤ ∑ j,flagError (P j) x b := by
  classical
  by_cases hh : ∀ j, eval₂ (Int.castRingHom (ZMod b)) (fun i => (x i : ZMod b)) (P j)=0 ↔ P j=0
  · rw [heq hh,sub_self,abs_zero]
    exact Finset.sum_nonneg (fun j _ => flagError_nonneg (P j) x b)
  · obtain ⟨j,hj⟩ := not_forall.mp hh
    have hsum : 1 ≤ ∑ j,flagError (P j) x b := by
      rw [←flagError_eq_one_of_modular_disagreement (P j) x b hj]
      exact Finset.single_le_sum (fun i _ => flagError_nonneg (P i) x b) (Finset.mem_univ j)
    apply le_trans _ hsum
    exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem unit_probability_error_le (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) [Fact b.Prime] (x : PairKey h k → ℤ) :
    |PrimeLineFamilies.probability b
      (leftRows h k hs ks r b (fun i => (x i : ZMod b)))
      (rightRows h k hs ks r b (fun i => (x i : ZMod b)))-unitKernel h k hs ks r b| ≤
      ∑ j : Index h k r,flagError (polynomial h k hs ks r j) x b := by
  apply abs_sub_le_flag_errors
    (polynomial h k hs ks r) x b _ _ (unit_probability_bounds b _ _)
    (unitKernel_bounds h k hs ks r b Fact.out)
  exact fun hx => probability_eq_unitKernel h k hs ks hroot r b _ hx

theorem mixed_probability_error_le (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) [Fact b.Prime] (x : PairKey h k → ℤ) :
    |PrimeMixedLineFamilies.probability b
      (leftRows h k hs ks r b (fun i => (x i : ZMod b)))
      (rightRows h k hs ks r b (fun i => (x i : ZMod b)))-mixedKernel h k hs ks r b| ≤
      ∑ j : Index h k r,flagError (polynomial h k hs ks r j) x b := by
  apply abs_sub_le_flag_errors
    (polynomial h k hs ks r) x b _ _ (mixed_probability_bounds b _ _)
    (mixedKernel_bounds h k hs ks r b Fact.out)
  exact fun hx => probability_eq_mixedKernel h k hs ks hroot r b _ hx

def actualProbability (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x : PairKey h k → ℤ) : ℝ :=
  if hb : b.Prime then
    letI : Fact b.Prime := ⟨hb⟩
    if mixed then PrimeMixedLineFamilies.probability b
      (leftRows h k hs ks r b (fun i => (x i : ZMod b)))
      (rightRows h k hs ks r b (fun i => (x i : ZMod b)))
    else PrimeLineFamilies.probability b
      (leftRows h k hs ks r b (fun i => (x i : ZMod b)))
      (rightRows h k hs ks r b (fun i => (x i : ZMod b)))
  else 0

def symbolicKernel (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) : ℝ :=
  if mixed then mixedKernel h k hs ks r b else unitKernel h k hs ks r b

theorem actualProbability_error_le (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) (x : PairKey h k → ℤ) :
    |actualProbability mixed h k hs ks r b x-symbolicKernel mixed h k hs ks r b| ≤
      ∑ j : Index h k r,flagError (polynomial h k hs ks r j) x b := by
  have : Fact b.Prime := ⟨hb⟩
  cases mixed
  · simpa only [actualProbability,symbolicKernel,hb,dite_eq_left,Bool.false_eq_true,ite_false]
      using unit_probability_error_le h k hs ks hroot r b x
  · simpa only [actualProbability,symbolicKernel,hb,dite_eq_left,ite_true]
      using mixed_probability_error_le h k hs ks hroot r b x

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
