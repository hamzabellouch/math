import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open scoped BigOperators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open PolynomialFlagReplacementFinite MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem inv_pred_le_two_div (b : ℕ) (hb : b.Prime) :
    (((b-1:ℕ):ℝ))⁻¹ ≤ 2/(b:ℝ) := by
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb.two_le
  rw [Nat.cast_sub hb.one_lt.le,Nat.cast_one,inv_eq_one_div]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

theorem inv_le_two_div (b : ℕ) (_hb : b.Prime) : (b:ℝ)⁻¹ ≤ 2/(b:ℝ) := by
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg b)

theorem actualProbability_le_two_div (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) (x : PairKey h k → ℤ)
    (hn : ¬∀i : Fiber h k r,
      leftRows h k hs ks r b (fun j=>(x j:ZMod b)) i=0 ∧
      rightRows h k hs ks r b (fun j=>(x j:ZMod b)) i=0) :
    0 ≤ actualProbability mixed h k hs ks r b x ∧
      actualProbability mixed h k hs ks r b x ≤ 2/(b:ℝ) := by
  have : Fact b.Prime := ⟨hb⟩
  cases mixed
  · simp only [actualProbability,hb,dite_true,Bool.false_eq_true,ite_false]
    exact ⟨(unit_probability_bounds b _ _).1,
      (PrimeLineFamilies.probability_le_unit_line b _ _ hn).trans (inv_pred_le_two_div b hb)⟩
  · simp only [actualProbability,hb,dite_true,ite_true]
    exact ⟨(mixed_probability_bounds b _ _).1,
      (PrimeMixedLineFamilies.probability_le_mixed_line b _ _ hn).trans (inv_le_two_div b hb)⟩

theorem symbolicKernel_le_two_div (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) :
    0 ≤ symbolicKernel mixed h k hs ks r b ∧
      symbolicKernel mixed h k hs ks r b ≤ 2/(b:ℝ) := by
  cases mixed
  · change 0 ≤ unitKernel h k hs ks r b ∧ unitKernel h k hs ks r b ≤ _
    refine ⟨(unitKernel_bounds h k hs ks r b hb).1,?_⟩
    unfold unitKernel
    split_ifs
    · exact inv_pred_le_two_div b hb
    · positivity
  · change 0 ≤ mixedKernel h k hs ks r b ∧ mixedKernel h k hs ks r b ≤ _
    refine ⟨(mixedKernel_bounds h k hs ks r b hb).1,?_⟩
    unfold mixedKernel
    split_ifs
    · exact inv_le_two_div b hb
    · positivity

theorem actualProbability_eq_symbolicKernel_of_noAccidentalFlags (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) (x : PairKey h k → ℤ)
    (hx : NoAccidentalFlags h k hs ks r b (fun i=>(x i:ZMod b))) :
    actualProbability mixed h k hs ks r b x=symbolicKernel mixed h k hs ks r b := by
  have : Fact b.Prime := ⟨hb⟩
  cases mixed
  · simpa only [actualProbability,symbolicKernel,hb,dite_true,Bool.false_eq_true,ite_false]
      using probability_eq_unitKernel h k hs ks hroot r b _ hx
  · simpa only [actualProbability,symbolicKernel,hb,dite_true,ite_true]
      using probability_eq_mixedKernel h k hs ks hroot r b _ hx

theorem scaled_abs_sub_le_four_flag_errors {ι κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial ι ℤ) (x : ι → ℤ) (b : ℕ) (u v : ℝ)
    (hu : 0 ≤ u ∧ (b:ℝ)*u ≤ 2) (hv : 0 ≤ v ∧ (b:ℝ)*v ≤ 2)
    (heq : (∀j,eval₂ (Int.castRingHom (ZMod b)) (fun i=>(x i:ZMod b)) (P j)=0 ↔
      P j=0) → u=v) :
    (b:ℝ)*|u-v| ≤ 4*∑j,flagError (P j) x b := by
  classical
  by_cases hh : ∀j,eval₂ (Int.castRingHom (ZMod b)) (fun i=>(x i:ZMod b)) (P j)=0 ↔ P j=0
  · rw [heq hh,sub_self,abs_zero,mul_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _=>flagError_nonneg (P j) x b))
  · obtain ⟨j,hj⟩ := not_forall.mp hh
    have hsum : 1 ≤ ∑j,flagError (P j) x b := by
      rw [←flagError_eq_one_of_modular_disagreement (P j) x b hj]
      exact Finset.single_le_sum (fun i _=>flagError_nonneg (P i) x b) (Finset.mem_univ j)
    have habs : |u-v| ≤ u+v := abs_le.mpr ⟨by linarith [hu.1,hv.1],by linarith [hu.1,hv.1]⟩
    calc
      (b:ℝ)*|u-v| ≤ (b:ℝ)*(u+v) := mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg b)
      _ ≤ 4 := by nlinarith [hu.2,hv.2]
      _ ≤ 4*∑j,flagError (P j) x b := by linarith

theorem actualProbability_scaled_error_le (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) (b : ℕ) (hb : b.Prime) (x : PairKey h k → ℤ)
    (hn : ¬∀i : Fiber h k r,
      leftRows h k hs ks r b (fun j=>(x j:ZMod b)) i=0 ∧
      rightRows h k hs ks r b (fun j=>(x j:ZMod b)) i=0) :
    (b:ℝ)*|actualProbability mixed h k hs ks r b x-symbolicKernel mixed h k hs ks r b| ≤
      4*∑j : Index h k r,flagError (polynomial h k hs ks r j) x b := by
  have hp : (0:ℝ) < b := by exact_mod_cast hb.pos
  have hu := actualProbability_le_two_div mixed h k hs ks r b hb x hn
  have hv := symbolicKernel_le_two_div mixed h k hs ks r b hb
  apply scaled_abs_sub_le_four_flag_errors (polynomial h k hs ks r) x b _ _
    ⟨hu.1,by simpa only [mul_comm] using (le_div_iff₀ hp).mp hu.2⟩
    ⟨hv.1,by simpa only [mul_comm] using (le_div_iff₀ hp).mp hv.2⟩
  exact fun hx=>actualProbability_eq_symbolicKernel_of_noAccidentalFlags mixed h k hs ks hroot r b hb x hx

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
