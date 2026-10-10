import OAI.NumberTheory.TotientAsymptotic.PPTActualResidual
import OAI.NumberTheory.TotientAsymptotic.PPTLeadingMismatch

namespace OAI

/-! Match the chosen terminal prefix to the actual high-prime preimage list. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

/-- The unequal-list normality estimate gives every needed right index
above the middle cutoff, while the right tail is smooth below it. The
right list and first mismatch come from the actual preimage. -/
theorem ppt_preimage_terminal_prefix {k J d F : ℕ}
    (p : Fin k → ℕ) (hJ : 0 < J) (hJk : J ≤ k)
    {S U V T z ε ε' : ℝ}
    (hd : 0 < d) (hF : 0 < F)
    (hS : 2 ≤ S) (hBS : 0 ≤ B S)
    (hSU : S ≤ U) (hUV : U < V) (hVT : V < T)
    (hp : ∀ i, IsNormalPrime S (p i)) (hpa : StrictAnti p)
    (hvalue : F.totient = d*(∏ i, p i).totient)
    (hDS : (largestPrimeFactor d : ℝ) ≤ S)
    (hsq : SquarefreeAbove F S)
    (hnormal : ∀ q : ℕ, q.Prime → q ∣ F → IsNormalPrime S q)
    (hmismatch : largestPrimeFactor F ≠ p ⟨0,by omega⟩)
    (hlast : T ≤ (p ⟨J-1,by omega⟩-1 : ℕ))
    (hlow : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ U)
    (hsize : (F.totient : ℝ) ≤ z)
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hε' : Real.sqrt (B S*B z) ≤ ε')
    (hindexgap : (2*((J-1 : ℕ) : ℝ)+1)*ε < B T-B V)
    (htailgap : (2*(J : ℝ)+1)*ε' < B V-B U) :
    ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ) (hJl : J ≤ l),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ 3 ≤ q i) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧
      p ⟨0,by omega⟩ ≠ q ⟨0,by omega⟩ ∧
      (∀ i : Fin l, i.val < J → V < (q i-1 : ℕ)) ∧
      (∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V) ∧
      (∀ i : Fin l, (q i-1 : ℕ) ≤ z) := by
  have hS1 : 1 < S := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hS
  have hSV : S ≤ V := hSU.trans hUV.le
  have hST : S < T := hSV.trans_lt hVT
  have hBV : B S ≤ B V := Real.log_le_log (Real.log_pos hS1)
    (Real.log_le_log (zero_lt_one.trans hS1) hSV)
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans hε
  have hcoef : ε ≤ (2*((J-1 : ℕ) : ℝ)+1)*ε := by
    have hj : (0 : ℝ) ≤ (J-1 : ℕ) := Nat.cast_nonneg _
    nlinarith only [hj, hε0]
  have hstartgap : Real.sqrt (B S*B T) < B T-B S := by
    linarith only [hε, hcoef, hindexgap, hBV]
  obtain ⟨l, hl, q, E, hE, hES, hqa, hq, heq, hfirst⟩ :=
    ppt_actual_preimage_leading_mismatch_of_gap p ⟨J-1,by omega⟩ hF hS1.le
      (fun i => (hp i).1) hpa.injective hvalue hsq hnormal
      (hp _) hST hlast hstartgap hmismatch
  have hprefixT (i : Fin k) (hi : i ≤ ⟨J-1,by omega⟩) : T ≤ (p i-1 : ℕ) :=
    hlast.trans (Nat.cast_le.mpr (Nat.sub_le_sub_right (hpa.antitone hi) 1))
  obtain ⟨hjl, r, hrj, hVr⟩ := ppt_right_index_exists p q ⟨J-1,by omega⟩
    hS1 hBS hd.ne' hE.ne' hp (fun i => (hq i).1) heq
    (hDS.trans hSV) (hES.trans hSV) hSV hVT hε hprefixT hindexgap
  have hJl : J ≤ l := by
    change J-1<l at hjl
    omega
  have hVlast : V < (q ⟨J-1,hjl⟩-1 : ℕ) := by
    have hr1 : 1 ≤ q r-1 := by have := (hq r).1.1.two_le; omega
    have hrr := largestPrimeFactor_le_self hr1
    have hmon := Nat.sub_le_sub_right (hqa.antitone
      (show (⟨J-1,hjl⟩ : Fin l) ≤ r from hrj)) 1
    exact hVr.trans_le (Nat.cast_le.mpr (hrr.trans hmon))
  have hqz (i : Fin l) : (q i-1 : ℕ) ≤ z := by
    have hdiv : q i-1 ∣ F.totient := by
      rw [hvalue, ppt_totient_primeProduct p (fun i => (hp i).1) hpa.injective, heq]
      exact (Finset.dvd_prod_of_mem (fun i => q i-1) (Finset.mem_univ i)).trans
        (dvd_mul_left _ _)
    exact (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.totient_pos.mpr hF) hdiv)).trans hsize
  have htail := ppt_right_tail_smooth p q hS1 hBS hSU hUV hd.ne' hE.ne'
    hp (fun i => (hq i).1) hqa.antitone heq (hDS.trans hSU) (hES.trans hSU)
    hlow hqz hε' htailgap
  refine ⟨l, q, E, hJl, hE, hES, hqa, ?_, heq, hfirst.symm, ?_, htail, hqz⟩
  · intro i
    have hqi : (2 : ℝ) < q i := hS.trans_lt (hq i).2
    have hqi' : 2 < q i := by exact_mod_cast hqi
    exact ⟨(hq i).1, by omega⟩
  · intro i hi
    have hij : i ≤ (⟨J-1,hjl⟩ : Fin l) := by change i.val ≤ J-1; omega
    exact hVlast.trans_le (Nat.cast_le.mpr (Nat.sub_le_sub_right (hqa.antitone hij) 1))

end TotientAsymptotic

end

end OAI
