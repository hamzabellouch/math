import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingColumnDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingGcdRemoval

namespace OAI

namespace Ostmann.QuadraticSieve

def binaryColumnEndpoint (N j : ℕ) : ℕ := min N (2*2^j)

theorem binarySquarefreeRows_subset_endpoint (N j : ℕ) :
    binarySquarefreeRows N j ⊆ oddSquarefreeUpTo (binaryColumnEndpoint N j) := by
  intro n hn
  obtain ⟨hn,hlo,hhi⟩ := Finset.mem_filter.mp hn
  obtain ⟨hp,hN,ho,hs⟩ := mem_oddSquarefreeUpTo.mp hn
  rw [pow_succ,mul_comm] at hhi
  exact mem_oddSquarefreeUpTo.mpr ⟨hp,Nat.le_min.mpr ⟨hN,hhi.le⟩,ho,hs⟩

theorem binarySquarefreeRows_strict_lower {N j : ℕ} (hj : 0 < j)
    {n : ℕ} (hn : n ∈ binarySquarefreeRows N j) : 2^j < n := by
  have h := (binarySquarefreeRows_positive_data hj).2 n hn
  apply lt_of_le_of_ne h.2.1
  intro he
  have heven : Even (2^j : ℕ) := Even.pow_of_ne_zero (by decide : Even (2:ℕ)) hj.ne'
  obtain ⟨r,hr⟩ := heven
  obtain ⟨k,hk⟩ := h.2.2.2.2.1
  omega

theorem smoothingNorm_small_binary_le (M K N j D : ℕ) (hsmall : 2^j ≤ D^2) :
    smoothingNorm M K (binarySquarefreeRows N j) ≤ 6*(M : ℝ)*(D : ℝ)^2 := by
  have hcard : (binarySquarefreeRows N j).card ≤ 2*2^j := by
    calc
      _ ≤ (Finset.Icc 1 (2*2^j)).card := Finset.card_le_card (fun n hn => by
        have h := mem_oddSquarefreeUpTo.mp (binarySquarefreeRows_subset_endpoint N j hn)
        exact Finset.mem_Icc.mpr ⟨h.1,h.2.1.trans (Nat.min_le_right _ _)⟩)
      _ = _ := by simp
  apply (smoothingNorm_le_trivial M K _).trans
  have hc : ((binarySquarefreeRows N j).card : ℝ) ≤ 2*(D : ℝ)^2 := by
    exact_mod_cast (hcard.trans (Nat.mul_le_mul_left 2 hsmall))
  calc
    _ ≤ 3*(M : ℝ)*(2*(D : ℝ)^2) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem binary_column_quotient_data {N j D d : ℕ} (hD : 0 < D)
    (hlarge : D^2 < 2^j) (hne : (binarySquarefreeRows N j).Nonempty)
    (hd : 0 < d) (hdD : d ≤ D) :
    0 < binaryColumnEndpoint N j/d ∧ d ≤ binaryColumnEndpoint N j/d ∧
      binaryColumnEndpoint N j/d ≤ N ∧
      ((binaryColumnEndpoint N j/d : ℕ) : ℝ) ≤ 2*((2^j : ℕ) : ℝ)/d ∧
      quotientSupport (binarySquarefreeRows N j) d ⊆
        oddSquarefreeUpTo (binaryColumnEndpoint N j/d) ∧
      ∀ n ∈ quotientSupport (binarySquarefreeRows N j) d,
        Nat.Coprime n d ∧ 1 < n ∧ ((2^j : ℕ) : ℝ)/d < (n : ℝ) ∧
          (n : ℝ) ≤ 2*((2^j : ℕ) : ℝ)/d := by
  have hj : 0 < j := by
    by_contra hh
    have hz : j=0 := by omega
    subst j
    simp only [pow_zero] at hlarge
    nlinarith
  obtain ⟨n,hn⟩ := hne
  have hmem := mem_oddSquarefreeUpTo.mp (binarySquarefreeRows_subset_endpoint N j hn)
  have hlow := (binarySquarefreeRows_positive_data hj).2 n hn
  have hHN : 2^j ≤ N := hlow.2.1.trans hlow.2.2.2.1
  have hHB : 2^j ≤ binaryColumnEndpoint N j := Nat.le_min.mpr ⟨hHN,by omega⟩
  have hd2 : d*d ≤ binaryColumnEndpoint N j := by nlinarith
  have hdiv : d ≤ binaryColumnEndpoint N j/d := (Nat.le_div_iff_mul_le hd).mpr hd2
  have hpos : 0 < binaryColumnEndpoint N j/d := hd.trans_le hdiv
  have hsub := binarySquarefreeRows_subset_endpoint N j
  have hdyadic (m : ℕ) (hm : m ∈ binarySquarefreeRows N j) :
      ((2^j : ℕ) : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2*((2^j : ℕ) : ℝ) := by
    have h := (binarySquarefreeRows_positive_data hj).2 m hm
    exact ⟨by exact_mod_cast binarySquarefreeRows_strict_lower hj hm,
      by exact_mod_cast h.2.2.1.le⟩
  have hdH : (d : ℝ) < ((2^j : ℕ) : ℝ) := by
    exact_mod_cast (show d < 2^j by nlinarith)
  have hq := smoothing_quotient_transform_support hsub hd hdH hdyadic
  refine ⟨hpos,hdiv,(Nat.div_le_self _ _).trans (Nat.min_le_left _ _),?_,hq.1,hq.2⟩
  have hB : (binaryColumnEndpoint N j : ℝ) ≤ 2*((2^j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.min_le_right N (2*2^j))
  exact (Nat.cast_div_le : ((binaryColumnEndpoint N j/d : ℕ) : ℝ) ≤
    (binaryColumnEndpoint N j : ℝ)/d).trans
      (div_le_div_of_nonneg_right hB (Nat.cast_nonneg d))

theorem small_gcd_quotient_energy_sum_le (S : Finset ℕ) (a : ℕ → ℂ) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (d : ℝ)^4*
      coefficientEnergy (quotientSupport S d) (fun n => a (d*n))) ≤
        (D : ℝ)^5*coefficientEnergy S a := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (D : ℝ)^4*coefficientEnergy S a := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (Finset.mem_Icc.mp hd).2) 4)
        (coefficientEnergy_quotientSupport_le S a d) (coefficientEnergy_nonneg _ _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]; push_cast; ring

end Ostmann.QuadraticSieve

end OAI
