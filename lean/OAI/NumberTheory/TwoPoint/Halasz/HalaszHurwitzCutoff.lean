import OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzTail
import PrimeNumberTheoremAnd.Erdos970.ZetaBounds

namespace OAI

/-! First-order Euler truncation for the actual Hurwitz function, uniform
in the shift after its first term is removed. -/
namespace TwoPointCorrelations

open Complex HurwitzZeta MeasureTheory Finset Erdos970

lemma halasz_zeta_cutoff {s : ℂ} (hs : 0<s.re) (hs1 : s≠1)
    {N : ℕ} (hN : 1≤N) :
    ‖riemannZeta s-(∑ n∈range N,((n+1:ℕ):ℂ)^(-s))‖≤
      (N:ℝ)^(1-s.re)/‖1-s‖+(N:ℝ)^(-s.re)/2+
        ‖s‖*(N:ℝ)^(-s.re)/s.re := by
  have hN0 : 0<N := by omega
  have hNR : 0<(N:ℝ) := by exact_mod_cast hN0
  have hs0 : s≠0 := fun h => by subst s; simp at hs
  have hsum : (∑ n∈range (N+1),1/(n:ℂ)^s)=
      ∑ n∈range N,((n+1:ℕ):ℂ)^(-s) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero,zero_cpow hs0,div_zero,add_zero,one_div,cpow_neg]
  have hint : ‖s*∫ x in Set.Ioi (N:ℝ),(⌊x⌋+1/2-x)/(x:ℂ)^(s+1)‖≤
      ‖s‖*(N:ℝ)^(-s.re)/s.re := by
    have hi := ZetaBnd_aux1b N hN hs (t := s.im)
    rw [s.re_add_im] at hi
    rw [norm_mul]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hi (norm_nonneg s)
  have hpower : ‖(-(N:ℂ)^(1-s))/(1-s)‖=(N:ℝ)^(1-s.re)/‖1-s‖ := by
    rw [norm_div,norm_neg]
    congr 1
    simpa only [Complex.sub_re,Complex.one_re,Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos hNR (1-s)
  have hhalf : ‖(-(N:ℂ)^(-s))/2‖=(N:ℝ)^(-s.re)/2 := by
    rw [norm_div,norm_neg]
    simp only [Complex.norm_ofNat]
    congr 1
    simpa only [Complex.neg_re,Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hNR (-s)
  rw [← Zeta0EqZeta hN0 hs hs1,riemannZeta0,hsum]
  have heq : ((∑ n∈range N,((n+1:ℕ):ℂ)^(-s))+
      (-(N:ℂ)^(1-s))/(1-s)+(-(N:ℂ)^(-s))/2+
      s*∫ x in Set.Ioi (N:ℝ),(⌊x⌋+1/2-x)/(x:ℂ)^(s+1))-
      (∑ n∈range N,((n+1:ℕ):ℂ)^(-s)) =
      ((-(N:ℂ)^(1-s))/(1-s)+(-(N:ℂ)^(-s))/2)+
        s*∫ x in Set.Ioi (N:ℝ),(⌊x⌋+1/2-x)/(x:ℂ)^(s+1) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans_eq (by rw [hpower,hhalf])) hint)

theorem halasz_hurwitz_cutoff {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) {N : ℕ} (hN : 1≤N) :
    ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
      (∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s))‖≤
      (N:ℝ)^(1-s.re)/‖1-s‖+(N:ℝ)^(-s.re)/2+
        2*‖s‖*(N:ℝ)^(-s.re)/s.re := by
  apply (halasz_hurwitz_cutoff_transfer ha hs hN (halasz_zeta_cutoff hs hs1 hN)).trans_eq
  ring

end TwoPointCorrelations

end OAI
