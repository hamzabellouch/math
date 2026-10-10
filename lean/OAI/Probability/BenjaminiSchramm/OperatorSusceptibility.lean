import OAI.Probability.BenjaminiSchramm.SusceptibilityComparison
import OAI.Probability.BenjaminiSchramm.ReciprocalDecay
import OAI.Probability.BenjaminiSchramm.VolumeEntropy

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_uniform_susceptibility_derivative_lower
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T)
    (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ k : ℝ, 0 < k ∧ ∀ (p : unitInterval), p₀ ≤ (p : ℝ) → p < pc G → ∀ x,
      k * (susceptibility G p x)^2 ≤ deriv (realSusceptibility G x) p := by
  obtain ⟨c,C,hc,hC,hcomp⟩ := exists_susceptibility_comparison G hconn hloc hqt p₀ hp₀
  let ε := c / (2 * (C * ‖T‖^3 + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨d,M,K,hdeg,hK,hKn,hrow,hsupport⟩ := exists_small_walk_kernel G hloc hqt hh ε hε
  have hsmall : C * (‖T‖^3 * ‖K‖) ≤ c/2 := by
    have hd : 0 < 2 * (C * ‖T‖^3 + 1) := by positivity
    have hmul := (lt_div_iff₀ hd).mp hKn
    nlinarith [norm_nonneg K]
  let A : ℝ := p₀^(-(M : ℤ)) * ((d+1)^M : ℕ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(c/2)/A,div_pos (half_pos hc) hA,fun p hpp hp x => ?_⟩
  have hp0 : 0 < (p : ℝ) := hp₀.trans_le hpp
  have hlo := susceptibility_derivative_lower_of_kernel G hloc hqt p hp0 hp T K hT hK d M
    hdeg hrow hsupport c C hc.le hC.le x
    (fun b => (hcomp p hpp hp x b).1) (fun b => (hcomp p hpp hp x b).2) hsmall
  have hz : (p : ℝ)^(-(M : ℤ)) ≤ p₀^(-(M : ℤ)) := by
    simp only [zpow_neg,zpow_natCast]
    exact inv_anti₀ (pow_pos hp₀ M) (pow_le_pow_left₀ hp₀.le hpp M)
  have hcoef : (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * (1-(p : ℝ)) ≤ A := by
    calc
      _ ≤ (p : ℝ)^(-(M : ℤ)) * ((d+1)^M : ℕ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [p.2.1]) (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg ((d+1)^M))
  have hbound := hlo.trans (mul_le_mul_of_nonneg_right hcoef
    (susceptibility_derivative_nonneg G hloc hqt p hp0 hp x))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hA).mpr
  simpa only [mul_comm A] using hbound

theorem susceptibility_upper_of_critical_operator
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p) := by
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  let a : ℝ := (pc G : ℝ)/4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨k,hk,hderiv⟩ := exists_uniform_susceptibility_derivative_lower G hconn hloc hqt hh T hT a ha
  have hnear (p : unitInterval) (hap : a < (p : ℝ)) (hp : p < pc G) (x : V) :
      susceptibility G p x ≤ 1 / (k * ((pc G : ℝ) - p)) := by
    rw [←realSusceptibility_coe G x p]
    apply reciprocal_upper_of_derivative_lower (realSusceptibility G x) a (pc G) k hk
      (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) p ⟨hap,hp⟩
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      change 0 < realSusceptibility G x q
      rw [realSusceptibility_coe G x q]
      exact lt_of_lt_of_le zero_lt_one (susceptibility_one_le G hloc hqt q ht.2 x)
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      exact (hasDerivAt_realSusceptibility G hloc hqt q (ha.trans ht.1) ht.2 x).differentiableAt
    · let q : unitInterval := ⟨t,⟨ha.le.trans ht.1.le,ht.2.le.trans (pc G).2.2⟩⟩
      change k * (realSusceptibility G x q)^2 ≤ deriv (realSusceptibility G x) q
      rw [realSusceptibility_coe G x q]
      exact hderiv q ht.1.le ht.2 x
  refine ⟨2/k,div_pos (by norm_num) hk,fun p hp x => ?_⟩
  have hgap : 0 < (pc G : ℝ) - p := sub_pos.mpr hp
  by_cases hap : a < (p : ℝ)
  · apply (hnear p hap hp x).trans
    have he : 1 / (k * ((pc G : ℝ)-p)) = (1/k) / ((pc G : ℝ)-p) := by
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hk.le) hgap.le
  · let q : unitInterval := ⟨(pc G : ℝ)/2,⟨by positivity,by linarith [(pc G).2.2]⟩⟩
    have hq : q < pc G := by change (pc G : ℝ)/2 < pc G; linarith
    have haq : a < (q : ℝ) := by dsimp [a,q]; linarith
    have hpq : p ≤ q := by change (p : ℝ) ≤ (pc G : ℝ)/2; dsimp [a] at hap; linarith
    have hm : susceptibility G p x ≤ susceptibility G q x :=
      (summable_twoPoint_subcritical G hloc hqt p hp x).tsum_le_tsum
        (fun y => twoPoint_mono G x y hpq)
        (summable_twoPoint_subcritical G hloc hqt q hq x)
    apply (hm.trans (hnear q haq hq x)).trans
    have he : 1 / (k * ((pc G : ℝ)-q)) = (2/k)/(pc G : ℝ) := by
      dsimp only [q]
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (div_nonneg (by norm_num) hk.le) hgap (by linarith [p.2.1])

theorem critical_volume_upper_of_operator
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ C : ℝ, 0 < C ∧ ∀ x n, 0 < n →
      criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n := by
  obtain ⟨A,hA,hχ⟩ := susceptibility_upper_of_critical_operator G hconn hloc hqt hh T hT
  exact critical_volume_upper_of_susceptibility_upper G hloc hqt hpc1 A hA hχ

theorem probability_upper_of_operator
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧ ∀ p : unitInterval, pc G < p →
      (p : ℝ) - pc G < η → ∀ x,
      percolationProbability G p x ≤ A * ((p : ℝ) - pc G) := by
  obtain ⟨C,hC,hvol⟩ := critical_volume_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  exact percolationProbability_upper_of_uniform_critical_volume G hloc hqt hpc1 C hC hvol

end Percolation.BenjaminiSchramm

end OAI
