import OAI.NumberTheory.Jacobsthal.Estimates.ActualPointSlopes

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open ErdosInverseSampling ErdosInverseSampleCost ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

noncomputable def sampleModulus (U : Finset ℕ) (h : ℕ) (s : Sample U h) : ℕ := ∏ i : Fin h,(s i).val

theorem sampleModulus_pos (U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hU : ∀ u ∈ U,0 < u) : 0 < sampleModulus U h s :=
  Finset.prod_pos (fun i _ => hU _ (s i).property)

theorem sample_prime_dvd_modulus (U : Finset ℕ) (h : ℕ) (s : Sample U h) (i : Fin h) :
    (s i).val ∣ sampleModulus U h s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem sampleModulus_upper (U : Finset ℕ) (h : ℕ) (s : Sample U h) (T : ℝ)
    (hU : ∀ u ∈ U,(u : ℝ) ≤ T) : (sampleModulus U h s : ℝ) ≤ T^h := by
  unfold sampleModulus
  rw [Nat.cast_prod]
  have hh := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => Nat.cast_nonneg (s i).val)
    (fun i _ => hU _ (s i).property)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh

theorem source_sample_modulus_square (K eps : ℝ) (h : ℕ) (hK : 0 ≤ K) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ U theta : ℝ,0 ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
      ∀ s : Sample (primeBin U theta) h,
        ((sampleModulus (primeBin U theta) h s : ℝ))^2 ≤ (sourceZ z)^eps := by
  let A : ℝ := (2*(h : ℝ))*(Real.log 2+K)
  have hA : 0 ≤ A := by dsimp [A];positivity
  filter_upwards [sourceW_log_bounds,(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    exp_loglog_sq_le_sourceZ A eps hA heps] with z hz hs hExp
  intro U theta hU0 hUtop htheta htheta1 s
  have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  have hUL : U ≤ (Real.log z)^K := hUtop.trans (Real.rpow_le_rpow hWpos.le hz.2.2.2 hK)
  have hcap : ∀ u ∈ primeBin U theta,(u : ℝ) ≤ 2*U := by
    intro u hu
    have hh := ((mem_primeBin hU0 htheta u).mp hu).2.2
    nlinarith
  have hM := sampleModulus_upper (primeBin U theta) h s (2*U) hcap
  have hML : (sampleModulus (primeBin U theta) h s : ℝ) ≤ (2*(Real.log z)^K)^h :=
    hM.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hUL (by norm_num)) h)
  have hLL1 : 1 ≤ Real.log (Real.log z) := hs
  have hLL2 : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hsq1 : 1 ≤ (Real.log (Real.log z))^2 := by nlinarith
  have hlogs : Real.log 2+K*Real.log (Real.log z) ≤ (Real.log 2+K)*(Real.log (Real.log z))^2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq1 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    have h2 := mul_le_mul_of_nonneg_left hLL2 hK
    nlinarith
  calc
    _ ≤ ((2*(Real.log z)^K)^h)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hML 2
    _ = Real.exp ((2*(h : ℝ))*(Real.log 2+K*Real.log (Real.log z))) := by
      rw [← pow_mul,← Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.rpow_pos_of_pos hz.2.1 K))]
      rw [← Real.exp_nat_mul]
      congr 1
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hz.2.1 K).ne',Real.log_rpow hz.2.1]
      push_cast
      ring
    _ ≤ Real.exp (A*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ 2*(h : ℝ) by positivity)
      dsimp [A]
      nlinarith
    _ ≤ _ := hExp

end ErdosInverseRefinement

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosInverseSampling

theorem refinement_sample_congruences (C U : Finset ℕ) (a : ℕ → ℕ)
    (h : ℕ) (s : Sample U h) (j : RefinementLabel (sampleModulus U h s)) (q r : ℕ)
    (hq : q ∈ refinementCell C a (sampleModulus U h s) j)
    (hr : r ∈ refinementCell C a (sampleModulus U h s) j) (i : Fin h) :
    (q : ZMod (s i).val) = (r : ZMod (s i).val) ∧
      (cofactorHit q a : ZMod (s i).val) = (cofactorHit r a : ZMod (s i).val) := by
  have hh := refinement_congruences C a (sampleModulus U h s) j q r hq hr
  have hd : ((s i).val : ℤ) ∣ (sampleModulus U h s : ℤ) := by
    exact_mod_cast sample_prime_dvd_modulus U h s i
  have hq' := Int.ModEq.of_dvd hd hh.1
  have hb' := Int.ModEq.of_dvd hd hh.2
  exact ⟨(ZMod.natCast_eq_natCast_iff _ _ _).mpr (Int.natCast_modEq_iff.mp hq'),
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Int.natCast_modEq_iff.mp hb')⟩

end ErdosInverseRefinement

end

end Erdos970

end OAI
