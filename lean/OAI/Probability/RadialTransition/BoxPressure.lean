import OAI.Probability.RadialTransition.GridPressure

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma summable_sectorWeight (φ : Potential) (L β z : ℝ) (n : ℕ) :
    Summable (fun k : ℕ => (if k = n then (1:ℝ) else 0)*Real.exp (z*k)*partition φ L k β) :=
  summable_of_ne_finset_zero (s := {n}) (by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk])

lemma sectorWeight_tsum (φ : Potential) (L β z : ℝ) (n : ℕ) :
    (∑' k : ℕ, (if k = n then (1:ℝ) else 0)*Real.exp (z*k)*partition φ L k β) = Real.exp (z*n)*partition φ L n β := by
  simp only [ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq n _

lemma macroProduct_sector (φ : Potential) (m q : ℕ) (β : ℝ) (n : ℕ) (x : MacroState m q) :
    macroProduct φ m q β (fun k => if k = n then 1 else 0) x =
      if (∀ i, particleCount (x i) = n) then
        Real.exp (-β*∑ i : GridIndex m, pairWithin (fun (y z : macroRegion q (gridEmbed i)) => radialPair φ y z) (x i)) else 0 := by
  classical
  by_cases hh : ∀ i, particleCount (x i) = n
  · rw [ite_eq_left hh]
    simp only [macroProduct, hh, ite_true, one_mul, ← Real.exp_sum, ← Finset.mul_sum]
  · simp only [hh, ite_false]
    obtain ⟨i, hi⟩ := not_forall.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma macroSector_lower {φ : Potential} {m q : ℕ} (hq : 0 < q) {β R lam : ℝ}
    (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam) (n : ℕ) (x : MacroState m q) :
    Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3)))*
      macroProduct φ m q β (fun k => if k = n then 1 else 0) x ≤
    Real.exp (-β*macroKacEnergy φ m q R lam x) := by
  classical
  rw [macroProduct_sector]
  split_ifs with hh
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb := mul_le_mul_of_nonneg_left (macro_attraction_lower hq hR x hh) (mul_nonneg hβ hlam)
    unfold macroKacEnergy
    nlinarith
  · simpa only [mul_zero] using (Real.exp_pos _).le

lemma macroKac_partition_lower {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {m q : ℕ} (hq : 0 < q) {β R lam z : ℝ} (hβ : 0 ≤ β) (hR : (q:ℝ)/4 ≤ R) (hlam : 0 ≤ lam)
    (hi : Integrable (fun x => Real.exp (-β*macroKacEnergy φ m q R lam x)) (macroMeasure m q z)) (n : ℕ) :
    Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3)))*
      (Real.exp (z*n)*partition φ ((q:ℝ)/4) n β)^(m^3) ≤
    boltzmannPartition (macroMeasure m q z) (fun x => β*macroKacEnergy φ m q R lam x) := by
  have hs := summable_sectorWeight φ ((q:ℝ)/4) β z n
  have hn (k : ℕ) : 0 ≤ (if k = n then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hh := integral_mono ((integrable_macroProduct hφ hb hq m β z _ hn hs).const_mul
    (Real.exp (β*lam*((kernelInterior m q R).card*(1-kernelRowError q R)*(n:ℝ)^2/(2*((q:ℝ)/4)^3))))) hi
    (macroSector_lower hq hβ hR hlam n)
  rw [integral_const_mul, integral_macroProduct hφ hb hq m β z _ hn hs, sectorWeight_tsum] at hh
  simpa only [boltzmannPartition, neg_mul] using hh

end RadialTransition

end

end OAI
