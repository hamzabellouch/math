import OAI.NumberTheory.DirichletL.Reflection.NormalizedPhysical
import OAI.NumberTheory.DirichletL.Descent.MarkBounds

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma primeFamily_support_card (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) :
    (IdealMobiusDivisorSum.primeSupport (∏ i,F.ideal i)).card=Fintype.card φ := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := InverseMoment.finite_primeSupport_card F.generator hc Finset.univ
  simpa only [PrimeFamily.product_span,Finset.card_univ] using hh

theorem branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (F : PrimeFamily ι),
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (Fintype.card (ι→Fin 3):ℝ)^2≤C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/4) (by positivity)
  refine ⟨C^4,by positivity,?_⟩
  intro ι _ F hF
  have hI : (∏ i,F.ideal i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))
  have hnorm : (0:ℝ)<Ideal.absNorm (∏ i,F.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh := hb (∏ i,F.ideal i) hI
  rw [primeFamily_support_card F hF] at hh
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  calc
    ((3:ℝ)^Fintype.card ι)^2 = (9:ℝ)^Fintype.card ι := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    _ ≤ (16:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^4 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^(ε/4))^4 :=
      pow_le_pow_left₀ (by positivity) hh _
    _ = C^4*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hnorm.le]
      congr 2
      norm_num

theorem surviving_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (F : PrimeFamily ι),
      Pairwise (Function.onFun IsCoprime F.ideal) →
      ∀ (jF : ι→ℕ) (A : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ)
        (nset bset : Finset (Ideal ActualEisensteinCubic.O)),
      ((survivingFrozenBranches F jF A nset bset).card:ℝ)^2≤
        C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ F hF jF A nset bset
  have hcard : ((survivingFrozenBranches F jF A nset bset).card:ℝ)≤Fintype.card (ι→Fin 3) := by
    exact_mod_cast Finset.card_le_univ _
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2).trans (hb F hF)

end
end SevenEighths.InverseReflectedPhase

end OAI
