import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical

namespace OAI

/-! Extraction through an additional prime band outside the original
family. The original typical mask remains on the cofactor, and ordinary
coprime multiplicativity suffices. The unsupported integers are retained
as a separate, literal missing-band coefficient. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrtTypicalCoefficient_outside_prime {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ q ∈ P j, q.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) {p m : ℕ} (hp : p.Prime)
    (hpout : p ∉ J.biUnion P) (hm : 0 < m) (hpm : ¬p ∣ m) :
    mrtTypicalCoefficient J P F (p*m) = F p * mrtTypicalCoefficient J P F m := by
  have ha : mrtPrimeAvoids (J.biUnion P) p := by
    intro q hq hqp
    obtain ⟨j,hj,hqj⟩ := mem_biUnion.mp hq
    have he : q=p := (Nat.prime_dvd_prime_iff_eq (hP j hj q hqj) hp).mp hqp
    exact hpout (he ▸ mem_biUnion.mpr ⟨j,hj,hqj⟩)
  unfold mrtTypicalCoefficient
  rw [mrtTypical_mul_of_avoids J P hP ha m]
  split_ifs
  · exact hF p m hp.pos hm (hp.coprime_iff_not_dvd.mpr hpm)
  · simp

/-- The exact missing-extra-band coefficient, before applying a sieve. -/
lemma mrt_extra_prime_missing (A : Finset ℕ) (C : ℕ → ℂ) (n : ℕ) :
    C n-mrtSupportedCoefficient A C n =
      if mrtPrimeAvoids A n then C n else 0 := by
  have hz : finitePrimeDivisorCount A n=0 ↔ mrtPrimeAvoids A n := by
    rw [finitePrimeDivisorCount_eq_card, card_eq_zero]
    simp only [eq_empty_iff_forall_notMem, mem_filter, not_and, mrtPrimeAvoids]
  unfold mrtSupportedCoefficient
  simp only [hz]
  split_ifs <;> simp

/-- The additional-band factorization has the same uniform square and
boundary error as the original bands, with no new factor for their count. -/
theorem mrt_extra_prime_mean_square {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (hout : Disjoint A (J.biUnion P))
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ A, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ A, lower (bin p) ≤ p ∧ (p:ℝ) ≤ δ*lower (bin p))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtSupportedCoefficient A (mrtTypicalCoefficient J P F)) N t -
        ∑ k ∈ K, mrtExponentialPolynomial (A.filter (fun p => bin p=k))
          (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t *
          mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (lower k) t‖^2) ≤
      1408*Real.exp 1*(T/(N:ℝ)+1)*
        ((∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+(δ-1)) := by
  let C := mrtTypicalCoefficient J P F
  let D := mrtDyadicPolynomial (mrtSupportedCoefficient A C) N
  let G := mrtCoarsePolynomial A (fun p => lower (bin p)) N C
  let H := fun t => ∑ p ∈ A, mrtDirichletAtom F p t *
    mrtCofactorPolynomial A C N (lower (bin p)) t
  have hC : OneBounded C := mrtTypicalCoefficient_oneBounded J P F hFb
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hH : Continuous H := by
    apply continuous_finsetSum
    intro p _
    apply Continuous.mul _ (mrtCofactorPolynomial_continuous A C N (lower (bin p)))
    unfold mrtDirichletAtom
    fun_prop
  have hb := mrt_coarse_error_mean_square A hA (fun p => lower (bin p))
    hN hδ hδ2 hL C hC hT
  have hp := mrt_general_prime_factorization_mean A hA (fun p => lower (bin p))
    hN hδ hδ2 hL C F C hC hFb hC
    (fun p hpa m hm hpm => mrtTypicalCoefficient_outside_prime J P hP F hF
      (hA p hpa) (fun hi => Finset.disjoint_left.mp hout hpa hi) hm hpm) hT
  have hpp : (∫ t in -T..T, ‖G t-H t‖^2) ≤
      512*Real.exp 1*(T/(N:ℝ)+1)*
        ((∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+(δ-1)) := by
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (sub_nonneg.mpr hδ)
  have hs := mrt_restricted_energy_split (fun t => D t-H t) (fun t => G t-H t)
    (hD.sub hH) (hG.sub hH) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) : (D t-H t)-(G t-H t)=D t-G t := by ring
  simp only [he, ← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hs
  have hbb : (∫ t in -T..T, ‖D t-H t‖^2) ≤
      1408*Real.exp 1*(T/(N:ℝ)+1)*
        ((∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+(δ-1)) := by
    apply hs.trans
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hpp (by norm_num : (0:ℝ) ≤ 2))
    convert hh using 1
    ring
  simpa only [D, H, C, mrt_extracted_prime_bins K A bin hbin lower N F
    (mrtTypicalCoefficient J P F)] using hbb

end TwoPointCorrelations

end OAI
