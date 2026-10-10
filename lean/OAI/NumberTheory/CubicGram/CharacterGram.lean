import Mathlib
import OAI.NumberTheory.CubicGram.GramCommon

namespace OAI

/-! The full epsilon-uniform off-diagonal character Gram estimate. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem primaryCharacterGram_finite_divisor_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p) →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        ((2 : ℝ)^(primaryPrimeFactors p).card)^3 *
          (C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_common_block W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro Q P Z p hP hZ hp hQ
  let T := Q.image (primaryCommonFactor p)
  let d : ℝ := (2 : ℝ)^(primaryPrimeFactors p).card
  let R : ℝ := C*(2 : ℝ)^ε*P^(4*ε)*(Z*P+P^2+P^2*Z^(1/3 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT k (hk : k ∈ T) : primary k ∧ Squarefree k ∧ k ∣ p := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    have hh := primaryCommonFactor_spec hp.1 (hQ q hq).1.1 hp.2.1 (hQ q hq).1.2.1
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hcard : (T.card : ℝ) ≤ d := by
    have h := primary_divisors_card_le T (fun k hk => ⟨(hT k hk).1,(hT k hk).2.1⟩) hp.1
    have he : T.filter (· ∣ p) = T := Finset.filter_eq_self.mpr (fun k hk => (hT k hk).2.2)
    simpa only [he,d] using h
  have hblock k (hk : k ∈ T) :
      (∑ q ∈ Q.filter (fun q => primaryCommonFactor p q = k), ‖primaryCharacterGram p q W Z‖^2) ≤ d^2*R := by
    have hh := hc (Q.filter (fun q => primaryCommonFactor p q = k)) P Z p k hP hZ hp
      (fun q hq => ⟨(hQ q (Finset.mem_filter.mp hq).1).1,
        (hQ q (Finset.mem_filter.mp hq).1).2,(Finset.mem_filter.mp hq).2⟩)
      (hT k hk).1 (hT k hk).2.1 (hT k hk).2.2
    have hd : (2 : ℝ)^(primaryPrimeFactors k).card ≤ d :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd (hT k hk).1 hp.1 (hT k hk).2.2))
    exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hd 2) hR)
  have he := Finset.sum_fiberwise_of_maps_to (s := Q) (t := T) (g := primaryCommonFactor p)
    (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) (fun q => ‖primaryCharacterGram p q W Z‖^2)
  calc
    _ = ∑ k ∈ T, ∑ q ∈ Q.filter (fun q => primaryCommonFactor p q = k),
        ‖primaryCharacterGram p q W Z‖^2 := he.symm
    _ ≤ ∑ k ∈ T, d^2*R := Finset.sum_le_sum hblock
    _ = (T.card : ℝ)*d^2*R := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ d*d^2*R := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (sq_nonneg d)) hR
    _ = _ := by dsimp [d,R]; ring

lemma gram_shape_le {P Z : ℝ} (hP : 0 < P) (hZ : 1 ≤ Z) :
    Z*P+P^2+P^2*Z^(1/3 : ℝ) ≤ 2*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have he : Z*(P^3/Z)^(2/3 : ℝ) = P^2*Z^(1/3 : ℝ) := by
    rw [Real.div_rpow (by positivity : 0 ≤ P^3) hZ0.le,
      ← Real.rpow_natCast P 3,← Real.rpow_mul hP.le]
    norm_num
    have hz : Z/Z^(2/3 : ℝ) = Z^(1/3 : ℝ) := by
      nth_rw 1 [← Real.rpow_one Z]
      rw [← Real.rpow_sub hZ0]
      norm_num
    calc _ = P^2*(Z/Z^(2/3 : ℝ)) := by ring
         _ = _ := by rw [hz]
  have hz1 := Real.one_le_rpow hZ (by norm_num : (0 : ℝ) ≤ 1/3)
  nlinarith [mul_nonneg (sq_nonneg P) (by linarith : 0 ≤ Z^(1/3 : ℝ)-1)]

theorem primaryCharacterGram_finite (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset Eisenstein) (P Z : ℝ) (p : Eisenstein),
      1 ≤ P → 1 ≤ Z → gramDyad P p →
      (∀ q ∈ Q, gramDyad P q ∧ q ≠ p) →
      (∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2) ≤
        C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by
  let η : ℝ := min (ε/8) (1/2)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : 7*η ≤ ε := by have h := min_le_left (ε/8) (1/2); change η ≤ ε/8 at h; linarith
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_finite_divisor_bound W hW hW' hη hη1
  obtain ⟨D,hD,hd⟩ := primeDivisorWeight_small_power η hη
  refine ⟨2*C*D^3*(2 : ℝ)^(4*η),by positivity,?_⟩
  intro Q P Z p hP hZ hp hQ
  have hP0 : 0 < P := by linarith
  have hZ0 : 0 < Z := by linarith
  have hdiv : (2 : ℝ)^(primaryPrimeFactors p).card ≤ D*(2*P)^η :=
    (hd p hp.1 hp.2.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg p) hp.2.2.2.le hη.le) hD.le)
  have hdiv3 := pow_le_pow_left₀ (by positivity) hdiv 3
  have hpow : P^(7*η) ≤ (P*Z)^ε := by
    apply (Real.rpow_le_rpow_of_exponent_le hP hηε).trans
    exact Real.rpow_le_rpow hP0.le (by nlinarith) hε.le
  have hh := hc Q P Z p hP hZ hp hQ
  have he : (D*(2*P)^η)^3 * (C*(2 : ℝ)^η*P^(4*η)) =
      C*D^3*(2 : ℝ)^(4*η)*P^(7*η) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP0.le,mul_pow,mul_pow,
      ← Real.rpow_natCast ((2 : ℝ)^η) 3,← Real.rpow_natCast (P^η) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_mul hP0.le]
    calc
      _ = C*D^3*((2 : ℝ)^(η*3)*(2 : ℝ)^η)*(P^(η*3)*P^(4*η)) := by ring_nf
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),← Real.rpow_add hP0]; ring_nf
  calc
    _ ≤ (D*(2*P)^η)^3 * (C*(2 : ℝ)^η*P^(4*η)) * (Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
      apply hh.trans
      have h := mul_le_mul_of_nonneg_right hdiv3
        (by positivity : 0 ≤ C*(2 : ℝ)^η*P^(4*η)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)))
      convert h using 1
      ring
    _ = C*D^3*(2 : ℝ)^(4*η)*P^(7*η)*(Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by rw [he]
    _ ≤ C*D^3*(2 : ℝ)^(4*η)*(P*Z)^ε*(2*Z*(P+(P^3/Z)^(2/3 : ℝ))) := by
      apply mul_le_mul _ (gram_shape_le hP0 hZ) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

theorem characterGram : CharacterGramStatement := by
  intro W hW' hW hWpos ε hε
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_finite W hW hW' hε
  refine ⟨C,hC,?_⟩
  intro P Z p hP hZ hp
  let Q := (finite_norm_le (2*P)).toFinset.filter (fun q => gramDyad P q ∧ q ≠ p)
  have hQ q : q ∈ Q ↔ gramDyad P q ∧ q ≠ p := by
    simp only [Q,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
    exact ⟨fun h => h.2,fun h => ⟨h.1.2.2.2.le,h⟩⟩
  have he : (∑' q : Eisenstein, if gramDyad P q ∧ q ≠ p then ‖primaryCharacterGram p q W Z‖^2 else 0) =
      ∑ q ∈ Q, ‖primaryCharacterGram p q W Z‖^2 := by
    rw [tsum_eq_sum (s := Q) (fun q hq => ite_eq_right (fun h => hq ((hQ q).mpr h)))]
    exact Finset.sum_congr rfl (fun q hq => ite_eq_left ((hQ q).mp hq))
  rw [he]
  exact hc Q P Z p hP hZ hp (fun q hq => (hQ q).mp hq)

end CubicFirstMoment
end
end

end OAI
