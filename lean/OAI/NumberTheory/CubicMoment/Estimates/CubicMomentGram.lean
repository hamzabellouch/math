import OAI.NumberTheory.CubicMoment.Estimates.WeightedGram
import OAI.NumberTheory.CubicGram.CharacterGram
import OAI.NumberTheory.CubicGram.SieveMajorant

namespace OAI

/-!
# The Gram estimate for a finite cubic-character moment

This supplies the near-orthogonality inequality in the exceptional-character-moment argument
for the actual character polynomials. The only analytic estimate used
here is the cubic Gram theorem.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def primarySieveWeight (Z : ℝ) (n : Eisenstein) : ℝ :=
  if primary n then gramLogBump (norm n / Z) else 0

lemma primarySieveWeight_nonneg (Z : ℝ) (n : Eisenstein) :
    0 ≤ primarySieveWeight Z n := by
  unfold primarySieveWeight
  split_ifs
  · exact gramLogBump.nonneg
  · exact le_rfl

lemma cutoff_gram_finite (p q : Eisenstein) {Z : ℝ} (hZ : 0 < Z) :
    primaryCharacterGram p q cubicSieveCutoff Z =
      weightedFiniteGram (nonzeroNormBall (2*Z)) (primarySieveWeight Z) cubicSymbol p q := by
  have hzero (n : Eisenstein) (hn : n ∉ nonzeroNormBall (2*Z)) :
      (if primary n then cubicSieveCutoff (norm n/Z)*cubicSymbol p n*
        star (cubicSymbol q n) else 0) = 0 := by
    split_ifs with hp
    · have hn' : 2*Z < norm n := lt_of_not_ge (fun h =>
        hn (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
      have hw : cubicSieveCutoff (norm n/Z) = 0 := cubicSieveCutoff_zero (by
        rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hZ.le)]
        exact (le_div_iff₀ hZ).mpr hn'.le)
      simp [hw]
    · rfl
  rw [primaryCharacterGram, tsum_eq_sum hzero]
  unfold weightedFiniteGram
  apply Finset.sum_congr rfl
  intro n hn
  simp only [primarySieveWeight, cubicSieveCutoff]
  split_ifs <;> simp

lemma cutoff_gram_diagonal_le {p : Eisenstein} (hp : primary p)
    {Z : ℝ} (hZ : 0 < Z) :
    ‖primaryCharacterGram p p cubicSieveCutoff Z‖ ≤
      ‖primaryCharacterGram 1 1 cubicSieveCutoff Z‖ := by
  rw [cutoff_gram_finite p p hZ, cutoff_gram_finite 1 1 hZ]
  have he : weightedFiniteGram (nonzeroNormBall (2*Z)) (primarySieveWeight Z)
      cubicSymbol 1 1 = ((∑ n ∈ nonzeroNormBall (2*Z), primarySieveWeight Z n : ℝ) : ℂ) := by
    simp only [weightedFiniteGram, cubicSymbol_one_lower, star_one, mul_one]
    exact (map_sum Complex.ofRealHom _ _).symm
  rw [he, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun n _ => primarySieveWeight_nonneg Z n))]
  calc
    _ ≤ ∑ n ∈ nonzeroNormBall (2*Z),
        ‖(primarySieveWeight Z n : ℂ)*cubicSymbol p n*star (cubicSymbol p n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ nonzeroNormBall (2*Z), primarySieveWeight Z n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg (primarySieveWeight_nonneg Z n)]
      calc
        _ ≤ primarySieveWeight Z n * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (norm_cubicSymbol_le_one hp n)
              (primarySieveWeight_nonneg Z n))
            (norm_cubicSymbol_le_one hp n) (_root_.norm_nonneg _)
            (by simpa using primarySieveWeight_nonneg Z n)
        _ = _ := by ring

lemma cutoff_gram_row_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q : Finset Eisenstein) (P Z : ℝ), 1 ≤ P → 1 ≤ Z →
      (∀ p ∈ Q, gramDyad P p) → ∀ p ∈ Q,
      (∑ q ∈ Q, ‖primaryCharacterGram p q cubicSieveCutoff Z‖) ≤
        D*Z + Real.sqrt ((Q.card : ℝ)*
          (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) := by
  obtain ⟨C,hC,hgram⟩ := primaryCharacterGram_finite cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth hε
  obtain ⟨D,hD,hdiag⟩ := primaryCharacterGram_one_one_bound cubicSieveCutoff
    cubicSieveCutoff_compact cubicSieveCutoff_smooth.continuous
  refine ⟨C,D,hC,hD,?_⟩
  intro Q P Z hP hZ hQ p hp
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsquares := hgram (Q.erase p) P Z p hP hZ (hQ p hp)
    (fun q hq => ⟨hQ q (Finset.mem_of_mem_erase hq), (Finset.mem_erase.mp hq).1⟩)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Q.erase p) (fun _ => (1 : ℝ))
    (fun q => ‖primaryCharacterGram p q cubicSieveCutoff Z‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hcard : ((Q.erase p).card : ℝ) ≤ (Q.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset p Q)
  have hB : 0 ≤ C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)) := by positivity
  have hbound : (∑ q ∈ Q.erase p, ‖primaryCharacterGram p q cubicSieveCutoff Z‖)^2 ≤
      (Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))) :=
    hc.trans ((mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard hB))
  have hsqrt : (∑ q ∈ Q.erase p, ‖primaryCharacterGram p q cubicSieveCutoff Z‖) ≤
      Real.sqrt ((Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))) := by
    exact (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hB)).mpr hbound
  rw [← Finset.add_sum_erase Q (fun q => ‖primaryCharacterGram p q cubicSieveCutoff Z‖) hp]
  exact add_le_add ((cutoff_gram_diagonal_le (hQ p hp).1 hZ0).trans (hdiag Z hZ0)) hsqrt

/-- A concrete smooth majorant converts the proved Gram theorem into a
bound for any finite primary-supported cubic-character polynomial. -/
theorem cubic_moment_gram_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (Q N : Finset Eisenstein) (P Z : ℝ) (v : Eisenstein → ℂ),
      1 ≤ P → 1 ≤ Z → (∀ p ∈ Q, gramDyad P p) →
      (∀ n ∈ N, primary n ∧ norm n ≤ Z) →
      (∑ p ∈ Q, ‖∑ n ∈ N, v n*cubicSymbol p n‖^2) ≤
        (D*Z + Real.sqrt ((Q.card : ℝ)*
          (C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ))))) * ∑ n ∈ N, ‖v n‖^2 := by
  obtain ⟨C,D,hC,hD,hrow⟩ := cutoff_gram_row_le hε
  refine ⟨C,D,hC,hD,?_⟩
  intro Q N P Z v hP hZ hQ hN
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let M := nonzeroNormBall (2*Z)
  let u : Eisenstein → ℂ := fun n => if n ∈ N then v n else 0
  have hNM : N ⊆ M := by
    intro n hn
    exact mem_nonzeroNormBall.mpr ⟨(hN n hn).2.trans (by linarith),
      primary_ne_zero (hN n hn).1⟩
  have hsum (p : Eisenstein) : (∑ n ∈ M, u n*cubicSymbol p n) =
      ∑ n ∈ N, v n*cubicSymbol p n := by
    calc
      _ = ∑ n ∈ N, u n*cubicSymbol p n :=
        (Finset.sum_subset hNM (fun n _ hnot => by simp [u,hnot])).symm
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [u,hn])
  have henergy : (∑ n ∈ M, ‖u n‖^2) = ∑ n ∈ N, ‖v n‖^2 := by
    calc
      _ = ∑ n ∈ N, ‖u n‖^2 :=
        (Finset.sum_subset hNM (fun n _ hnot => by simp [u,hnot])).symm
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [u,hn])
  have hmajor (n : Eisenstein) (hn : n ∈ M) (hu : u n ≠ 0) :
      1 ≤ primarySieveWeight Z n := by
    have hnN : n ∈ N := by by_contra h; exact hu (by simp [u,h])
    have hb : gramLogBump (norm n/Z) = 1 := gramLogBump.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, gramLogBump,
        abs_of_nonneg (div_nonneg (norm_nonneg _) hZ0.le)] using
          (div_le_one hZ0).mpr (hN n hnN).2)
    simp [primarySieveWeight,(hN n hnN).1,hb]
  have h := weighted_gram_operator_le Q M u cubicSymbol (primarySieveWeight Z)
    (R := D*Z + Real.sqrt ((Q.card : ℝ)*(C*(P*Z)^ε*Z*(P+(P^3/Z)^(2/3 : ℝ)))))
    (by positivity) (fun n _ => primarySieveWeight_nonneg Z n) hmajor
    (fun p hp => by
      simpa only [M, ← cutoff_gram_finite _ _ hZ0] using hrow Q P Z hP hZ hQ p hp)
  simpa only [hsum,henergy] using h

end CubicFirstMoment

end

end OAI
