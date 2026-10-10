import OAI.Analysis.KadisonSimilarity.Derivation.QuadraticSandwich
import OAI.Analysis.KadisonSimilarity.Derivation.OrbitSquareNormalization

namespace OAI

/-! Finite equal-square families have uniformly comparable orbit norms.
The regularization stays inside the original C*-algebra. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_positive_shift_sqrt_unit (x : A) (hx : 0 ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Aˣ, 0 ≤ (S : A) ∧ (S : A) * (S : A) = x + ε • (1 : A) := by
  let Q : Aˣ := {
    val := x + ε • (1 : A)
    inv := positiveShiftReciprocal x ε
    val_inv := positiveShiftReciprocal_inverse x hx hε
    inv_val := by
      have hc : Commute (positiveShiftReciprocal x ε) (x + ε • (1 : A)) :=
        (positiveShiftReciprocal_commute x ε).add_right ((Commute.one_right _).smul_right ε)
      rw [hc.eq]
      exact positiveShiftReciprocal_inverse x hx hε }
  have hQ : 0 ≤ (Q : A) := add_nonneg hx (smul_nonneg hε.le zero_le_one)
  obtain ⟨S, hS⟩ := (CFC.isUnit_sqrt_iff _ hQ).mpr Q.isUnit
  refine ⟨S, ?_, ?_⟩
  · rw [hS]; exact CFC.sqrt_nonneg _
  · rw [hS, CFC.sqrt_mul_sqrt_self _ hQ]

theorem unit_normalized_square_sum (S : Aˣ) (hS : 0 ≤ (S : A))
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = (S : A) * (S : A)) :
    ∑ i, star (a i * (↑S⁻¹ : A)) * (a i * (↑S⁻¹ : A)) = 1 := by
  have hstar : star S = S := Units.ext hS.star_eq
  have hi : star (↑S⁻¹ : A) = (↑S⁻¹ : A) := by
    rw [← Units.coe_star, star_inv, hstar]
  simp only [star_mul, hi]
  calc
    _ = (↑S⁻¹ : A) * (∑ i, star (a i) * a i) * (↑S⁻¹ : A) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = 1 := by rw [ha]; simp

theorem finite_equal_square_orbit_comparison (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n m : ℕ} (a : Fin n → A) (b : Fin m → A)
    (hab : ∑ i, star (a i) * a i = ∑ j, star (b j) * b j) (ξ : H) :
    ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤ (2 * M ^ 4) ^ 2 * ∑ j, ‖π.1 (b j) ξ‖ ^ 2 := by
  let K := (2 * M ^ 4) ^ 2
  let s := ‖ξ‖ ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hs : 0 ≤ s := sq_nonneg _
  have regularized (ε : ℝ) (hε : 0 < ε) :
      ε * s + ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤
        K * (ε * s + ∑ j, ‖π.1 (b j) ξ‖ ^ 2) := by
    let x := ∑ j, star (b j) * b j
    have hx : 0 ≤ x := Finset.sum_nonneg fun j _ => star_mul_self_nonneg (b j)
    obtain ⟨S, hS, hSq⟩ := exists_positive_shift_sqrt_unit x hx hε
    let e : A := Real.sqrt ε • 1
    have he : star e * e = ε • (1 : A) := by
      dsimp [e]
      rw [star_smul, star_trivial, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, Real.mul_self_sqrt hε.le]
    let a' : Fin (n + 1) → A := Fin.cons e a
    let b' : Fin (m + 1) → A := Fin.cons e b
    have ha' : ∑ i, star (a' i) * a' i = (S : A) * (S : A) := by
      rw [Fin.sum_univ_succ]
      simp only [a', Fin.cons_zero, Fin.cons_succ, he]
      rw [hab, hSq]; dsimp [x]; abel
    have hb' : ∑ i, star (b' i) * b' i = (S : A) * (S : A) := by
      rw [Fin.sum_univ_succ]
      simp only [b', Fin.cons_zero, Fin.cons_succ, he]
      rw [hSq]; dsimp [x]; abel
    let η := π.1 (S : A) ξ
    have hu := normalized_orbit_sum_le π hM hπ
      (fun i => a' i * (↑S⁻¹ : A)) (unit_normalized_square_sum S hS a' ha') η
    have hl := norm_sq_le_normalized_orbit_sum π hM hπ
      (fun i => b' i * (↑S⁻¹ : A)) (unit_normalized_square_sum S hS b' hb') η
    have hrecover (c : A) : π.1 (c * (↑S⁻¹ : A)) η = π.1 c ξ := by
      dsimp [η]
      calc
        _ = (π.1 (c * (↑S⁻¹ : A)) * π.1 (S : A)) ξ := rfl
        _ = π.1 ((c * (↑S⁻¹ : A)) * (S : A)) ξ := by simp only [map_mul]
        _ = π.1 c ξ := by simp [mul_assoc]
    simp only [hrecover] at hu hl
    have hcomp := hu.trans (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * M ^ 4))
    have henorm : ‖π.1 e ξ‖ ^ 2 = ε * s := by
      dsimp [e, s]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_one, smul_apply,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg ε),
        mul_pow, Real.sq_sqrt hε.le]
    simp only [Fin.sum_univ_succ, a', b', Fin.cons_zero, Fin.cons_succ] at hcomp
    rw [henorm] at hcomp
    simpa only [K, pow_two, mul_assoc] using hcomp
  apply le_of_forall_pos_le_add
  intro δ hδ
  let d := (K + 1) * (s + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let ε := δ / d
  have hε : 0 < ε := div_pos hδ hd
  have heq : ε * d = δ := div_mul_cancel₀ δ hd.ne'
  have hsmall : K * (ε * s) ≤ δ := by
    calc
      _ = ε * (K * s) := by ring
      _ ≤ ε * d := mul_le_mul_of_nonneg_left (by dsimp [d]; nlinarith) hε.le
      _ = δ := heq
  have h := regularized ε hε
  nlinarith [mul_nonneg hε.le hs]

theorem listSquareSum_eq_sum_get (L : List A) :
    (listSquareSum L : A) = ∑ i : Fin L.length, star (L.get i) * L.get i := by
  unfold listSquareSum
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact map_sum (selfAdjoint A).subtype _ _

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem listOrbitSum_eq_sum_get (π : BoundedUnitalHom A H) (ξ : H) (L : List A) :
    listOrbitSum π ξ L = ∑ i : Fin L.length, ‖π.1 (L.get i) ξ‖ ^ 2 := by
  rw [listOrbitSum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem list_equal_square_orbit_comparison (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    (a b : List A) (hab : listSquareSum a = listSquareSum b) (ξ : H) :
    listOrbitSum π ξ a ≤ (2 * M ^ 4) ^ 2 * listOrbitSum π ξ b := by
  rw [listOrbitSum_eq_sum_get, listOrbitSum_eq_sum_get]
  apply finite_equal_square_orbit_comparison π hM hπ a.get b.get
  rw [← listSquareSum_eq_sum_get, ← listSquareSum_eq_sum_get, hab]

end KadisonSimilarity

end

end OAI
