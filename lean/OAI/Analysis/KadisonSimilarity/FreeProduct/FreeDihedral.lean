import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralFourier
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialCompression

namespace OAI

/-! The Haar and reflection-coset moments of two free centered symmetries,
derived directly from alternating-centered-word freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

private def pairedWord (d s : R) : ℕ → List R
  | 0 => []
  | n + 1 => d :: s :: pairedWord d s n

omit [Algebra ℂ R] [StarRing R] [StarModule ℂ R] in
private theorem pairedWord_prod (d s : R) (n : ℕ) :
    (pairedWord d s n).prod = (d * s) ^ n := by
  induction n with
  | zero => simp [pairedWord]
  | succ n ih => simp only [pairedWord, List.prod_cons, ih, pow_succ']; simp [mul_assoc]

private theorem pairedWord_alternating
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0) (n : ℕ) :
    AlternatingCenteredWord τ P Q true (pairedWord d s n) := by
  induction n with
  | zero => exact .nil true
  | succ n ih => exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

/-- Exchanging the free factors exchanges the alternating starting side. -/
theorem ScalarFree.symm {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}
    (h : ScalarFree τ P Q) : ScalarFree τ Q P := by
  intro side x xs hw
  apply h (!side) x xs
  have swap : ∀ {side : Bool} {w : List R}, AlternatingCenteredWord τ Q P side w →
      AlternatingCenteredWord τ P Q (!side) w := by
    intro side w hw
    induction hw with
    | nil side => exact .nil (!side)
    | @cons side x xs hm hz ht ih =>
      apply AlternatingCenteredWord.cons (by cases side <;> simpa using hm) hz
      simpa using ih
  exact swap hw

/-- Every positive power of the product of free centered letters has trace zero. -/
theorem ScalarFree.trace_pair_power {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {d s : R}
    (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)
    {n : ℕ} (hn : 0 < n) : τ ((d * s) ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have ha := pairedWord_alternating τ P Q hd hs hd0 hs0 (m + 1)
  have ht := hf true d (s :: pairedWord d s m) ha
  rw [← pairedWord_prod d s (m + 1)]
  exact ht

private theorem pairedWord_append_alternating
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0) (n : ℕ) :
    AlternatingCenteredWord τ P Q true (pairedWord d s n ++ [d]) := by
  induction n with
  | zero => exact .cons (by simpa using hd) hd0 (.nil false)
  | succ n ih => exact .cons (by simpa using hd) hd0 (.cons (by simpa using hs) hs0 ih)

/-- The odd alternating words, which form the reflection coset, also vanish. -/
theorem ScalarFree.trace_pair_power_mul_first
    {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {d s : R} (hd : d ∈ P) (hs : s ∈ Q) (hd0 : τ d = 0) (hs0 : τ s = 0)
    (n : ℕ) : τ ((d * s) ^ n * d) = 0 := by
  have ha := pairedWord_append_alternating τ P Q hd hs hd0 hs0 n
  have hnonempty : pairedWord d s n ++ [d] ≠ [] := by simp
  obtain ⟨x, xs, heq⟩ := List.exists_cons_of_ne_nil hnonempty
  rw [heq] at ha
  have ht := hf true x xs ha
  rw [← heq, List.prod_append, pairedWord_prod] at ht
  simpa using ht

/-- Two free centered symmetries have a product whose nonzero integer
moments vanish. -/
theorem free_symmetry_haar_moments
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ (↑((d * s) ^ l) : R) = if l = 0 then 1 else 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hτ
    | succ n =>
      change τ (↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) =
        if ((n + 1 : ℕ) : ℤ) = 0 then 1 else 0
      rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul, ite_eq_right (by omega)]
      exact hf.trace_pair_power hd hs hd0 hs0 (Nat.succ_pos n)
  | negSucc n =>
    simp only [Int.negSucc_ne_zero, zpow_negSucc]
    rw [← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power hs hd hs0 hd0 (Nat.succ_pos _)

/-- Every reflection-coset word has zero trace. -/
theorem free_symmetry_coset_moments
    (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
    (d s : Rˣ) (hd : (d : R) ∈ P) (hs : (s : R) ∈ Q)
    (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
    (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (l : ℤ) :
    τ ((↑((d * s) ^ l) : R) * (s : R)) = 0 := by
  cases l with
  | ofNat n =>
    cases n with
    | zero => simpa using hs0
    | succ n =>
      have hss : s * s = 1 := by simpa only [hsinv] using inv_mul_cancel s
      have hword : (d * s) ^ (n + 1) * s = (d * s) ^ n * d := by
        rw [pow_succ]
        simp only [mul_assoc, hss, mul_one]
      change τ ((↑((d * s) ^ ((n + 1 : ℕ) : ℤ)) : R) * (s : R)) = 0
      rw [zpow_natCast, ← Units.val_mul, hword, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_mul]
      exact hf.trace_pair_power_mul_first hd hs hd0 hs0 n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, mul_inv_rev, hdinv, hsinv,
      Units.val_pow_eq_pow_val, Units.val_mul]
    exact hf.symm.trace_pair_power_mul_first hs hd hs0 hd0 (n + 1)

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- The product of two selfadjoint involutions is unitary. -/
theorem free_symmetry_product_star (d s : Rˣ)
    (hd : star d = d) (hs : star s = s) (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) :
    star (d * s) = (d * s)⁻¹ := by
  rw [star_mul, hd, hs, mul_inv_rev, hdi, hsi]

omit [StarModule ℂ R] in
/-- Haar moments give orthonormal nonnegative powers in the tracial Hilbert
space. This is the weak-null family used in the corner argument. -/
theorem tracial_haar_powers_orthonormal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] H)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (w : Rˣ) (hw : star w = w⁻¹)
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : R) = if l = 0 then 1 else 0) :
    Orthonormal ℂ (fun n : ℕ => V (↑(w ^ (n : ℤ)) : R)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [hinner, star_unitary_zpow w hw]
  have hprod : (↑(w ^ (-(i : ℤ))) : R) * (↑(w ^ (j : ℤ)) : R) =
      (↑(w ^ ((j : ℤ) - i)) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 2
    omega
  rw [hprod, hhaar]
  by_cases hij : i = j
  · subst j
    simp
  · have hdif : (j : ℤ) - i ≠ 0 := by omega
    simp [hdif, hij]

end KadisonSimilarity

end

end OAI
