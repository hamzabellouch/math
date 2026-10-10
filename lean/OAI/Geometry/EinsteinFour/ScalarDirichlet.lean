import OAI.Geometry.EinsteinFour.DirichletMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

/-! The positive first mode of the scalar Dirichlet comparison matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def scalarDirichlet (N : ℕ) (d : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (if i = j then d else 0) - (if j.val + 1 = i.val then 1 else 0) -
    (if i.val + 1 = j.val then 1 else 0)

theorem scalarDirichlet_isHermitian (N : ℕ) (d : ℝ) : (scalarDirichlet N d).IsHermitian := by
  ext i j
  change scalarDirichlet N d j i = scalarDirichlet N d i j
  simp only [scalarDirichlet, eq_comm]
  ring

private theorem predecessor_sum {N : ℕ} (f : ℕ → ℝ) (hf : f 0 = 0) (i : Fin N) :
    (∑ j : Fin N, if j.val + 1 = i.val then f (j.val + 1) else 0) = f i.val := by
  by_cases hi : i.val = 0
  · simp [hi, hf]
  · let k : Fin N := ⟨i.val - 1, by omega⟩
    have hk : k.val + 1 = i.val := by dsimp [k]; omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hj
      have hji : j.val + 1 ≠ i.val := by
        intro h
        apply hj
        apply Fin.ext
        dsimp [k]
        omega
      simp [hji]
    · simp

private theorem successor_sum {N : ℕ} (f : ℕ → ℝ) (hf : f (N + 1) = 0) (i : Fin N) :
    (∑ j : Fin N, if i.val + 1 = j.val then f (j.val + 1) else 0) = f (i.val + 2) := by
  by_cases hi : i.val + 1 < N
  · let k : Fin N := ⟨i.val + 1, hi⟩
    rw [Finset.sum_eq_single k]
    · simp [k, Nat.add_assoc]
    · intro j _ hj
      have hji : i.val + 1 ≠ j.val := by
        intro h
        apply hj
        exact Fin.ext h.symm
      simp [hji]
    · simp
  · have hiN : i.val + 2 = N + 1 := by omega
    have hall : ∀ j : Fin N, i.val + 1 ≠ j.val := by intro j; omega
    simp [hall, hiN, hf]

theorem scalarDirichlet_apply_sequence {N : ℕ} (d : ℝ) (f : ℕ → ℝ)
    (h0 : f 0 = 0) (hN : f (N + 1) = 0) (i : Fin N) :
    (scalarDirichlet N d *ᵥ fun j => f (j.val + 1)) i =
      d * f (i.val + 1) - f i.val - f (i.val + 2) := by
  simp only [Matrix.mulVec, dotProduct, scalarDirichlet, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [predecessor_sum f h0, successor_sum f hN]
  simp

theorem scalarDirichlet_sine_eigenvector {N : ℕ} (d θ : ℝ)
    (hθ : Real.sin ((N + 1) * θ) = 0) :
    scalarDirichlet N d *ᵥ (fun i => Real.sin ((i.val + 1) * θ)) =
      (d - 2 * Real.cos θ) • (fun i : Fin N => Real.sin ((i.val + 1) * θ)) := by
  funext i
  have happly := scalarDirichlet_apply_sequence d (fun k => Real.sin (k * θ))
    (by simp) (by simpa only [Nat.cast_add, Nat.cast_one] using hθ) i
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at happly
  rw [happly]
  change d * Real.sin ((i.val + 1) * θ) - Real.sin (i.val * θ) -
    Real.sin ((i.val + 2) * θ) = (d - 2 * Real.cos θ) * Real.sin ((i.val + 1) * θ)
  have hplus : ((i.val : ℝ) + 2) * θ = ((i.val : ℝ) + 1) * θ + θ := by ring
  have hminus : (i.val : ℝ) * θ = ((i.val : ℝ) + 1) * θ - θ := by ring
  rw [hplus, hminus, Real.sin_add, Real.sin_sub]
  ring

private theorem weighted_row_sum {I : Type*} [Fintype I]
    (L : Matrix I I ℝ) (w y : I → ℝ) (lam : ℝ)
    (heigen : L *ᵥ w = lam • w) :
    (∑ i, ∑ j, L i j * w i * w j * y i ^ 2) =
      lam * ∑ i, w i ^ 2 * y i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : ∑ j, L i j * w j = lam * w i := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun heigen i
  calc
    _ = (w i * y i ^ 2) * ∑ j, L i j * w j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hi]; ring

/-- The scalar ground-state identity. It keeps the off-diagonal entries
explicit, so its sign applies directly to the tridiagonal reference. -/
theorem scalar_ground_state_identity {I : Type*} [Fintype I]
    (L : Matrix I I ℝ) (w y : I → ℝ) (lam : ℝ)
    (hsymm : L.IsHermitian) (heigen : L *ᵥ w = lam • w) :
    (∑ i, ∑ j, (-L i j * w i * w j) * (y i - y j) ^ 2) =
      2 * ((fun i => w i * y i) ⬝ᵥ (L *ᵥ fun i => w i * y i) -
        lam * ∑ i, w i ^ 2 * y i ^ 2) := by
  have hrow := weighted_row_sum L w y lam heigen
  have hcol : (∑ i, ∑ j, L i j * w i * w j * y j ^ 2) =
      lam * ∑ i, w i ^ 2 * y i ^ 2 := by
    rw [← hrow, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : L j i = L i j := congrFun (congrFun hsymm.eq i) j
    rw [hs]
    ring
  have hcross : (∑ i, ∑ j, L i j * w i * w j * y i * y j) =
      (fun i => w i * y i) ⬝ᵥ (L *ᵥ fun i => w i * y i) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ = -(∑ i, ∑ j, L i j * w i * w j * y i ^ 2) -
        (∑ i, ∑ j, L i j * w i * w j * y j ^ 2) +
        2 * (∑ i, ∑ j, L i j * w i * w j * y i * y j) := by
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hrow, hcol, hcross]; ring

/-- A positive first eigenvector with positive eigenvalue proves positivity
of a symmetric scalar matrix with nonpositive off-diagonal entries. -/
theorem scalar_posDef_of_positive_mode {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℝ) (w : I → ℝ) (lam : ℝ)
    (hsymm : L.IsHermitian) (hoff : ∀ i j, i ≠ j → L i j ≤ 0)
    (hw : ∀ i, 0 < w i) (hlam : 0 < lam) (heigen : L *ᵥ w = lam • w) :
    L.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsymm
  intro x hx
  let y := fun i => x i / w i
  have hwy : (fun i => w i * y i) = x := by
    funext i
    exact mul_div_cancel₀ (x i) (hw i).ne'
  have hsum : (∑ i, w i ^ 2 * y i ^ 2) = ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [y]
    field_simp [(hw i).ne']
  have hnonneg : 0 ≤ ∑ i, ∑ j, (-L i j * w i * w j) * (y i - y j) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hoff i j hij))
        (hw i).le) (hw j).le) (sq_nonneg _)
  have hid := scalar_ground_state_identity L w y lam hsymm heigen
  rw [hwy, hsum] at hid
  have hnorm : 0 < ∑ i, x i ^ 2 := by
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hp := mul_pos hlam hnorm
  simpa only [star_trivial] using (show 0 < x ⬝ᵥ (L *ᵥ x) by linarith)

def firstSineAngle (N : ℕ) : ℝ := Real.pi / (N + 1)

def firstSineVector (N : ℕ) (i : Fin N) : ℝ := Real.sin ((i.val + 1) * firstSineAngle N)

theorem firstSineVector_pos (N : ℕ) (i : Fin N) : 0 < firstSineVector N i := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hπ : 0 < Real.pi / (N + 1) := div_pos Real.pi_pos hden
  have hi : (i.val : ℝ) + 1 < N + 1 := by exact_mod_cast Nat.succ_lt_succ i.isLt
  have hb := mul_lt_mul_of_pos_right hi hπ
  have he : ((N : ℝ) + 1) * (Real.pi / (N + 1)) = Real.pi := by field_simp
  rw [he] at hb
  exact Real.sin_pos_of_pos_of_lt_pi (by dsimp [firstSineAngle]; positivity) hb

theorem firstSineVector_eigenvector (N : ℕ) (d : ℝ) :
    scalarDirichlet N d *ᵥ firstSineVector N =
      (d - 2 * Real.cos (firstSineAngle N)) • firstSineVector N := by
  apply scalarDirichlet_sine_eigenvector
  have hden : (N : ℝ) + 1 ≠ 0 := by positivity
  have he : ((N : ℝ) + 1) * firstSineAngle N = Real.pi := by
    dsimp [firstSineAngle]
    field_simp
  rw [he, Real.sin_pi]

/-- Positivity of the scalar reference follows from its first sine mode;
no diagonalization of the other sine modes is needed. -/
theorem scalarDirichlet_posDef (N : ℕ) (d : ℝ)
    (hfirst : 0 < d - 2 * Real.cos (firstSineAngle N)) :
    (scalarDirichlet N d).PosDef := by
  apply scalar_posDef_of_positive_mode _ (firstSineVector N)
    (d - 2 * Real.cos (firstSineAngle N)) (scalarDirichlet_isHermitian N d)
    ?_ (firstSineVector_pos N) hfirst (firstSineVector_eigenvector N d)
  intro i j hij
  simp only [scalarDirichlet, ite_eq_right hij, zero_sub]
  split_ifs <;> norm_num

def firstSineNormSq (N : ℕ) : ℝ := ∑ i, firstSineVector N i ^ 2

theorem firstSineNormSq_pos {N : ℕ} (hN : 0 < N) : 0 < firstSineNormSq N := by
  apply Finset.sum_pos' (fun i _ => sq_nonneg (firstSineVector N i))
  exact ⟨⟨0, hN⟩, Finset.mem_univ _, sq_pos_of_pos (firstSineVector_pos N ⟨0, hN⟩)⟩

def unitFirstSineVector (N : ℕ) : Fin N → ℝ :=
  (1 / Real.sqrt (firstSineNormSq N)) • firstSineVector N

theorem unitFirstSineVector_norm {N : ℕ} (hN : 0 < N) :
    ∑ i, unitFirstSineVector N i ^ 2 = 1 := by
  have hs := firstSineNormSq_pos hN
  simp only [unitFirstSineVector, Pi.smul_apply, smul_eq_mul, mul_pow,
    ← Finset.mul_sum]
  change (1 / Real.sqrt (firstSineNormSq N)) ^ 2 * firstSineNormSq N = 1
  rw [div_pow, one_pow, Real.sq_sqrt hs.le]
  exact one_div_mul_cancel hs.ne'

theorem unitFirstSineVector_eigenvector (N : ℕ) (d : ℝ) :
    scalarDirichlet N d *ᵥ unitFirstSineVector N =
      (d - 2 * Real.cos (firstSineAngle N)) • unitFirstSineVector N := by
  rw [unitFirstSineVector, Matrix.mulVec_smul, firstSineVector_eigenvector]
  exact smul_comm _ _ _

end

end PositiveEinsteinFour.Jacobi

end OAI
