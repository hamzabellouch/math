import OAI.Probability.ContinuumTransition.CellEnergy

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

def cellIndex (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ := fun k => ⌊4 * x k⌋

theorem dist_lt_one_of_cellIndex_eq {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cellIndex x = cellIndex y) : ‖x - y‖ < 1 := by
  have hcoord (k : Fin 3) : |x k - y k| < (1 / 4 : ℝ) := by
    have heq : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxlo := Int.floor_le (4 * x k)
    have hxhi := Int.lt_floor_add_one (4 * x k)
    have hylo := Int.floor_le (4 * y k)
    have hyhi := Int.lt_floor_add_one (4 * y k)
    rw [heq] at hxlo hxhi
    rw [abs_lt]
    constructor <;> linarith
  have hsq (k : Fin 3) : (x k - y k) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hc := (hcoord k).le
    have := sq_le_sq₀ (abs_nonneg (x k - y k)) (by norm_num : (0 : ℝ) ≤ 1 / 4) |>.mpr hc
    simpa only [sq_abs] using this
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)
  have hnorm : ‖x - y‖ ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using hsum
  nlinarith [norm_nonneg (x-y)]

abbrev Lattice := Fin 3 → ℤ

def cellRadius (R : ℝ) : ℤ := ⌈4 * R + 1⌉

def nearCells (R : ℝ) (i : Lattice) : Finset Lattice :=
  Fintype.piFinset (fun k => Finset.Icc (i k - cellRadius R) (i k + cellRadius R))

theorem mem_nearCells_iff {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ ∀ k, |j k - i k| ≤ cellRadius R := by
  simp only [nearCells, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' (fun k => ?_)
  omega

theorem nearCells_symm {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ i ∈ nearCells R j := by
  simp only [mem_nearCells_iff, abs_sub_comm]

theorem cellRadius_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellRadius R :=
  Int.ceil_nonneg (by linarith)

theorem cellRadius_le {R : ℝ} (hR : 1 ≤ R) : (cellRadius R : ℝ) ≤ 6 * R := by
  have h := Int.ceil_lt_add_one (4 * R + 1)
  dsimp [cellRadius]
  linarith

theorem card_nearCells {R : ℝ} (hR : 0 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) = (2 * (cellRadius R : ℝ) + 1) ^ 3 := by
  have hn := cellRadius_nonneg hR
  have hc (k : Fin 3) : ((Finset.Icc (i k - cellRadius R) (i k + cellRadius R)).card : ℝ) =
      2 * (cellRadius R : ℝ) + 1 := by
    have h := Int.card_Icc_of_le (i k - cellRadius R) (i k + cellRadius R) (by omega)
    exact_mod_cast h.trans (by ring)
  rw [nearCells, Fintype.card_piFinset, Nat.cast_prod]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_nearCells_le {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  rw [card_nearCells (by linarith)]
  have hn := cellRadius_nonneg (show 0 ≤ R by linarith)
  have hn' : (0 : ℝ) ≤ cellRadius R := by exact_mod_cast hn
  have h : 2 * (cellRadius R : ℝ) + 1 ≤ 13 * R := by
    have := cellRadius_le hR
    linarith
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * cellRadius R + 1) h 3
  nlinarith only [hp]

theorem cellIndex_mem_nearCells {x y : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hd : ‖x - y‖ ≤ R) : cellIndex y ∈ nearCells R (cellIndex x) := by
  rw [mem_nearCells_iff]
  intro k
  have hx1 := Int.floor_le (4 * x k)
  have hx2 := Int.lt_floor_add_one (4 * x k)
  have hy1 := Int.floor_le (4 * y k)
  have hy2 := Int.lt_floor_add_one (4 * y k)
  have hcoord : |x k - y k| ≤ R := by
    have h := PiLp.norm_apply_le (x - y) k
    have hc : |x k - y k| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact hc.trans hd
  have hceil : 4 * R + 1 ≤ (cellRadius R : ℝ) := Int.le_ceil _
  have habs : |((cellIndex y k : ℤ) : ℝ) - (cellIndex x k : ℝ)| ≤
      (cellRadius R : ℝ) := by
    dsimp [cellIndex]
    rw [abs_le] at hcoord ⊢
    constructor <;> linarith
  exact_mod_cast habs

def latticeEnvelope (R : ℝ) (i j : Lattice) : ℝ :=
  if j ∈ nearCells R i then R⁻¹ ^ 3 else 0

theorem latticeEnvelope_nonneg {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    0 ≤ latticeEnvelope R i j := by
  unfold latticeEnvelope
  split_ifs <;> positivity

theorem latticeEnvelope_symm (R : ℝ) (i j : Lattice) :
    latticeEnvelope R i j = latticeEnvelope R j i := by
  simp only [latticeEnvelope, nearCells_symm (i := i) (j := j)]

theorem latticeEnvelope_le {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    latticeEnvelope R i j ≤ R⁻¹ ^ 3 := by
  unfold latticeEnvelope
  split_ifs
  · rfl
  · positivity

theorem sum_latticeEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ∑ j, latticeEnvelope R i (f j) ≤ 2197 := by
  classical
  let s := Finset.univ.filter (fun j : κ => f j ∈ nearCells R i)
  have hcard : s.card ≤ (nearCells R i).card :=
    Finset.card_le_card_of_injOn f (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2) hf.injOn
  have hsum : (∑ j, latticeEnvelope R i (f j)) = (s.card : ℝ) * R⁻¹ ^ 3 := by
    simp only [latticeEnvelope, ← Finset.sum_filter, s, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ ((nearCells R i).card : ℝ) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ ≤ (2197 * R ^ 3) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (card_nearCells_le hR i) (by positivity)
    _ = 2197 := by field_simp

theorem kernel_le_latticeEnvelope (w : ℝ → ℝ) (H R : ℝ)
    (hheight : ∀ r, w r ≤ R⁻¹ ^ 3 * H) (hsupport : ∀ r, R < r → w r = 0)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w ‖x - y‖ ≤ H * latticeEnvelope R (cellIndex x) (cellIndex y) := by
  by_cases h : cellIndex y ∈ nearCells R (cellIndex x)
  · simpa only [latticeEnvelope, ite_eq_left h, mul_comm H] using hheight ‖x - y‖
  · have hd : R < ‖x - y‖ := lt_of_not_ge (fun hle => h (cellIndex_mem_nearCells hle))
    rw [hsupport _ hd, latticeEnvelope, ite_eq_right h, mul_zero]

def mixedEnvelope (σ R : ℕ → ℝ) (i j : Lattice) : ℝ :=
  ∑' n, σ n * latticeEnvelope (R n) i j

theorem summable_mixedEnvelope_terms {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i j : Lattice) :
    Summable (fun n => σ n * latticeEnvelope (R n) i j) := by
  apply hs.of_norm_bounded
  intro n
  have hRp : 0 ≤ R n := le_trans zero_le_one (hR n)
  rw [Real.norm_of_nonneg (mul_nonneg (hσ n) (latticeEnvelope_nonneg hRp i j))]
  have he : latticeEnvelope (R n) i j ≤ 1 :=
    (latticeEnvelope_le hRp i j).trans
      (pow_le_one₀ (inv_nonneg.mpr hRp) (inv_le_one_of_one_le₀ (hR n)))
  simpa using mul_le_mul_of_nonneg_left he (hσ n)

theorem mixedEnvelope_nonneg {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 0 ≤ R n) (i j : Lattice) :
    0 ≤ mixedEnvelope σ R i j :=
  tsum_nonneg (fun n => mul_nonneg (hσ n) (latticeEnvelope_nonneg (hR n) i j))

theorem mixedEnvelope_symm (σ R : ℕ → ℝ) (i j : Lattice) :
    mixedEnvelope σ R i j = mixedEnvelope σ R j i := by
  unfold mixedEnvelope
  congr 1
  funext n
  rw [latticeEnvelope_symm]

theorem sum_mixedEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i : Lattice) :
    ∑ j, mixedEnvelope σ R i (f j) ≤ 2197 * ∑' n, σ n := by
  have hsum : Summable (fun n => ∑ j, σ n * latticeEnvelope (R n) i (f j)) := by
    apply Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hσ n) (latticeEnvelope_nonneg (le_trans zero_le_one (hR n)) i (f j)))) _
      (hs.mul_left 2197)
    intro n
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
    nlinarith only [hh]
  unfold mixedEnvelope
  rw [← Summable.tsum_finsetSum (fun j _ => summable_mixedEnvelope_terms hσ hR hs i (f j)),
    ← hs.tsum_mul_left]
  apply hsum.tsum_le_tsum _ (hs.mul_left 2197)
  intro n
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
  nlinarith only [hh]

theorem attraction_le_mixedEnvelope {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (x y : Space) :
    attraction t σ R ‖x - y‖ ≤
      (t * kernelHeight) * mixedEnvelope σ R (cellIndex x) (cellIndex y) := by
  unfold attraction mixedEnvelope
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ht
  rw [← tsum_mul_left]
  apply (summable_attraction_terms hσ hR hs _).tsum_le_tsum _
    ((summable_mixedEnvelope_terms hσ hR hs _ _).mul_left kernelHeight)
  intro n
  have hh := kernel_le_latticeEnvelope (scaledKernelProfile (R n)) kernelHeight (R n)
    (fun r => by simpa only [kernelHeight, div_eq_mul_inv, one_mul] using
      scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR n)) r)
    (fun r hr => scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR n)) hr.le) x y
  have hh' := mul_le_mul_of_nonneg_left hh (hσ n)
  nlinarith only [hh']

end
end ContinuumTemperature
end

end OAI
