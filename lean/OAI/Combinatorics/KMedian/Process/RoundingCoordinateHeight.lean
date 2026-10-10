import Mathlib
import OAI.Combinatorics.KMedian.Compression.RationalOperationHeight
import OAI.Combinatorics.KMedian.Rounding.SignedGridInvariant

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid
open Binary

theorem table {n : ℕ} (q : Fin n → ℚ) (i : Fin n) : At (RationalScaling.denominator q) (q i) := by
  refine ⟨RationalScaling.numerator q i,?_⟩
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀ _ (by exact_mod_cast (RationalScaling.denominator_pos q).ne')]

theorem enlarge {D : ℤ} {q : ℚ} (hq : At D q) (E : ℤ) (hE : E≠0) : At (D*E) q := by
  simpa only [Int.cast_one,mul_one] using RationalGrid.mul hq (integer E 1 hE)

theorem unit_height {D : ℤ} {q : ℚ} {H : ℕ} (hD : D≠0) (hDb : |D|≤(2:ℤ)^H)
    (hq : At D q) (hu : |q|≤1) : HasHeight q H := by
  obtain ⟨A,ha⟩ := hq
  have hDc : (D:ℚ)≠0 := by exact_mod_cast hD
  have he : (A:ℚ)=q*(D:ℚ) := ((eq_div_iff hDc).mp ha).symm
  have hA : |A|≤(2:ℤ)^H := by
    have hh : |(A:ℚ)|≤|(D:ℚ)| := by
      rw [he,abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu (abs_nonneg (D:ℚ))
    exact (by exact_mod_cast hh : |A|≤|D|).trans hDb
  rw [ha]
  exact Gaussian.ratio_num_den_bound A D hD _ hA hDb

theorem divide_weight {D : ℤ} {β q : ℚ} (hD : D≠0) (hβ : β≠0) (hq : At D (β*q)) :
    At (D*β.num) q := by
  obtain ⟨A,ha⟩ := hq
  have hn : (β.num:ℚ)≠0 := by
    intro hz
    apply hβ
    rw [← Rat.num_div_den β,hz,zero_div]
  have hDc : (D:ℚ)≠0 := by exact_mod_cast hD
  refine ⟨A*β.den,?_⟩
  rw [Int.cast_mul,Int.cast_mul,Int.cast_natCast]
  apply (eq_div_iff (mul_ne_zero hDc hn)).mpr
  have hb := β.mul_den_eq_num
  calc
    q*((D:ℚ)*(β.num:ℚ)) = (β*q*(D:ℚ))*(β.den:ℚ) := by rw [← hb]; ring
    _ = (A:ℚ)*(β.den:ℚ) := by rw [(eq_div_iff hDc).mp ha]

end MetricKMedian.RationalGrid

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

def denominator (β : Fin n → ℚ) (p : Vector ℚ n) : ℤ :=
  RationalScaling.denominator β * RationalScaling.denominator (point p)

theorem denominator_pos (β : Fin n → ℚ) (p : Vector ℚ n) : 0<denominator β p :=
  mul_pos (RationalScaling.denominator_pos _) (RationalScaling.denominator_pos _)

theorem initial_grid (β : Fin n → ℚ) (p : Vector ℚ n) :
    (∀ i, At (denominator β p) (β i)) ∧ (∀ i, At (denominator β p) (β i*point p i)) :=
  ⟨fun i => enlarge (table β i) _ (RationalScaling.denominator_pos _).ne',
    fun i => RationalGrid.mul (table β i) (table (point p) i)⟩

theorem denominator_bound (β : Fin n → ℚ) (p : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L) :
    denominator β p≤(2:ℤ)^(2*n*L) := by
  have h1 := RationalScaling.denominator_bound β L (fun i => (hb i).2)
  have h2 := RationalScaling.denominator_bound (point p) L (fun i => (hp i).2)
  simp only [Fintype.card_fin] at h1 h2
  calc
    _ ≤ (2:ℤ)^(L*n)*(2:ℤ)^(L*n) := mul_le_mul h1 h2 (RationalScaling.denominator_pos _).le (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem coordinate_height (β : Fin n → ℚ) (p q : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hq : ∀ i, At (denominator β p) (β i*point q i))
    (hz : ∀ i, β i=0 → point q i=point p i)
    (hu : ∀ i, 0≤point q i ∧ point q i≤1) (i : Fin n) :
    HasHeight (point q i) (2*n*L+L) := by
  by_cases hi : β i=0
  · rw [hz i hi]
    exact (hp i).mono (by omega)
  have hD := denominator_pos β p
  have hd := denominator_bound β p L hb hp
  apply RationalGrid.unit_height (mul_ne_zero hD.ne' (by
      intro hz
      apply hi
      rw [← Rat.num_div_den (β i),hz,Int.cast_zero,zero_div]))
    (D := denominator β p * (β i).num)
  · rw [abs_mul,abs_of_pos hD,pow_add]
    exact mul_le_mul hd (hb i).1 (abs_nonneg _) (by positivity)
  · exact divide_weight hD.ne' hi (hq i)
  · rw [abs_of_nonneg (hu i).1]
    exact (hu i).2

theorem weighted_run (β : Fin n → ℚ) (hβ : ∀ i, 0<β i) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseWeightedPartial.run β hβ p t).length)
    (i : Fin n) : HasHeight (point (SparseWeightedPartial.run β hβ p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseWeightedPartial.run_grid β hβ p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · intro j hj; exact False.elim ((hβ j).ne' hj)
  · exact (SparseWeightedPartial.run_invariants β hβ p hu t a).1

theorem signed_run (β : Fin n → ℚ) (p : Vector ℚ n) (L t : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hu : ∀ i, 0≤point p i ∧ point p i≤1) (a : Fin (SparseSignedPartial.run β p t).length)
    (i : Fin n) : HasHeight (point (SparseSignedPartial.run β p t).states[a.val] i) (2*n*L+L) := by
  apply coordinate_height β p _ L hb hp
  · exact SparseSignedPartial.run_grid β p _ (initial_grid β p).1 (initial_grid β p).2 t a
  · exact SparseSignedPartial.run_zero_weight β p t a
  · exact (SparseSignedPartial.run_invariants β p hu t a).1

end MetricKMedian.RoundingHeight
end

end OAI
