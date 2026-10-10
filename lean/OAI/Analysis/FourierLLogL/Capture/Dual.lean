import OAI.Analysis.FourierLLogL.Capture.Criterion
import OAI.Analysis.FourierLLogL.Plateau.Features

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture

open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread
variable {M : ℕ} {s : Scene M}
open scoped Classical

def utility (main : Bool) (k x : ℂ) :=
    if main then 2*(k*x).re-‖k‖^2 else (k*x).re

def sales (main : Bool) (s : Scene M) (c : Grid M → ℂ) (i : Grid M) :=
    rung s (channel (optic s main)) (fun x z => utility main (c z) (chi i x))

lemma utility_bounds (main : Bool) (k x : ℂ) (hk : ‖k‖ ≤ 1) (hx : ‖x‖=1) :
    |utility main k x| ≤ 3 := by
  have hi : |(k*x).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (by rw [norm_mul,hx,mul_one]; exact hk)
  obtain ⟨h1,h2⟩ := abs_le.mp hi
  rw [abs_le]
  unfold utility; split <;>
  · constructor <;> nlinarith [norm_nonneg k]

lemma utility_diff (main : Bool) (k x y : ℂ) (hk : ‖k‖ ≤ 1) :
    |utility main k x- utility main k y| ≤ 2* ‖x-y‖ := by
  have he : |(k*x).re-(k*y).re| ≤ ‖x-y‖ := by
    rw [← Complex.sub_re,←mul_sub]
    exact (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hk)
  cases main
  · change |(k*x).re-(k*y).re| ≤ _; linarith [norm_nonneg (x-y)]
  change |2*_ -_-(2*_ -_)| ≤ _
  rw [sub_sub_sub_cancel_right,←mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  linarith

private lemma income (main : Bool) (s : Scene M) (c : Grid M → ℂ) (i : Grid M) :
    let A := optic s main
    (sales main s c i) = ∑ z : Grid M, let f := fz s.here s.wage s.norm A i z
                                       let H := hist s (channel A) z
                                       if main then 2 * (c z*f).re - H*‖c z‖^2
                                         else (c z*f).re := by
  intro A
  unfold sales rung
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  let l := fun x : Grid M => addMass s (channel A) x z
  have hi : (c z * fz s.here s.wage s.norm A i z).re =
      ∑ x : Grid M, l x * (c z * chi i x).re := by
    unfold fz
    rw [Finset.mul_sum,Complex.re_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_left_comm, Complex.re_ofReal_mul]
    rfl
  change ∑ x, l x * utility main _ _ = (if _ then _ else _)
  rw [hi]
  split
  case isTrue he =>
    simp_rw [show ∀ k v : ℂ, utility main k v = 2*(k*v).re-‖k‖^2 from fun _ _ => by simp [he,utility]]
    rw [Finset.mul_sum,show hist s (channel A) z=∑ i, l i from rfl, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  case isFalse he =>
    simp_rw [show ∀ k v : ℂ, utility main k v = (k*v).re from fun _ _ => by simp [he,utility]]

private lemma fz_dry (s : Scene M) (i z : Grid M) :
    fz s.here s.wage s.norm 0 i z = (side M:ℂ)*scalar s i := by
  unfold fz omegaObs scalar; simp_rw [no_label,uniform_side,Complex.ofReal_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

private def seller (M : ℝ) (f : ℂ) : ℂ := conj f / M

private lemma seller_limit (M : ℝ) (f : ℂ) (hf : ‖f‖ ≤ M) : ‖seller M f‖ ≤ 1 := by
  have hx : 0 ≤ M := le_trans (norm_nonneg _) hf
  unfold seller; rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hx,Complex.norm_conj]
  rcases eq_or_lt_of_le hx with h|h
  · rw [← h,div_zero]; norm_num
  exact (div_le_one h).mpr hf

private lemma price_upper (m : ℝ) (f k : ℂ) (hf : ‖f‖ ≤ m) :
    2*(k*f).re - m*‖k‖^2 ≤ ‖f‖^2/m := by
  have hx : 0 ≤ m := le_trans (norm_nonneg _) hf
  rcases eq_or_lt_of_le hx with h|h
  · have hh : f=0 := norm_le_zero_iff.mp (h ▸ hf)
    simp [←h, hh]
  · have hi : (k*f).re ≤ ‖k‖ * ‖f‖ :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (by rw [norm_mul]))
    apply (le_div_iff₀ h).mpr
    nlinarith [sq_nonneg (m *‖k‖ - ‖f‖),mul_le_mul_of_nonneg_left hi h.le]

private lemma seller_eq (m : ℝ) (f : ℂ) (hf : ‖f‖ ≤ m) :
    2*(seller m f*f).re - m*‖seller m f‖^2= ‖f‖^2 / m := by
  have hx : 0 ≤ m := le_trans (norm_nonneg _) hf
  unfold seller
  by_cases hm : m = 0
  · subst m; simp
  · rw [div_mul_eq_mul_div,mul_comm (conj f) f,Complex.mul_conj,
      ←Complex.sq_norm,← Complex.ofReal_div,norm_div,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hx,Complex.norm_conj,Complex.ofReal_re]
    field_simp; ring

/-- sales of every packet at most the magnitude, attained by choice of a bounded tester. -/
theorem test_complete (main : Bool) (s : Scene M) (hp : 0 ≤ s.wage) (hv : 0 ≤ s.norm)
    (i : Grid M) :
    (∀ c : Grid M → ℂ, (∀ z, ‖c z‖ ≤ 1) → sales main s c i ≤ magnitude main s i) ∧
      ∃ c : Grid M → ℂ, (∀ z, ‖c z‖ ≤ 1) ∧ sales main s c i = magnitude main s i := by
  cases main
  case true =>
    let L (z) := Mz s.here s.wage s.norm s.fund.mood z
    let f (z) := fz s.here s.wage s.norm s.fund.mood i z
    have hf z : ‖f z‖ ≤ L z := fz_norm _ hp hv _ _ _
    constructor
    · intro c _; rw [income]
      apply Finset.sum_le_sum; intro j hj; exact price_upper (L j) (f j) _ (hf j)
    refine ⟨fun i => seller (L i) (f i),fun i => seller_limit _ _ (hf i),?_⟩
    rw [income]
    refine Finset.sum_congr rfl fun j _ => seller_eq (L j) (f j) (hf j)
  case false =>
    let f := scalar s i
    have h1 (c : Grid M → ℂ) :
        sales false s c i = (uniform (Grid M)).Ex (fun z => (c z*f).re) := by
      rw [income]
      change ∑ z : Grid M,(c z*fz s.here s.wage s.norm 0 i z).re= _
      unfold Ex
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [fz_dry,mul_left_comm,Complex.re_ofReal_mul,uniform_side]
    constructor
    · intro c hc
      rw [h1]
      apply le_trans (b:=(uniform (Grid M)).Ex fun _ => ‖f‖)
      · refine Ex_mono _ fun i => ?_
        apply (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans _)
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hc i)
      rw [Ex_const]
      exact le_rfl
    refine ⟨fun _ => polar f,fun _ => polar_unit f,?_⟩
    rw [h1,Ex_const]
    exact polar_identity f

lemma sup_children (main : Bool) (s : Scene M) (hp : s.here.valid) (h : s.here.lev < M)
    (ha : 0 ≤ s.wage) (hb : 0 ≤ s.norm) (i : Grid M) :
    ∃ b, magnitude main s i ≤ magnitude main (s.smaller b) i := by
  obtain ⟨c,hc,H⟩ := (test_complete main s ha hb i).2
  let T (b : Bool) := sales main (s.smaller b) c i
  have he : T false+T true= 2*sales main s c i := rung_split s hp h _ _
  by_contra! HH
  have h1 (b : Bool) : T b ≤ magnitude main (s.smaller b) i :=
    (test_complete main (s.smaller b) ha hb i).1 _ hc
  linarith [HH true,HH false,h1 true,h1 false]

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
