import Mathlib

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set
abbrev Index := ℤ × ℤ
abbrev Base := ℝ × ℝ

def cell (h R : ℝ) (a : Index) : Set Base :=
  {x | |x.1 - h * a.1| < R * h ∧ |x.2 - h * a.2| < R * h}

def color (q : ℕ) (a : Index) : (ZMod q) × (ZMod q) :=
  ((a.1 : ZMod q), (a.2 : ZMod q))

lemma same_color_difference (q : ℕ) {a b : ℤ}
    (he : (a : ZMod q) = (b : ZMod q)) : (q : ℤ) ∣ a - b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp [he]

lemma divided_ne_abs_ge {q : ℕ} (hq : 0 < q) {a b : ℤ}
    (he : (q : ℤ) ∣ a - b) (hne : a ≠ b) : (q : ℝ) ≤ |(a : ℝ) - b| := by
  obtain ⟨k, hk⟩ := he
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hn : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hk0)
  have heq : (a : ℝ) - b = q * (k : ℝ) := by exact_mod_cast hk
  rw [heq, abs_mul, abs_of_pos (by exact_mod_cast hq : (0 : ℝ) < q)]
  nlinarith [show (0 : ℝ) < q by exact_mod_cast hq]



theorem same_color_disjoint {q : ℕ} (hq : 0 < q) {h R : ℝ} (hh : 0 < h)
    (hR : 2 * R ≤ q) {a b : Index} (hne : a ≠ b)
    (he : color q a = color q b) : Disjoint (cell h R a) (cell h R b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hc1 : (a.1 : ZMod q) = (b.1 : ZMod q) := congrArg Prod.fst he
  have hc2 : (a.2 : ZMod q) = (b.2 : ZMod q) := congrArg Prod.snd he
  have hd (i j : ℤ) (hi : |x.1 - h * i| < R * h)
      (hj : |x.1 - h * j| < R * h) : |(i : ℝ) - j| < 2 * R := by
    have ht := abs_sub_le (x.1 - h * i) 0 (x.1 - h * j)
    have heq : (x.1 - h * i) - (x.1 - h * j) = -(h * ((i : ℝ) - j)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hh] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    nlinarith
  have hdx := hd a.1 b.1 hxa.1 hxb.1
  have hdy : |(a.2 : ℝ) - b.2| < 2 * R := by
    have ht := abs_sub_le (x.2 - h * a.2) 0 (x.2 - h * b.2)
    have heq : (x.2 - h * a.2) - (x.2 - h * b.2) = -(h * ((a.2 : ℝ) - b.2)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hh] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    nlinarith [hxa.2,hxb.2]
  by_cases ha : a.1 = b.1
  · have hb : a.2 ≠ b.2 := fun hb => hne (Prod.ext ha hb)
    have hy := divided_ne_abs_ge hq (same_color_difference q hc2) hb
    linarith
  · have hx := divided_ne_abs_ge hq (same_color_difference q hc1) ha
    linarith

def quantize (h : ℝ) (x : Base) : Index :=
  (⌊x.1/h⌋,⌊x.2/h⌋)

lemma coordinate_floor_near {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |x - h * (⌊x/h⌋ : ℤ)| < h := by
  have hl := Int.floor_le (x/h)
  have hu := Int.lt_floor_add_one (x/h)
  have hlo : h * (⌊x/h⌋ : ℤ) ≤ x := by
    simpa [mul_comm] using (le_div_iff₀ hh).mp hl
  have hup : x < h * ((⌊x/h⌋ : ℤ) + 1) := by
    have ht := (div_lt_iff₀ hh).mp hu
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

lemma quantize_covers {h : ℝ} (hh : 0 < h) (x : Base) :
    x ∈ cell h 1 (quantize h x) := by
  exact ⟨by simpa [quantize] using coordinate_floor_near hh x.1,
    by simpa [quantize] using coordinate_floor_near hh x.2⟩

def box (N : ℕ) : Finset Index :=
  (Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)

lemma floor_mem_interval {A h : ℝ} {N : ℕ} (hh : 0 < h)
    (hN : A/h + 1 ≤ N) {x : ℝ} (hx : |x| ≤ A) :
    ⌊x/h⌋ ∈ Finset.Icc (-(N : ℤ)) N := by
  rw [Finset.mem_Icc]
  have hlo : -A ≤ x := (abs_le.mp hx).1
  have hup : x ≤ A := (abs_le.mp hx).2
  have hfl := Int.floor_le (x/h)
  have hfu := Int.lt_floor_add_one (x/h)
  have hdlo : -A/h ≤ x/h := div_le_div_of_nonneg_right hlo hh.le
  have hdup : x/h ≤ A/h := div_le_div_of_nonneg_right hup hh.le
  constructor
  · have hr : -(N : ℝ) ≤ (⌊x/h⌋ : ℤ) := by rw [neg_div] at hdlo; linarith
    exact_mod_cast hr
  · have hr : ((⌊x/h⌋ : ℤ) : ℝ) ≤ N := by linarith
    exact_mod_cast hr

lemma finite_box_covers {A h : ℝ} {N : ℕ} (hh : 0 < h) (hN : A/h + 1 ≤ N)
    {x : Base} (hx : |x.1| ≤ A ∧ |x.2| ≤ A) :
    ∃ a ∈ box N, x ∈ cell h 1 a := by
  refine ⟨quantize h x, ?_, quantize_covers hh x⟩
  exact Finset.mem_product.mpr ⟨floor_mem_interval hh hN hx.1,
    floor_mem_interval hh hN hx.2⟩

lemma box_card (N : ℕ) : (box N).card = (2 * N + 1)^2 := by
  have hi : (Finset.Icc (-(N : ℤ)) N).card = 2*N+1 := by
    rw [Int.card_Icc]
    omega
  simp [box, hi, pow_two]



lemma box_card_bound {A h : ℝ} {N : ℕ} (hA : 0 ≤ A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hN : (N : ℝ) ≤ A/h + 2) :
    ((box N).card : ℝ) ≤ ((2*A+5)/h)^2 := by
  rw [box_card]
  push_cast
  have hb : 2*(N : ℝ)+1 ≤ (2*A+5)/h := by
    apply (le_div_iff₀ hh).mpr
    have ht : (N : ℝ)*h ≤ A+2*h := by
      have hz := mul_le_mul_of_nonneg_right hN hh.le
      rw [add_mul, div_mul_cancel₀ _ hh.ne'] at hz
      linarith
    nlinarith
  have hlo : 0 ≤ (2*(N : ℝ)+1) := by positivity
  have hhi : 0 ≤ (2*A+5)/h := div_nonneg (by linarith only [hA]) hh.le
  exact (sq_le_sq₀ hlo hhi).mpr hb

end ClosedSurfaceR4.PhaseGrid

end

end OAI
