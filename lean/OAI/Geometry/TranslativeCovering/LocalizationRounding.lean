import OAI.Geometry.TranslativeCovering.LocalizationWindow

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

namespace LocalizationRounding
open Set Finset
open scoped BigOperators
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def weight (n : ℕ) (a r : ℝ) : ℝ := 1+(n:ℝ)*max (1-r^2/a^2) 0

lemma truncated_square {a r s : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    max (a^2-s^2) 0 ≤ max (a^2-r^2) 0+2*a*|s-r| := by
  have hab : |r-s| = |s-r| := abs_sub_comm _ _
  have hzero : 0 ≤ 2*a*|s-r| := by positivity
  apply max_le _ (by have := le_max_right (a^2-r^2) 0; linarith)
  by_cases hsa : s ≤ a
  · by_cases hra : r ≤ a
    · have hsum : r+s ≤ 2*a := by linarith
      have hmul := mul_le_mul_of_nonneg_right (le_abs_self (r-s)) (add_nonneg hr hs)
      rw [hab] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hsum (abs_nonneg (s-r))
      have hm := le_max_left (a^2-r^2) 0
      nlinarith only [hmul,hmul',hm]
    · have har : 0 ≤ r-a := by linarith [le_of_not_ge hra]
      have hdist : a-s ≤ |s-r| := by
        have hh := le_abs_self (r-s)
        rw [hab] at hh
        linarith only [hh,har]
      have hh := mul_le_mul_of_nonneg_right hdist (by linarith : 0 ≤ 2*a)
      have hm := le_max_right (a^2-r^2) 0
      nlinarith only [hh,hm,sq_nonneg (a-s)]
  · have hsq : a^2 ≤ s^2 := (sq_le_sq₀ ha.le hs).mpr (le_of_not_ge hsa)
    have hm := le_max_right (a^2-r^2) 0
    linarith only [hsq,hm,hzero]

lemma weight_lipschitz {n : ℕ} {a r s : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    weight n a s ≤ weight n a r+(2*(n:ℝ)/a)*|s-r| := by
  have hh := div_le_div_of_nonneg_right (truncated_square ha hr hs) (sq_nonneg a)
  have he (t : ℝ) : max (a^2-t^2) 0/a^2 = max (1-t^2/a^2) 0 := by
    rw [← max_div_div_right (sq_nonneg a),sub_div,div_self (pow_ne_zero _ ha.ne'),zero_div]
  rw [add_div,he s,he r] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  dsimp [weight]
  have he2 : (n:ℝ)*(2*a*|s-r|/a^2) = (2*(n:ℝ)/a)*|s-r| := by field_simp
  rw [mul_add,he2] at hm
  linarith only [hm]

noncomputable def rounded {n : ℕ} (h : ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => h*(round (x i/h):ℝ))

lemma rounded_coord {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Space n) (i : Fin n) :
    |x i-rounded h x i| ≤ h/2 := by
  have hb := abs_sub_round (x i/h)
  have hb' := mul_le_mul_of_nonneg_left hb hh.le
  calc
    _ = |h*(x i/h-(round (x i/h):ℝ))| := by
      congr 1
      dsimp [rounded]
      field_simp
    _ = h*|x i/h-(round (x i/h):ℝ)| := by rw [abs_mul,abs_of_pos hh]
    _ ≤ h*(1/2) := hb'
    _ = _ := by ring

lemma rounding_error {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Space n) :
    ‖x-rounded h x‖ ≤ Real.sqrt n*h/2 := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ i : Fin n,‖(x-rounded h x).ofLp i‖^2 ≤ (n:ℝ)*(h/2)^2 := by
    calc
      _ ≤ ∑ _i : Fin n,(h/2)^2 := Finset.sum_le_sum fun i _ => by
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        simpa only [PiLp.sub_apply,Real.norm_eq_abs] using rounded_coord hh x i
      _ = _ := by simp
  apply (Real.sqrt_le_sqrt hs).trans_eq
  rw [Real.sqrt_mul (Nat.cast_nonneg n),Real.sqrt_sq (by positivity)]
  ring

lemma residual_error {n : ℕ} {h : ℝ} (hh : 0 < h) (x y : Space n) :
    |‖y-rounded h x‖-‖y-x‖| ≤ Real.sqrt n*h/2 := by
  calc
    _ ≤ ‖(y-rounded h x)-(y-x)‖ := abs_norm_sub_norm_le _ _
    _ = ‖x-rounded h x‖ := by congr 1; abel
    _ ≤ _ := rounding_error hh x

lemma norm_buffer {n : ℕ} {h r : ℝ} (hh : 0 < h) (x y : Space n)
    (hr : ‖y-x‖ ≤ r) : ‖y-rounded h x‖ ≤ r+Real.sqrt n*h/2 := by
  have ht := residual_error hh x y
  have hx := le_abs_self (‖y-rounded h x‖-‖y-x‖)
  linarith only [hr,ht,hx]

lemma slab_buffer {n : ℕ} {h T : ℝ} (hh : 0 < h) (x y u : Space n)
    (hu : ‖u‖ = 1) (hslab : |inner ℝ u (y-x)| ≤ T) :
    |inner ℝ u (y-rounded h x)| ≤ T+Real.sqrt n*h/2 := by
  have hdecomp : y-rounded h x = (y-x)+(x-rounded h x) := by abel
  rw [hdecomp,inner_add_right]
  calc
    _ ≤ |inner ℝ u (y-x)|+|inner ℝ u (x-rounded h x)| := abs_add_le _ _
    _ ≤ T+‖u‖*‖x-rounded h x‖ := add_le_add hslab (abs_real_inner_le_norm _ _)
    _ ≤ _ := by rw [hu,one_mul]; exact add_le_add_right (rounding_error hh x) T

lemma weight_transfer {n : ℕ} {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (x y : Space n) :
    weight n a ‖y-rounded h x‖ ≤
      (1+(2*(n:ℝ)/a)*(Real.sqrt n*h/2))*weight n a ‖y-x‖ := by
  have hLip := weight_lipschitz (n := n) ha (norm_nonneg (y-x)) (norm_nonneg (y-rounded h x))
  have herr := mul_le_mul_of_nonneg_left (residual_error hh x y) (by positivity : 0 ≤ 2*(n:ℝ)/a)
  have hw : 1 ≤ weight n a ‖y-x‖ := by
    dsimp [weight]; have := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (le_max_right (1-‖y-x‖^2/a^2) 0); linarith
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (2*(n:ℝ)/a)*(Real.sqrt n*h/2))
  nlinarith only [hLip,herr,hm]

noncomputable def latticePoint {n : ℕ} (h : ℝ) (z : Fin n → ℤ) : Space n :=
  WithLp.toLp 2 (fun i => h*(z i:ℝ))
noncomputable def integerBox (n : ℕ) (m : ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-m) m)
noncomputable def alphabet (n : ℕ) (h L : ℝ) : Finset (Space n) := by
  classical
  exact ((integerBox n ⌊L/h⌋).image (latticePoint h)).filter (fun x => ‖x‖ ≤ L)

lemma latticePoint_mem_box {n : ℕ} {h L : ℝ} (hh : 0 < h) (z : Fin n → ℤ)
    (hz : ‖latticePoint h z‖ ≤ L) : z ∈ integerBox n ⌊L/h⌋ := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  have hcoord : h*|(z i:ℝ)| ≤ L := by
    have hp := (PiLp.norm_apply_le (latticePoint h z) i).trans hz
    simpa [latticePoint,Real.norm_eq_abs,abs_mul,abs_of_pos hh] using hp
  have hab : |(z i:ℝ)| ≤ L/h := (le_div_iff₀ hh).mpr (by linarith only [hcoord])
  have hu : z i ≤ ⌊L/h⌋ := Int.le_floor.mpr ((le_abs_self _).trans hab)
  have hl : -(z i) ≤ ⌊L/h⌋ := Int.le_floor.mpr (by
    push_cast
    exact (neg_le_abs _).trans hab)
  exact Finset.mem_Icc.mpr ⟨by linarith only [hl],hu⟩

lemma mem_alphabet {n : ℕ} {h L : ℝ} (hh : 0 < h) (x : Space n) :
    x ∈ alphabet n h L ↔ (∃ z : Fin n → ℤ,x = latticePoint h z) ∧ ‖x‖ ≤ L := by
  classical
  constructor
  · intro hx
    obtain ⟨hm,hL⟩ := Finset.mem_filter.mp hx
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hm
    exact ⟨⟨z,hz.symm⟩,hL⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z,latticePoint_mem_box hh z hz,rfl⟩,hz⟩

lemma rounded_mem_alphabet {n : ℕ} {h L : ℝ} (hh : 0 < h) (x : Space n)
    (hx : ‖x‖+Real.sqrt n*h/2 ≤ L) : rounded h x ∈ alphabet n h L := by
  apply (mem_alphabet hh _).mpr
  refine ⟨⟨fun i => round (x i/h),rfl⟩,?_⟩
  have hh' : ‖rounded h x‖ ≤ ‖x‖+‖x-rounded h x‖ := by
    have he : rounded h x = x-(x-rounded h x) := by abel
    conv_lhs => rw [he]
    exact norm_sub_le x (x-rounded h x)
  exact (hh'.trans (add_le_add_right (rounding_error hh x) ‖x‖)).trans hx

lemma alphabet_card {n : ℕ} {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    ((alphabet n h L).card:ℝ) ≤ (1+2*L/h)^n := by
  classical
  have hn : (alphabet n h L).card ≤ (integerBox n ⌊L/h⌋).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hc : (integerBox n ⌊L/h⌋).card = (⌊L/h⌋+1-(-⌊L/h⌋)).toNat^n := by
    simp [integerBox,Fintype.card_piFinset,Int.card_Icc]
  have hm : 0 ≤ ⌊L/h⌋ := Int.floor_nonneg.mpr (div_nonneg hL hh.le)
  have hz : 0 ≤ ⌊L/h⌋+1-(-⌊L/h⌋) := by omega
  have hcast : ((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ) = (⌊L/h⌋:ℝ)+1-(-(⌊L/h⌋:ℝ)) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hz]
    push_cast
    rfl
  have hb : ((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ) ≤ 1+2*L/h := by
    rw [hcast]
    have hf := Int.floor_le (L/h)
    rw [mul_div_assoc]
    linarith only [hf]
  calc
    _ ≤ ((integerBox n ⌊L/h⌋).card:ℝ) := by exact_mod_cast hn
    _ = (((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ))^n := by rw [hc,Nat.cast_pow]
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hb _

abbrev BoundedLists (n : ℕ) (h L : ℝ) (N : ℕ) :=
  (m : Fin (N+1)) × (Fin m.val → {x // x ∈ alphabet n h L})

lemma boundedLists_card (n N : ℕ) (h L : ℝ) :
    Fintype.card (BoundedLists n h L N) ≤ (N+1)*max 1 (alphabet n h L).card^N := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_coe,Fintype.card_fin]
  calc
    _ ≤ ∑ _m : Fin (N+1), max 1 (alphabet n h L).card^N := Finset.sum_le_sum fun i _ => by
      calc
        _ ≤ max 1 (alphabet n h L).card^i.val := Nat.pow_le_pow_left (le_max_right _ _) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    _ = _ := by simp

end LocalizationRounding

end OAI
