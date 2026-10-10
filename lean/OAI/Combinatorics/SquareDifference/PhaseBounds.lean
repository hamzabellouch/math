import OAI.Combinatorics.SquareDifference.CircleDistance

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma linear_phase_sum_bound (t : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ phaseBound L t := by
  unfold phaseBound
  split_ifs with ht
  · exact linear_phase_sum_trivial t L
  · refine le_min (linear_phase_sum_trivial t L) ?_
    have htp : 0 < circleDistance t := lt_of_le_of_ne (circleDistance_nonneg t) (Ne.symm ht)
    refine (linear_phase_sum_distance t L htp).trans ?_
    rw [one_div]
    exact inv_anti₀ htp (by linarith)

noncomputable def distanceBucket (q : ℕ) (t : ℝ) : ℕ :=
  ⌊2*(q : ℝ)*circleDistance t⌋₊

lemma distanceBucket_le (q : ℕ) (t : ℝ) : distanceBucket q t ≤ q := by
  apply Nat.floor_le_of_le
  have := circleDistance_le_half t
  nlinarith [Nat.cast_nonneg (α := ℝ) q]

lemma distanceBucket_same_close {q : ℕ} (hq : 0 < q) {s t : ℝ}
    (h : distanceBucket q s = distanceBucket q t)
    (hsign : (0 ≤ s-round s) ↔ (0 ≤ t-round t)) :
    circleDistance (s-t) < 1/(2*(q : ℝ)) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hl (x : ℝ) : (distanceBucket q x : ℝ) ≤ 2*q*circleDistance x :=
    Nat.floor_le (mul_nonneg (by positivity) (circleDistance_nonneg x))
  have hu (x : ℝ) : 2*q*circleDistance x < (distanceBucket q x : ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hab : |circleDistance s-circleDistance t| < 1/(2*(q : ℝ)) := by
    rw [abs_lt]
    constructor
    · have hc : circleDistance t-circleDistance s < 1/(2*(q : ℝ)) := by
        rw [lt_div_iff₀ (by positivity)]
        have := hl s
        have := hu t
        rw [← h] at this
        nlinarith
      linarith
    · rw [lt_div_iff₀ (by positivity)]
      have := hl t
      have := hu s
      rw [h] at this
      nlinarith
  apply (circleDistance_sub_le s t).trans_lt
  have he : |(s-round s)-(t-round t)| = |circleDistance s-circleDistance t| := by
    unfold circleDistance
    by_cases hs : 0 ≤ s-round s
    · rw [abs_of_nonneg hs, abs_of_nonneg (hsign.mp hs)]
    · have ht : t-round t < 0 := lt_of_not_ge (fun ht => hs (hsign.mpr ht))
      rw [abs_of_neg (lt_of_not_ge hs), abs_of_neg ht]
      rw [← abs_neg]
      congr 1
      ring
  rwa [he]

noncomputable def bucketWeight (q : ℕ) (M : ℝ) (k : ℕ) : ℝ :=
  if k=0 then M else 2*q/(k : ℝ)

lemma phaseBound_le_bucketWeight (q : ℕ) (M t : ℝ) :
    phaseBound M t ≤ bucketWeight q M (distanceBucket q t) := by
  unfold bucketWeight
  split_ifs with hk
  · exact phaseBound_le M t
  · have hkpos : 0 < (distanceBucket q t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hl : (distanceBucket q t : ℝ) ≤ 2*q*circleDistance t :=
      Nat.floor_le (mul_nonneg (by positivity) (circleDistance_nonneg t))
    have ht : 0 < circleDistance t := by
      by_contra hn
      have hz : circleDistance t = 0 := le_antisymm (le_of_not_gt hn) (circleDistance_nonneg t)
      rw [hz, mul_zero] at hl
      linarith
    unfold phaseBound
    rw [ite_eq_right (ne_of_gt ht)]
    apply (min_le_right _ _).trans
    apply (le_div_iff₀ hkpos).mpr
    rw [inv_mul_eq_div, div_le_iff₀ ht]
    exact hl

lemma separated_phaseBound_sum {I : Type*} [Fintype I]
    (q : ℕ) (hq : 0 < q) (M : ℝ) (hM : 0 ≤ M) (t : I → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/(2*(q : ℝ)) ≤ circleDistance (t i-t j)) :
    ∑ i, phaseBound M (t i) ≤ 2*M + 4*q*(harmonic q : ℝ) := by
  classical
  let e : I → Fin (q+1) × Bool := fun i =>
    (⟨distanceBucket q (t i), Nat.lt_succ_of_le (distanceBucket_le q (t i))⟩,
      decide (0 ≤ t i-round (t i)))
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have hb : distanceBucket q (t i)=distanceBucket q (t j) :=
      congrArg (fun x : Fin (q+1) × Bool => x.1.val) hij
    have hs : (0 ≤ t i-round (t i)) ↔ (0 ≤ t j-round (t j)) := by
      have hh := congrArg Prod.snd hij
      exact decide_eq_decide.mp hh
    exact (not_lt_of_ge (hsep i j hne)) (distanceBucket_same_close hq hb hs)
  calc
    _ ≤ ∑ i, bucketWeight q M (e i).1.val :=
      sum_le_sum fun i _ => phaseBound_le_bucketWeight q M (t i)
    _ = ∑ j ∈ univ.image e, bucketWeight q M j.1.val := by
      rw [sum_image]
      exact Set.injOn_of_injective hinj
    _ ≤ ∑ j : Fin (q+1) × Bool, bucketWeight q M j.1.val := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro j _ _
      unfold bucketWeight
      split_ifs
      · exact hM
      · positivity
    _ = 2*M + 4*q*(harmonic q : ℝ) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, ← two_mul]
      rw [← mul_sum]
      rw [Fin.sum_univ_eq_sum_range]
      rw [sum_range_succ']
      simp only [bucketWeight, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      rw [← mul_sum]
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv]
      push_cast
      ring

lemma circleDistance_lipschitz (s t : ℝ) : circleDistance s ≤ circleDistance t + |s-t| := by
  calc
    _ ≤ |s-round t| := circleDistance_le_abs_sub_int s (round t)
    _ = |(t-round t)+(s-t)| := by congr 1; ring
    _ ≤ |t-round t|+|s-t| := abs_add_le _ _

lemma rational_circleDistance_lower (k : ℤ) (q : ℕ) (hq : 0 < q)
    (hnd : ¬ (q : ℤ) ∣ k) : 1/(q : ℝ) ≤ circleDistance ((k : ℝ)/q) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  let n := round ((k : ℝ)/q)
  have hn : k-(q : ℤ)*n ≠ 0 := by
    intro he
    apply hnd
    exact ⟨n, by linarith⟩
  have hI : (1 : ℤ) ≤ |k-(q : ℤ)*n| := by
    have := abs_pos.mpr hn
    omega
  have hR : (1 : ℝ) ≤ |(k : ℝ)-(q : ℝ)*(n : ℝ)| := by exact_mod_cast hI
  have he : |(k : ℝ)-(q : ℝ)*(n : ℝ)| = (q : ℝ)*circleDistance ((k : ℝ)/q) := by
    calc
      _ = |(q : ℝ)*((k : ℝ)/q-(n : ℝ))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hqR]; rfl
  rw [he] at hR
  exact (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hR)

lemma rational_quadratic_spacing (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (h : ℤ) (h0 : h ≠ 0) (hh : 4*|h| < (q : ℤ)) :
    1/(2*(q : ℝ)) ≤ circleDistance (2*α*h) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hnd : ¬ (q : ℤ) ∣ 2*a*h := by
    intro hd
    have hd' : (q : ℤ) ∣ 2*h := hc.symm.dvd_of_dvd_mul_left (by rwa [show a*(2*h)=2*a*h by ring])
    have hab : |2*h| < (q : ℤ) := by rw [abs_mul]; norm_num at *; omega
    have hpos : 0 < |2*h| := abs_pos.mpr (mul_ne_zero (by norm_num) h0)
    exact (not_le_of_gt hab) (Int.le_of_dvd hpos ((dvd_abs _ _).mpr hd'))
  have hr := rational_circleDistance_lower (2*a*h) q hq hnd
  push_cast at hr
  have hdiff : |((2 : ℝ)*a*h)/q-2*α*h| ≤ 1/(2*(q : ℝ)) := by
    have he : (2 : ℝ)*a*h/q-2*α*h = -(2*h*(α-(a : ℝ)/q)) := by ring
    rw [he, abs_neg, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left ha (abs_nonneg (2*(h : ℝ)))
    apply hmul.trans
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have hhr : 4*|(h : ℝ)| < (q : ℝ) := by exact_mod_cast hh
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp
    nlinarith
  have hl := circleDistance_lipschitz (((2 : ℝ)*a*h)/q) (2*α*h)
  have hqeq : 1/(q : ℝ)=2*(1/(2*(q : ℝ))) := by ring
  rw [hqeq] at hr
  linarith

lemma sum_range_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (b k : ℕ) :
    ∑ n ∈ range (b*k), f n = ∑ i ∈ range k, ∑ j ∈ range b, f (b*i+j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma quadratic_block_bound (α : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M : ℕ) (x : ℝ) :
    ∑ j ∈ range (q/4), phaseBound M (2*α*(x+j)) ≤
      2*M+4*q*(harmonic q : ℝ) := by
  have hqpos : 0 < q := by omega
  have hbq : 4*(q/4) ≤ q := by omega
  let b := q/4
  have hs := separated_phaseBound_sum q hqpos (M : ℝ) (Nat.cast_nonneg M)
    (fun j : Fin b => 2*α*(x+j))
  rw [← Fin.sum_univ_eq_sum_range]
  apply hs
  intro j k hjk
  have hh0 : (j : ℤ)-(k : ℤ) ≠ 0 := by
    intro he
    apply hjk
    exact Fin.ext (by exact_mod_cast sub_eq_zero.mp he)
  have hj : (j : ℤ) < (b : ℤ) := by exact_mod_cast j.isLt
  have hk : (k : ℤ) < (b : ℤ) := by exact_mod_cast k.isLt
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hab : |(j : ℤ)-(k : ℤ)| ≤ (b : ℤ)-1 := abs_le.mpr ⟨by omega, by omega⟩
  have hbqI : 4*(b : ℤ) ≤ (q : ℤ) := by exact_mod_cast hbq
  have hsmall : 4*|(j : ℤ)-(k : ℤ)| < (q : ℤ) := by omega
  have hr := rational_quadratic_spacing α a q hqpos hc ha _ hh0 hsmall
  convert hr using 1
  push_cast
  congr 1
  ring

lemma rational_spacing_sum (α : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M : ℕ) :
    ∑ j ∈ range M, phaseBound M (2*α*j) ≤
      (8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)) := by
  let b := q/4
  have hb : 0 < b := by dsimp [b]; omega
  have hcover : M ≤ b*(M/b+1) := by
    have := Nat.mod_lt M hb
    have := Nat.mod_add_div M b
    nlinarith
  have hsum : ∑ j ∈ range M, phaseBound M (2*α*j) ≤
      ((M/b+1 : ℕ) : ℝ)*(2*M+4*q*(harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ range (b*(M/b+1)), phaseBound M (2*α*j) :=
        sum_le_sum_of_subset_of_nonneg (range_mono hcover) (fun _ _ _ =>
          phaseBound_nonneg (Nat.cast_nonneg _) _)
      _ = ∑ i ∈ range (M/b+1), ∑ j ∈ range b, phaseBound M (2*α*(b*i+j)) := by
        rw [sum_range_blocks]
        simp only [Nat.cast_add, Nat.cast_mul]
      _ ≤ ∑ _i ∈ range (M/b+1), (2*M+4*q*(harmonic q : ℝ)) := by
        apply sum_le_sum
        intro i _
        exact quadratic_block_bound α a q (by omega) hc ha M ((b : ℝ)*i)
      _ = _ := by simp; ring
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0<q by omega)
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hqb : (q : ℝ) ≤ 8*b := by
    have hi : q ≤ 8*b := by dsimp [b]; omega
    exact_mod_cast hi
  have hnum : ((M/b+1 : ℕ) : ℝ) ≤ 8*(M : ℝ)/q+1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply add_le_add _ le_rfl
    apply Nat.cast_div_le.trans
    apply (div_le_div_iff₀ hbR hqR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hlog : 0 ≤ 1+Real.log (q : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast (show 1≤q by omega))
    linarith
  apply hsum.trans
  apply mul_le_mul hnum _ _ _
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (by positivity)
  · have hharm : 0 ≤ (harmonic q : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv]
      positivity
    positivity
  · positivity

lemma sum_triangle_differences {A : Type*} [AddCommMonoid A]
    (f : ℕ → ℕ → A) (L : ℕ) :
    (∑ n ∈ range L, ∑ m ∈ range n, f m n) =
      ∑ j ∈ Ico 1 L, ∑ m ∈ range (L-j), f m (m+j) := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x : Σ _ : ℕ, ℕ => ⟨x.1-x.2,x.2⟩)
    (fun x : Σ _ : ℕ, ℕ => ⟨x.2+x.1,x.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_sigma, mem_range, mem_Ico] at hx ⊢
    omega
  · intro x hx
    simp only [mem_sigma, mem_range, mem_Ico] at hx ⊢
    omega
  · rintro ⟨n,m⟩ hx
    simp only [mem_sigma, mem_range] at hx
    apply Sigma.ext (by dsimp; omega)
    rfl
  · rintro ⟨j,m⟩ _
    apply Sigma.ext (by dsimp; omega)
    rfl
  · rintro ⟨n,m⟩ hx
    simp only [mem_sigma, mem_range] at hx
    change f m n = f m (m+(n-m))
    congr 1
    omega

lemma complex_sum_square_identity (z : ℕ → ℂ) (L : ℕ)
    (hz : ∀ n < L, ‖z n‖=1) :
    (∑ n ∈ range L, z n) * conj (∑ n ∈ range L, z n) =
      (L : ℂ) + (∑ n ∈ range L, ∑ m ∈ range n, z n*conj (z m)) +
        conj (∑ n ∈ range L, ∑ m ∈ range n, z n*conj (z m)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hi := ih (fun n hn => hz n (Nat.lt_succ_of_lt hn))
    have hn : z L*conj (z L)=1 := by simp only [Complex.mul_conj', hz L (Nat.lt_succ_self _), Complex.ofReal_one, one_pow]
    simp only [sum_range_succ, Nat.cast_add, Nat.cast_one, map_add]
    rw [add_mul, mul_add, mul_add, hi, hn]
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    simp only [← mul_sum]
    ring

lemma norm_sum_square_differencing (z : ℕ → ℂ) (L : ℕ)
    (hz : ∀ n < L, ‖z n‖=1) :
    ‖∑ n ∈ range L, z n‖^2 ≤ (L : ℝ) +
      2 * ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), z (m+j)*conj (z m)‖ := by
  have hid := congrArg Complex.re (complex_sum_square_identity z L hz)
  rw [Complex.mul_conj'] at hid
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.add_re, Complex.natCast_re, Complex.conj_re] at hid
  rw [sum_triangle_differences (fun m n => z n*conj (z m)) L] at hid
  have hle : (∑ j ∈ Ico 1 L, ∑ m ∈ range (L-j), z (m+j)*conj (z m)).re ≤
      ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), z (m+j)*conj (z m)‖ := by
    rw [Complex.re_sum]
    exact sum_le_sum fun j _ => Complex.re_le_norm _
  linarith

lemma quadratic_correlation (α θ : ℝ) (j L : ℕ) :
    ‖∑ m ∈ range L, expPhase (α*(m+j)^2+θ*(m+j)) *
      conj (expPhase (α*m^2+θ*m))‖ =
      ‖∑ m ∈ range L, expPhase (m*(2*α*j))‖ := by
  simp_rw [← expPhase_sub]
  have he (m : ℕ) : α*((m : ℝ)+j)^2+θ*((m : ℝ)+j)-(α*m^2+θ*m) =
      (α*j^2+θ*j)+m*(2*α*j) := by ring
  simp_rw [he, expPhase_add, ← mul_sum, norm_mul, norm_expPhase, one_mul]

lemma phaseBound_mono {M N : ℝ} (hMN : M ≤ N) (t : ℝ) :
    phaseBound M t ≤ phaseBound N t := by
  unfold phaseBound
  split_ifs
  · exact hMN
  · exact min_le_min_right _ hMN

lemma quadratic_sum_differencing (α θ : ℝ) (L M : ℕ) (hLM : L ≤ M) :
    ‖∑ m ∈ range L, expPhase (α*m^2+θ*m)‖^2 ≤ (M : ℝ) +
      2 * ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) := by
  apply (norm_sum_square_differencing (fun m => expPhase (α*m^2+θ*m)) L
    (fun _ _ => norm_expPhase _)).trans
  apply add_le_add (Nat.cast_le.mpr hLM)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), expPhase (m*(2*α*j))‖ := by
      apply sum_congr rfl
      intro j _
      simp only [Nat.cast_add]
      exact quadratic_correlation α θ j (L-j)
    _ ≤ ∑ j ∈ Ico 1 L, phaseBound M (2*α*j) := by
      apply sum_le_sum
      intro j _
      exact (linear_phase_sum_bound (2*α*j) (L-j)).trans
        (phaseBound_mono (Nat.cast_le.mpr ((Nat.sub_le L j).trans hLM)) _)
    _ ≤ ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) := by
      apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hLM)
      intro i _ _
      exact phaseBound_nonneg (Nat.cast_nonneg _) _

lemma expPhase_lipschitz (s t : ℝ) : ‖expPhase s-expPhase t‖ ≤ 2*Real.pi*|s-t| := by
  have he : expPhase s-expPhase t = (expPhase (s-t)-1)*expPhase t := by
    rw [sub_mul, one_mul, ← expPhase_add, sub_add_cancel]
  rw [he, norm_mul, norm_expPhase, mul_one]
  change ‖Complex.exp (↑(2*Real.pi*(s-t))*Complex.I)-1‖ ≤ _
  rw [mul_comm _ Complex.I]
  convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(s-t)) using 1
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]

lemma periodic_zero_prefix (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (hz : ∑ m ∈ range T, a m = 0)
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ m, ‖a m‖ ≤ B) (L : ℕ) :
    ‖∑ m ∈ range L, a m‖ ≤ T*B := by
  have hperiod (k j : ℕ) : a (T*k+j) = a j := by
    simpa [mul_comm, add_comm] using hp.nat_mul k j
  rw [← Nat.mod_add_div L T, add_comm, sum_range_add, sum_range_blocks]
  simp_rw [hperiod, hz, sum_const_zero, zero_add]
  calc
    _ ≤ ∑ _m ∈ range (L%T), B := (norm_sum_le _ _).trans (sum_le_sum (fun m _ => ha m))
    _ ≤ (T : ℝ)*B := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mod_lt L hT).le) hB

lemma norm_periodicMean (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (B : ℝ) (ha : ∀ m, ‖a m‖ ≤ B) : ‖periodicMean a T‖ ≤ B := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  unfold periodicMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (T : ℝ)⁻¹ * ∑ _m ∈ range T, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum (fun m _ => ha m)))
        (inv_nonneg.mpr hTR.le)
    _ = B := by simp [ne_of_gt hTR]

lemma periodic_prefix_error (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (L : ℕ) :
    ‖∑ m ∈ range L, a m-(L : ℂ)*periodicMean a T‖ ≤ 2*T*B := by
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hμ := norm_periodicMean a T hT B ha
  have hz : ∑ m ∈ range T, (a m-periodicMean a T) = 0 := by
    simp [sum_sub_distrib, periodicMean, mul_inv_cancel_left₀ hTC]
  have hc : Function.Periodic (fun m => a m-periodicMean a T) T := by
    intro m; dsimp; rw [hp m]
  have hh := periodic_zero_prefix (fun m => a m-periodicMean a T) T hT hc hz
    (2*B) (by positivity) (fun m => by linarith [norm_sub_le (a m) (periodicMean a T), ha m]) L
  convert hh using 1
  · simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  · ring

lemma norm_weighted_partial_bound (a f : ℕ → ℂ) (L : ℕ) (B : ℝ)
    (_hB : 0 ≤ B) (ha : ∀ K ≤ L, ‖∑ m ∈ range K, a m‖ ≤ B) :
    ‖∑ m ∈ range L, f m*a m‖ ≤
      B*(‖f (L-1)‖+∑ m ∈ range (L-1), ‖f (m+1)-f m‖) := by
  change ‖∑ m ∈ range L, f m • a m‖ ≤ _
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖f (L-1)‖*‖∑ m ∈ range L, a m‖+
        ∑ m ∈ range (L-1), ‖f (m+1)-f m‖*‖∑ j ∈ range (m+1), a j‖ := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (le_of_eq (by simp)))
    _ ≤ ‖f (L-1)‖*B+∑ m ∈ range (L-1), ‖f (m+1)-f m‖*B := by
      apply add_le_add (mul_le_mul_of_nonneg_left (ha L le_rfl) (norm_nonneg _))
      apply sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ha (m+1) (by have := mem_range.mp hm; omega)
    _ = _ := by rw [← sum_mul]; ring

noncomputable def squareWeight (N : ℕ) (y : ℝ) (m : ℕ) : ℂ :=
  (2*((m : ℝ)+1)/(N : ℝ)) • expPhase (y*(m+1)^2)

lemma norm_squareWeight (N : ℕ) (y : ℝ) (m : ℕ) :
    ‖squareWeight N y m‖ = 2*((m : ℝ)+1)/N := by
  unfold squareWeight
  rw [norm_smul, norm_expPhase, mul_one, Real.norm_of_nonneg (by positivity)]

lemma squareWeight_difference (N : ℕ) (y : ℝ) (m : ℕ) :
    ‖squareWeight N y (m+1)-squareWeight N y m‖ ≤
      2/(N : ℝ) + (2*((m : ℝ)+1)/N)*(2*Real.pi*|y| *(2*m+3)) := by
  have he : squareWeight N y (m+1)-squareWeight N y m =
      (2/(N : ℝ)) • expPhase (y*(m+2)^2)+
      (2*((m : ℝ)+1)/N) • (expPhase (y*(m+2)^2)-expPhase (y*(m+1)^2)) := by
    unfold squareWeight
    simp only [Nat.cast_add, Nat.cast_one, smul_sub]
    rw [show (m : ℝ)+1+1=m+2 by ring]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, norm_expPhase, mul_one]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2/(N : ℝ)),
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*((m : ℝ)+1)/N)]
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left _ (by positivity))
  apply (expPhase_lipschitz _ _).trans
  rw [show y*((m : ℝ)+2)^2-y*((m : ℝ)+1)^2=y*(2*m+3) by ring,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*(m : ℝ)+3)]
  apply le_of_eq
  ring

lemma squareWeight_variation (N M : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    ‖squareWeight N y (M-1)‖+
      ∑ m ∈ range (M-1), ‖squareWeight N y (m+1)-squareWeight N y m‖ ≤
      (4+8*Real.pi*|y| *(M : ℝ)^2)*M/N := by
  have hlast : ((M-1 : ℕ) : ℝ)+1=M := by exact_mod_cast Nat.sub_add_cancel hM
  rw [norm_squareWeight, hlast]
  calc
    _ ≤ 2*(M : ℝ)/N + ∑ _m ∈ range (M-1),
        (2/(N : ℝ)+8*Real.pi*|y| *(M : ℝ)^2/N) := by
      apply add_le_add le_rfl (sum_le_sum _)
      intro m hm
      apply (squareWeight_difference N y m).trans
      apply add_le_add le_rfl
      have hmR : (m : ℝ)+2 ≤ M := by exact_mod_cast (show m+2 ≤ M by
        have := mem_range.mp hm; omega)
      calc
        _ ≤ (2*(M : ℝ)/N)*(2*Real.pi*|y| *(2*M)) := by
          gcongr <;> linarith
        _ = _ := by ring
    _ ≤ 2*(M : ℝ)/N+(M : ℝ)*(2/(N : ℝ)+8*Real.pi*|y| *(M : ℝ)^2/N) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M 1)) (by positivity)
    _ = _ := by ring

lemma periodic_squareWeight_error (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (M N : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*(∑ m ∈ range M, squareWeight N y m)‖ ≤
      (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
  have hb : ∀ K ≤ M, ‖∑ m ∈ range K, (a m-periodicMean a T)‖ ≤ 2*T*B := by
    intro K _
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] using
      periodic_prefix_error a T hT hp B hB ha K
  have hh := norm_weighted_partial_bound (fun m => a m-periodicMean a T)
    (squareWeight N y) M (2*T*B) (by positivity) hb
  have he : (∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*(∑ m ∈ range M, squareWeight N y m) =
      ∑ m ∈ range M, squareWeight N y m*(a m-periodicMean a T) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, mul_comm (periodicMean a T)]
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left (squareWeight_variation N M hM y) (by positivity))

end SquareDifference
end

end OAI
