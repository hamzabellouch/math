import OAI.NumberTheory.GaussianMoat.FiniteLaw

namespace OAI

namespace GaussianMoat

section
open scoped BigOperators

def colorEdge (a b : Fin 3) : ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

def Tricolored (a b c : Fin 3) : Prop := a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem colorEdge_add {a b c : Fin 3} (h : ¬ Tricolored a b c) :
    colorEdge a b + colorEdge b c = colorEdge a c := by
  unfold Tricolored at h
  revert a b c
  decide

theorem colorEdge_zero_left (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_zero_one (a b : Fin 3) (ha : a ≠ 1) (hb : b ≠ 1) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_binary (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) :
    colorEdge a b = (b.val : ℤ) - a.val := by
  revert a b
  decide

theorem discrete_rectangle_sperner (c : ℕ → ℕ → Fin 3) (m n : ℕ)
    (hbottom : ∀ i ≤ m, c i 0 = 0)
    (htop : ∀ i ≤ m, c i n ≠ 0)
    (hleft : ∀ j ≤ n, c 0 j ≠ 2)
    (hright : ∀ j ≤ n, c m j ≠ 1) :
    ∃ i < m, ∃ j < n,
      Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) ∨
      Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) := by
  by_contra h
  have hcell (i j : ℕ) (hi : i < m) (hj : j < n) :
      colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)) =
      colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)) := by
    have h1 : ¬ Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inl hh⟩
    have h2 : ¬ Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inr hh⟩
    have he1 := colorEdge_add h1
    have he2 := colorEdge_add h2
    omega
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun j hj =>
    Finset.sum_congr (s₁ := Finset.range m) rfl (fun i hi =>
      hcell i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))
  have hl : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.sum_range_sub']
    rw [hbottom i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      hbottom (i+1) (Finset.mem_range.mp hi)]
    rw [colorEdge_zero_left _ _ (htop i (Nat.le_of_lt (Finset.mem_range.mp hi)))
      (htop (i+1) (Finset.mem_range.mp hi))]
    rfl
  have hr : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)))) = 1 := by
    have he (j : ℕ) (hj : j ∈ Finset.range n) :
        (∑ i ∈ Finset.range m, (colorEdge (c i j) (c i (j+1)) -
          colorEdge (c (i+1) j) (c (i+1) (j+1)))) = ((c 0 (j+1)).val : ℤ) - (c 0 j).val := by
      rw [Finset.sum_range_sub']
      rw [colorEdge_zero_one _ _ (hright j (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (hright (j+1) (Finset.mem_range.mp hj)),sub_zero,
        colorEdge_binary _ _ (hleft j (Nat.le_of_lt (Finset.mem_range.mp hj)))
          (hleft (j+1) (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl he,Finset.sum_range_sub (fun j => ((c 0 j).val : ℤ))]
    have hend : c 0 n = 1 := by
      have h0 := htop 0 (Nat.zero_le m)
      have h2 := hleft n le_rfl
      have hone : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
      exact hone _ h0 h2
    rw [hend,hbottom 0 (Nat.zero_le m)]
    norm_num
  rw [hl,hr] at hsum
  omega

noncomputable def pointColor (z : ℂ) : Fin 3 := if z.im < 0 then 0 else if z.re < 0 then 1 else 2

theorem pointColor_zero {z : ℂ} (h : pointColor z = 0) : z.im < 0 := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact hi
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) h)

theorem pointColor_one {z : ℂ} (h : pointColor z = 1) : z.re < 0 ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
  · exact ⟨hr,le_of_not_gt hi⟩
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) h)

theorem pointColor_two {z : ℂ} (h : pointColor z = 2) : 0 ≤ z.re ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h)
  · exact ⟨le_of_not_gt hr,le_of_not_gt hi⟩

theorem tricolored_covers {a b c : Fin 3} (h : Tricolored a b c) (q : Fin 3) :
    q = a ∨ q = b ∨ q = c := by
  unfold Tricolored at h
  revert a b c q
  decide

theorem tricolored_norm_bound {x y z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hxy : dist x y ≤ r) (hxz : dist x z ≤ r)
    (hc : Tricolored (pointColor x) (pointColor y) (pointColor z)) : ‖x‖ ≤ 2*r := by
  have he (q : Fin 3) : ∃ w : ℂ, pointColor w = q ∧ dist x w ≤ r := by
    rcases tricolored_covers hc q with h | h | h
    · exact ⟨x,h.symm,by simpa using hr⟩
    · exact ⟨y,h.symm,hxy⟩
    · exact ⟨z,h.symm,hxz⟩
  obtain ⟨w0,h0,hd0⟩ := he 0
  obtain ⟨w1,h1,hd1⟩ := he 1
  obtain ⟨w2,h2,hd2⟩ := he 2
  have hc0 := pointColor_zero h0
  have hc1 := pointColor_one h1
  have hc2 := pointColor_two h2
  have hRe (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.re-w.re ∧ x.re-w.re ≤ r := by
    apply abs_le.mp
    have hh : |x.re-w.re| ≤ dist x w := by simpa only [Complex.sub_re,dist_eq_norm] using Complex.abs_re_le_norm (x-w)
    exact hh.trans hd
  have hIm (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.im-w.im ∧ x.im-w.im ≤ r := by
    apply abs_le.mp
    have hh : |x.im-w.im| ≤ dist x w := by simpa only [Complex.sub_im,dist_eq_norm] using Complex.abs_im_le_norm (x-w)
    exact hh.trans hd
  have hR1 := hRe w1 hd1
  have hR2 := hRe w2 hd2
  have hI0 := hIm w0 hd0
  have hI1 := hIm w1 hd1
  have hrx : |x.re| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have hix : |x.im| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im x
  linarith

theorem discrete_rectangle_approx_zero (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, (f i 0).im < 0)
    (htop : ∀ i ≤ m, 0 ≤ (f i n).im)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hb : ∀ i ≤ m, pointColor (f i 0) = 0 := by
    intro i hi
    simp [pointColor,hbottom i hi]
  have ht : ∀ i ≤ m, pointColor (f i n) ≠ 0 := by
    intro i hi hh
    exact (not_lt_of_ge (htop i hi)) (pointColor_zero hh)
  have hl : ∀ j ≤ n, pointColor (f 0 j) ≠ 2 := by
    intro j hj hh
    exact (not_le_of_gt (hleft j hj)) (pointColor_two hh).1
  have hr : ∀ j ≤ n, pointColor (f m j) ≠ 1 := by
    intro j hj hh
    exact (not_lt_of_ge (hright j hj)) (pointColor_one hh).1
  obtain ⟨i,hi,j,hj,hc⟩ := discrete_rectangle_sperner (fun i j => pointColor (f i j)) m n hb ht hl hr
  refine ⟨i,hi.le,j,hj.le,?_⟩
  have hdiag : dist (f i j) (f (i+1) (j+1)) ≤ 2*D := by
    have h := dist_triangle (f i j) (f (i+1) j) (f (i+1) (j+1))
    have h1 := hhor i hi j hj.le
    have h2 := hver (i+1) hi j hj
    linarith
  rcases hc with hc | hc
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hhor i hi j hj.le).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hver i hi.le j hj).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith

noncomputable def repeatPath (v : ℕ → ℂ) (n : ℕ) (a : ℂ) (t : ℕ) : ℂ :=
  v (t % n) + ((t / n : ℕ) : ℂ) * a

@[simp] theorem repeatPath_zero (v : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    repeatPath v n a 0 = v 0 := by simp [repeatPath]

@[simp] theorem repeatPath_multiple (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ) (k : ℕ) :
    repeatPath v n a (k*n) = v 0 + (k : ℂ)*a := by simp [repeatPath,hn.ne']

theorem repeatPath_step (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ)
    (hv0 : v 0 = 0) (hvn : v n = a) {D : ℝ}
    (hstep : ∀ i < n, dist (v i) (v (i+1)) ≤ D) (t : ℕ) :
    dist (repeatPath v n a t) (repeatPath v n a (t+1)) ≤ D := by
  have hr := Nat.mod_lt t hn
  have hdiv := Nat.mod_add_div t n
  by_cases hh : t % n + 1 = n
  · have ht : t+1 = (t/n+1)*n := by nlinarith
    rw [ht,repeatPath_multiple v hn]
    have he : repeatPath v n a t = v (t%n) + ((t/n:ℕ):ℂ)*a := rfl
    rw [he,hv0,zero_add,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (((t/n:ℕ):ℂ)*a) a]
    rw [dist_add_right]
    simpa [hh,hvn] using hstep (t%n) hr
  · have hr' : t%n+1 < n := by omega
    have ht : t+1 = t%n+1+(t/n)*n := by nlinarith
    have hmod : (t+1)%n = t%n+1 := by rw [ht,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr']
    have hquo : (t+1)/n = t/n := by rw [ht,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr',zero_add]
    simp only [repeatPath,hmod,hquo,dist_add_right]
    exact hstep (t%n) hr

theorem discrete_rectangle_approx_zero_rev (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, 0 < (f i 0).im)
    (htop : ∀ i ≤ m, (f i n).im ≤ 0)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hh : ∀ i < m, ∀ j ≤ n, dist (star (f i j)) (star (f (i+1) j)) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hhor i hi j hj
  have hv : ∀ i ≤ m, ∀ j < n, dist (star (f i j)) (star (f i (j+1))) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hver i hi j hj
  have hb : ∀ i ≤ m, (star (f i 0)).im < 0 := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_lt_zero] using hbottom i hi
  have ht : ∀ i ≤ m, 0 ≤ (star (f i n)).im := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_nonneg] using htop i hi
  obtain ⟨i,hi,j,hj,hz⟩ := discrete_rectangle_approx_zero (fun i j => star (f i j)) m n
    hD hh hv hb ht (by simpa only [Complex.star_def,Complex.conj_re] using hleft)
      (by simpa only [Complex.star_def,Complex.conj_re] using hright)
  exact ⟨i,hi,j,hj,by simpa only [norm_star] using hz⟩

theorem path_difference_cover (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : 0 < b.im) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  let H : ℝ := (∑ i ∈ Finset.range n, ‖v i‖) + (∑ j ∈ Finset.range m, ‖u j‖) + ‖w‖
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hvb (i : ℕ) : ‖v (i%n)‖ ≤ ∑ k ∈ Finset.range n, ‖v k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (v k)) (Finset.mem_range.mpr (Nat.mod_lt i hn))
  have hub (j : ℕ) : ‖u (j%m)‖ ≤ ∑ k ∈ Finset.range m, ‖u k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (u k)) (Finset.mem_range.mpr (Nat.mod_lt j hm))
  have herr (i j : ℕ) : ‖v (i%n)-u (j%m)-w‖ ≤ H := by
    have h1 := norm_sub_le (v (i%n)) (u (j%m))
    have h2 := norm_sub_le (v (i%n)-u (j%m)) w
    dsimp [H]
    linarith [hvb i,hub j]
  have hrerr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).re ∧
      (v (i%n)-u (j%m)-w).re ≤ H :=
    abs_le.mp ((Complex.abs_re_le_norm _).trans (herr i j))
  have hierr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).im ∧
      (v (i%n)-u (j%m)-w).im ≤ H :=
    abs_le.mp ((Complex.abs_im_le_norm _).trans (herr i j))
  obtain ⟨N,hN⟩ := exists_nat_gt (H/b.im)
  have hN' : H < (N:ℝ)*b.im := (div_lt_iff₀ hb).mp hN
  obtain ⟨M,hM⟩ := exists_nat_gt ((H+(N:ℝ)*|b.re|)/a.re)
  have hM' : H+(N:ℝ)*|b.re| < (M:ℝ)*a.re := (div_lt_iff₀ ha).mp hM
  let f (i j : ℕ) : ℂ := repeatPath v n a i-repeatPath u m b j-(M:ℂ)*a+(N:ℂ)*b-w
  have hf (i j : ℕ) : f i j = v (i%n)-u (j%m)-w +
      (((i/n:ℕ):ℂ)-(M:ℂ))*a + ((N:ℂ)-((j/m:ℕ):ℂ))*b := by
    dsimp [f,repeatPath]
    ring
  have hfr (i j : ℕ) : (f i j).re = (v (i%n)-u (j%m)-w).re +
      (((i/n:ℕ):ℝ)-(M:ℝ))*a.re + ((N:ℝ)-((j/m:ℕ):ℝ))*b.re := by
    rw [hf]
    simp
  have hfi (i j : ℕ) : (f i j).im = (v (i%n)-u (j%m)-w).im +
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.im := by
    rw [hf]
    simp [hai]
  have hhor (i : ℕ) (_ : i < 2*M*n) (j : ℕ) (_ : j ≤ 2*N*m) :
      dist (f i j) (f (i+1) j) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right] using repeatPath_step v hn a hv0 hvn hv i
  have hver (i : ℕ) (_ : i ≤ 2*M*n) (j : ℕ) (_ : j < 2*N*m) :
      dist (f i j) (f i (j+1)) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right,dist_sub_left] using repeatPath_step u hm b hu0 hum hu j
  have hbottom (i : ℕ) (_ : i ≤ 2*M*n) : 0 < (f i 0).im := by
    rw [hfi]
    simpa only [Nat.zero_div,Nat.cast_zero,sub_zero] using (show
      0 < (v (i%n)-u (0%m)-w).im+(N:ℝ)*b.im by linarith [(hierr i 0).1])
  have htop (i : ℕ) (_ : i ≤ 2*M*n) : (f i (2*N*m)).im ≤ 0 := by
    rw [hfi,Nat.mul_div_cancel _ hm,Nat.cast_mul,Nat.cast_ofNat]
    linarith [(hierr i (2*N*m)).2]
  have hcoef (j : ℕ) (hj : j ≤ 2*N*m) :
      |(N:ℝ)-((j/m:ℕ):ℝ)| ≤ N := by
    have hq : j/m ≤ 2*N := (Nat.div_le_div_right hj).trans_eq (Nat.mul_div_cancel _ hm)
    have hqr : ((j/m:ℕ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hq
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α := ℝ) (j/m)]⟩
  have hprod (j : ℕ) (hj : j ≤ 2*N*m) :
      -(N:ℝ)*|b.re| ≤ ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ∧
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ≤ (N:ℝ)*|b.re| := by
    have hh : |((N:ℝ)-((j/m:ℕ):ℝ))*b.re| ≤ (N:ℝ)*|b.re| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef j hj) (abs_nonneg _)
    simpa only [neg_mul] using abs_le.mp hh
  have hleft (j : ℕ) (hj : j ≤ 2*N*m) : (f 0 j).re < 0 := by
    rw [hfr]
    simp only [Nat.zero_div,Nat.cast_zero,zero_sub]
    nlinarith [(hrerr 0 j).2,(hprod j hj).2]
  have hright (j : ℕ) (hj : j ≤ 2*N*m) : 0 ≤ (f (2*M*n) j).re := by
    rw [hfr,Nat.mul_div_cancel _ hn,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [(hrerr (2*M*n) j).1,(hprod j hj).1]
  obtain ⟨i,_,j,_,hz⟩ := discrete_rectangle_approx_zero_rev f (2*M*n) (2*N*m)
    hD hhor hver hbottom htop hleft hright
  refine ⟨i%n,Nat.mod_lt i hn,j%m,Nat.mod_lt j hm,((i/n:ℕ):ℤ)-(M:ℤ),(N:ℤ)-((j/m:ℕ):ℤ),?_⟩
  convert hz using 1
  rw [hf]
  simp only [Int.cast_sub,Int.cast_natCast]
  congr 1
  ring

theorem path_difference_cover_horizontal (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : b.im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  rcases hb.lt_or_gt with hb | hb
  · have hzv : (fun i => star (v i)) 0 = 0 := by simp [hv0]
    have hzu : (fun i => star (u i)) 0 = 0 := by simp [hu0]
    have hva : (fun i => star (v i)) n = star a := by simp only [hvn]
    have hub : (fun i => star (u i)) m = star b := by simp only [hum]
    have hbr : 0 < (star b).im := by simpa using hb
    have hv' : ∀ i < n, dist (star (v i)) (star (v (i+1))) ≤ D := by simpa using hv
    have hu' : ∀ j < m, dist (star (u j)) (star (u (j+1))) ≤ D := by simpa using hu
    obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover (fun i => star (v i))
      (fun j => star (u j)) hn hm (star a) (star b) hzv hzu hva hub
      (by simpa using ha) (by simpa using hai) hbr hD hv' hu' (star w)
    refine ⟨i,hi,j,hj,s,t,?_⟩
    have he : ‖star (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)‖ ≤ 4*D := by
      simpa only [star_sub,star_add,star_mul,star_intCast,mul_comm] using hh
    simpa only [norm_star] using he
  · exact path_difference_cover v u hn hm a b hv0 hu0 hvn hum ha hai hb hD hv hu w

theorem path_difference_cover_general (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : a ≠ 0) (hb : (b/a).im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hv' : ∀ i < n, dist (v i/a) (v (i+1)/a) ≤ D/‖a‖ := by
    intro i hi
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hv i hi) hna.le
  have hu' : ∀ j < m, dist (u j/a) (u (j+1)/a) ≤ D/‖a‖ := by
    intro j hj
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hu j hj) hna.le
  obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover_horizontal (fun i => v i/a)
    (fun j => u j/a) hn hm 1 (b/a) (by simp [hv0]) (by simp [hu0])
    (by simp [hvn,ha]) (by simp [hum]) (by norm_num) (by simp) hb
    (by positivity : 0 ≤ D/‖a‖) hv' hu' (w/a)
  refine ⟨i,hi,j,hj,s,t,?_⟩
  have he : v i/a-u j/a+(s:ℂ)*1+(t:ℂ)*(b/a)-w/a =
      (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)/a := by field_simp
  rw [he,norm_div] at hh
  have hh' := (div_le_iff₀ hna).mp hh
  calc
    _ ≤ 4 * (D/‖a‖) * ‖a‖ := hh'
    _ = 4*D := by field_simp

end

def latticeCoords : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re,z.im]
  invFun v := ⟨v 0,v 1⟩
  left_inv z := by ext <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' c z := by
    ext i
    fin_cases i <;> simp [zsmul_eq_mul]

noncomputable def latticeBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map latticeCoords.symm

noncomputable instance : Module.Free ℤ GaussianInt := Module.Free.of_basis latticeBasis
instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis latticeBasis

noncomputable def twoVectorMap (a b : GaussianInt) : GaussianInt →ₗ[ℤ] GaussianInt :=
  Matrix.toLin latticeBasis latticeBasis !![a.re,b.re; a.im,b.im]

@[simp] theorem twoVectorMap_apply (a b z : GaussianInt) :
    twoVectorMap a b z = z.re • a + z.im • b := by
  apply latticeCoords.injective
  change latticeBasis.repr (twoVectorMap a b z) = latticeCoords (z.re • a+z.im • b)
  rw [twoVectorMap,Matrix.toLin_apply]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  ext i
  fin_cases i <;> simp [latticeCoords,latticeBasis,zsmul_eq_mul,Fin.sum_univ_two,Pi.basisFun_repr,Matrix.vecHead,Matrix.vecTail] <;> ring

@[simp] theorem twoVectorMap_det (a b : GaussianInt) :
    LinearMap.det (twoVectorMap a b) = a.re*b.im-a.im*b.re := by
  rw [← LinearMap.det_toMatrix latticeBasis,twoVectorMap,LinearMap.toMatrix_toLin]
  simp [Matrix.det_fin_two,mul_comm]

theorem twoVectorMap_injective {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    Function.Injective (twoVectorMap a b) := by
  intro z w hzw
  have h1 := congrArg Zsqrtd.re hzw
  have h2 := congrArg Zsqrtd.im hzw
  simp only [twoVectorMap_apply,zsmul_eq_mul,Zsqrtd.re_add,Zsqrtd.im_add,
    Zsqrtd.re_smul,Zsqrtd.im_smul] at h1 h2
  have hr : (a.re*b.im-a.im*b.re)*(z.re-w.re) = 0 := by linear_combination b.im*h1-b.re*h2
  have hi : (a.re*b.im-a.im*b.re)*(z.im-w.im) = 0 := by linear_combination a.re*h2-a.im*h1
  ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left h)

theorem twoVectorMap_quotient_card {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    Nat.card (GaussianInt ⧸ (twoVectorMap a b).range) = (a.re*b.im-a.im*b.re).natAbs := by
  have hh := Submodule.natAbs_det_equiv (twoVectorMap a b).range
    (LinearEquiv.ofInjective (twoVectorMap a b) (twoVectorMap_injective h))
  have he : (twoVectorMap a b).range.subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective (twoVectorMap a b)
        (twoVectorMap_injective h)) : GaussianInt →+ (twoVectorMap a b).range) = twoVectorMap a b := by
    ext z <;> rfl
  rw [he,twoVectorMap_det] at hh
  exact hh.symm

noncomputable def latticeBall (D : ℝ) : Finset GaussianInt :=
  (finite_dist_le 0 D).toFinset

@[simp] theorem mem_latticeBall (D : ℝ) (z : GaussianInt) :
    z ∈ latticeBall D ↔ ‖(z:ℂ)‖ ≤ D := by simp [latticeBall]

theorem complex_div_im_ne_zero {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    ((b:ℂ)/(a:ℂ)).im ≠ 0 := by
  have ha : a ≠ 0 := by intro hh; simp [hh] at h
  have hac : (a:ℂ) ≠ 0 := by simpa using ha
  have hn : Complex.normSq (a:ℂ) ≠ 0 := (Complex.normSq_pos.mpr hac).ne'
  rw [Complex.div_im,← sub_div]
  intro hh
  have hh' := (div_eq_zero_iff.mp hh).resolve_right hn
  have hz : (a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ) = 0 := by
    simpa only [← GaussianInt.intCast_re,← GaussianInt.intCast_im,mul_comm] using hh'
  apply h
  exact_mod_cast hz

theorem lattice_path_difference_cover (v u : ℕ → GaussianInt) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a b : GaussianInt)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (hab : a.re*b.im-a.im*b.re ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu : ∀ j < m, dist (u j:ℂ) (u (j+1):ℂ) ≤ D) (w : GaussianInt) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖((v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w:GaussianInt):ℂ)‖ ≤ 4*D := by
  have ha : a ≠ 0 := by intro hh; simp [hh] at hab
  obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover_general
    (fun i => (v i:ℂ)) (fun j => (u j:ℂ)) hn hm (a:ℂ) (b:ℂ)
    (by simp [hv0]) (by simp [hu0]) (by simp [hvn]) (by simp [hum])
    (by simpa using ha) (complex_div_im_ne_zero hab) hD hv hu (w:ℂ)
  exact ⟨i,hi,j,hj,s,t,by simpa using hh⟩

theorem lattice_path_difference_card (v u : ℕ → GaussianInt) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a b : GaussianInt)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (hab : a.re*b.im-a.im*b.re ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu : ∀ j < m, dist (u j:ℂ) (u (j+1):ℂ) ≤ D)
    (E : Finset GaussianInt) (hE : ∀ i < n, ∀ j < m, v i-u j ∈ E) :
    (a.re*b.im-a.im*b.re).natAbs ≤ E.card*(latticeBall (4*D)).card := by
  classical
  let Q := (twoVectorMap a b).range
  have hcard : Nat.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs :=
    twoVectorMap_quotient_card hab
  have : Finite (GaussianInt ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; simpa using hab)
  let : Fintype (GaussianInt ⧸ Q) := Fintype.ofFinite _
  let F : E × (latticeBall (4*D)) → GaussianInt ⧸ Q :=
    fun x => Q.mkQ (x.1.val+x.2.val)
  have hf : Function.Surjective F := by
    intro q
    obtain ⟨w,rfl⟩ := Q.mkQ_surjective q
    obtain ⟨i,hi,j,hj,s,t,hh⟩ := lattice_path_difference_cover v u hn hm a b hv0 hu0 hvn hum hab hD hv hu w
    let r : GaussianInt := -(v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w)
    have hr : r ∈ latticeBall (4*D) := by
      rw [mem_latticeBall]
      dsimp only [r]
      rw [map_neg,norm_neg]
      exact hh
    refine ⟨(⟨v i-u j,hE i hi j hj⟩,⟨r,hr⟩),?_⟩
    apply (Submodule.Quotient.eq Q).mpr
    change (v i-u j)+r-w ∈ (twoVectorMap a b).range
    refine ⟨⟨-s,-t⟩,?_⟩
    rw [twoVectorMap_apply]
    change (-s) • a + (-t) • b = _
    simp only [zsmul_eq_mul,Int.cast_neg]
    dsimp [r]
    ring
  have hh := Fintype.card_le_of_surjective F hf
  have hQ : Fintype.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs := by
    rw [← Nat.card_eq_fintype_card,hcard]
  simpa only [Fintype.card_prod,Fintype.card_coe,hQ] using hh

theorem lattice_norm_ge_one {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ ‖(z:ℂ)‖ := by
  have hi : 1 ≤ z.norm := by have := GaussianInt.norm_pos.mpr hz; omega
  have hr : (1:ℝ) ≤ (z.norm:ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm,Complex.normSq_eq_norm_sq] at hr
  nlinarith [norm_nonneg (z:ℂ)]

theorem lattice_dist_ge_one {z w : GaussianInt} (h : z ≠ w) :
    1 ≤ dist (z:ℂ) (w:ℂ) := by
  simpa only [map_sub,dist_eq_norm] using lattice_norm_ge_one (sub_ne_zero.mpr h)

noncomputable def latticePixel (e c : ℂ) (z : GaussianInt) : ℤ × ℤ :=
  (⌊2*(e*((z:ℂ)-c)).re⌋,⌊2*(e*((z:ℂ)-c)).im⌋)

theorem abs_sub_lt_half_of_pixel_eq {x y : ℝ} (h : ⌊2*x⌋ = ⌊2*y⌋) : |x-y| < 1/2 := by
  have h1 := Int.floor_le (2*x)
  have h2 := Int.lt_floor_add_one (2*x)
  have h3 := Int.floor_le (2*y)
  have h4 := Int.lt_floor_add_one (2*y)
  rw [h] at h1 h2
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem latticePixel_injective {e : ℂ} (he : ‖e‖ = 1) (c : ℂ) :
    Function.Injective (latticePixel e c) := by
  intro z w h
  have hr := abs_sub_lt_half_of_pixel_eq (congrArg Prod.fst h)
  have hi := abs_sub_lt_half_of_pixel_eq (congrArg Prod.snd h)
  have hn : ‖e*((z:ℂ)-c)-e*((w:ℂ)-c)‖ < 1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (e*((z:ℂ)-c)-e*((w:ℂ)-c))
    simp only [Complex.sub_re,Complex.sub_im] at hh
    change |(e*((z:ℂ)-c)).re-(e*((w:ℂ)-c)).re| < 1/2 at hr
    change |(e*((z:ℂ)-c)).im-(e*((w:ℂ)-c)).im| < 1/2 at hi
    linarith
  have heq : e*((z:ℂ)-c)-e*((w:ℂ)-c) = e*((z:ℂ)-(w:ℂ)) := by ring
  rw [heq,norm_mul,he,one_mul] at hn
  by_contra hne
  exact (not_lt_of_ge (lattice_dist_ge_one hne)) (by simpa only [dist_eq_norm] using hn)

theorem lattice_rectangle_card (E : Finset GaussianInt) {e c : ℂ} (he : ‖e‖ = 1)
    {R W : ℝ} (hR : 1 ≤ R) (hW : 1 ≤ W)
    (hE : ∀ z ∈ E, 0 ≤ (e*((z:ℂ)-c)).re ∧ (e*((z:ℂ)-c)).re ≤ R ∧
      |(e*((z:ℂ)-c)).im| ≤ W) :
    (E.card:ℝ) ≤ 18*R*W := by
  classical
  let B : Finset (ℤ × ℤ) := Finset.Icc 0 ⌊2*R⌋ ×ˢ Finset.Icc ⌊-2*W⌋ ⌊2*W⌋
  have hb : E.image (latticePixel e c) ⊆ B := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hz0,hzR,hzW⟩ := hE z hz
    have hzw := abs_le.mp hzW
    simp only [B,Finset.mem_product,Finset.mem_Icc,latticePixel]
    refine ⟨⟨?_,Int.floor_mono (by linarith)⟩,
      ⟨Int.floor_mono (by linarith),Int.floor_mono (by linarith)⟩⟩
    exact Int.floor_nonneg.mpr (by linarith)
  have hcard : E.card ≤ B.card := by
    rw [← Finset.card_image_iff.mpr (latticePixel_injective he c).injOn]
    exact Finset.card_le_card hb
  have hR0 : (0:ℤ) ≤ ⌊2*R⌋+1 := by
    have hh : (0:ℤ) ≤ ⌊2*R⌋ := Int.floor_nonneg.mpr (by linarith)
    omega
  have hW0 : ⌊-2*W⌋ ≤ ⌊2*W⌋+1 := by
    have hh : ⌊-2*W⌋ ≤ ⌊2*W⌋ := Int.floor_mono (by linarith)
    omega
  have hcr : ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) = (⌊2*R⌋:ℝ)+1 := by
    have h := Int.card_Icc_of_le 0 ⌊2*R⌋ hR0
    simp only [sub_zero] at h
    exact_mod_cast h
  have hcw : ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) = (⌊2*W⌋:ℝ)+1-(⌊-2*W⌋:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌊-2*W⌋ ⌊2*W⌋ hW0
  have hrb : ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) ≤ 3*R := by
    rw [hcr]
    linarith [Int.floor_le (2*R)]
  have hwb : ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) ≤ 6*W := by
    rw [hcw]
    linarith [Int.floor_le (2*W),Int.lt_floor_add_one (-2*W)]
  have hh : (E.card:ℝ) ≤ ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ)*
      ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) := by
    dsimp only [B] at hcard
    rw [Finset.card_product] at hcard
    exact_mod_cast hcard
  calc
    (E.card:ℝ) ≤ _ := hh
    _ ≤ (3*R)*(6*W) := mul_le_mul hrb hwb (Nat.cast_nonneg _) (by linarith)
    _ = 18*R*W := by ring

end GaussianMoat

end OAI
