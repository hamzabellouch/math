import Mathlib
import OAI.Probability.SKValue.Equations.HalflineComparison
import OAI.Probability.SKValue.Equations.BackwardPolynomials

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue.BackwardBurgers
variable (F : SKValue.BackwardBurgers)

lemma preserve_w (hinit : ∀ x,0≤x → F.jet 2 0 x≤0) {t x : ℝ}
    (ht : 0≤t) (hx : 0≤x) : F.jet 2 t x≤0 := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨C,hC,hc⟩ := F.bound 1
  obtain ⟨M,hM,hm⟩ := F.bound 2
  have hh := halfline_parabolic_nonneg (T := t) (B := B) (C := 3*C) (M := M) ht hB hM
    (u := fun s y ↦ -F.jet 2 s y)
    (ut := fun s y ↦ -((1/2:ℝ)*F.jet 4 s y+3*F.jet 1 s y*F.jet 2 s y+F.jet 0 s y*F.jet 3 s y))
    (ux := fun s y ↦ -F.jet 3 s y) (uxx := fun s y ↦ -F.jet 4 s y)
    (β := F.jet 0) (c := fun s y ↦ 3*F.jet 1 s y)
    (F.continuous 2).neg.continuousOn
    (by intro s hs y hy; exact (F.time2 s hs.1 y).neg)
    (by intro s hs y; exact (F.space 2 s y).neg)
    (by intro s hs y; exact (F.space 3 s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hinit y hy))
    (by intro s hs; simp only [F.zero2,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s y); linarith)
    (by intro s hs y hy; exact (le_abs_self _).trans (hb s y))
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hc s y); linarith)
    (by intro s hs y hy; ring_nf; exact le_rfl) t ⟨ht,le_rfl⟩ x hx
  linarith

lemma preserve_k (hinit : ∀ x,0≤x → F.k 0 x≤0) {t x : ℝ}
    (ht : 0≤t) (hx : 0≤x) : F.k t x≤0 := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨C,hC,hc⟩ := F.bound 1
  obtain ⟨M,hM,hm⟩ := F.k_bound
  have hh := halfline_parabolic_nonneg (T := t) (B := B) (C := C) (M := M) ht hB hM
    (u := fun s y ↦ -F.k s y) (ut := fun s y ↦ -F.kt s y)
    (ux := fun s y ↦ -F.kx s y) (uxx := fun s y ↦ -F.kxx s y)
    (β := F.jet 0) (c := F.jet 1)
    F.k_continuous.neg.continuousOn
    (by intro s hs y hy; exact (F.k_time hs.1 y).neg)
    (by intro s hs y; exact (F.k_space s y).neg)
    (by intro s hs y; exact (F.kx_space s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hinit y hy))
    (by intro s hs; simp only [k_zero,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s y); linarith)
    (by intro s hs y hy; exact (le_abs_self _).trans (hb s y))
    (by intro s hs y hy; exact (le_abs_self _).trans (hc s y))
    (by intro s hs y hy; dsimp only [kt]; ring_nf; exact le_rfl) t ⟨ht,le_rfl⟩ x hx
  linarith

lemma preserve_n (hw : ∀ x,0≤x → F.jet 2 0 x≤0)
    (hk : ∀ x,0≤x → F.k 0 x≤0) (hn : ∀ x,0≤x → 0≤F.n 0 x)
    {t x : ℝ} (ht : 0≤t) (hx : 0≤x) : 0≤F.n t x := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨M,hM,hm⟩ := F.n_bound
  apply halfline_parabolic_nonneg (T := t) (B := B) (C := 0) (M := M) ht hB hM
    (u := F.n) (ut := F.nt) (ux := F.nx) (uxx := F.nxx)
    (β := fun s y ↦ F.jet 0 s y-F.jet 1 s y/F.jet 0 s y)
    (c := fun s y ↦ F.k s y/F.jet 0 s y)
    F.n_continuous.continuousOn
    (by intro s hs y hy; exact F.n_time hs.1 hy)
    (by intro s hs y; exact F.n_space s y)
    (by intro s hs y; exact F.nx_space s y)
    hn
    (by intro s hs; simp only [n_zero,le_refl])
    (by intro s hs y hy; exact (neg_le_abs _).trans (hm s y) |> neg_le_neg |>.trans_eq (neg_neg _))
    (by
      intro s hs y hy
      have hd := div_nonneg (F.slope_nonneg s y) (F.positive s y hy).le
      have hh := (le_abs_self _).trans (hb s y)
      linarith)
    (by
      intro s hs y hy
      exact div_nonpos_of_nonpos_of_nonneg (F.preserve_k hk hs.1.le hy.le) (F.positive s y hy).le)
    (by
      intro s hs y hy
      have hf := mul_nonneg (F.positive s y hy).le
        (mul_nonneg_of_nonpos_of_nonpos (F.preserve_w hw hs.1.le hy.le) (F.preserve_k hk hs.1.le hy.le))
      dsimp only [nt]
      nlinarith only [hf]) t ⟨ht,le_rfl⟩ x hx

lemma preserve_shape (hw : ∀ x,0≤x → F.jet 2 0 x≤0)
    (hk : ∀ x,0≤x → F.k 0 x≤0) (hn : ∀ x,0≤x → 0≤F.n 0 x)
    {t x : ℝ} (ht : 0≤t) (hx : 0≤x) :
    F.jet 2 t x≤0 ∧ F.k t x≤0 ∧ 0≤F.n t x :=
  ⟨F.preserve_w hw ht hx,F.preserve_k hk ht hx,F.preserve_n hw hk hn ht hx⟩

end SKValue.BackwardBurgers

end

section

open Set Filter
open scoped Topology
namespace SKValue

lemma halfline_parabolic_nonneg_linear {T B C M : ℝ} (hT : 0≤T) (hB : 0≤B) (hM : 0≤M)
    {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Ici 0)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioi (0 : ℝ), HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (ux t) (uxx t x) x)
    (hinit : ∀ x, 0≤x → 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t 0)
    (hbound : ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → -M*(1+x)≤u t x)
    (hβ : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → β t x≤B)
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x →
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → 0≤u t x := by
  let k := max C 0+B+2
  have hk : 0≤k := by dsimp [k]; linarith [le_max_right C 0]
  have hεbound : ∀ ε : ℝ, 0<ε → ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x →
      -ε*Real.exp (k*t)*(1+x^2)≤u t x := by
    intro ε hε t ht x hx
    let A := max 1 (max x (2*M/ε+1))
    have hA1 : 1≤A := le_max_left _ _
    have hA0 : 0≤A := le_trans zero_le_one hA1
    have hxA : x≤A := (le_max_left _ _).trans (le_max_right _ _)
    have hMA : 2*M≤ε*A := by
      have hA := (le_max_right x (2*M/ε+1)).trans (le_max_right 1 (max x (2*M/ε+1)))
      have hh := mul_le_mul_of_nonneg_left hA hε.le
      rw [mul_add,mul_div_cancel₀ (2*M) hε.ne'] at hh
      linarith
    have hMA2 : M*(1+A)≤ε*(1+A^2) := by
      have hh := mul_le_mul_of_nonneg_right hMA hA0
      have ha := mul_nonneg hM (sub_nonneg.mpr hA1)
      nlinarith
    let q := fun s : ℝ ↦ ε*Real.exp (k*s)
    have hqpos : ∀ s, 0≤q s := fun s ↦ mul_nonneg hε.le (Real.exp_pos _).le
    have hqε : ∀ s∈Icc (0 : ℝ) T, ε≤q s := by
      intro s hs
      have hh : 1≤Real.exp (k*s) := Real.one_le_exp_iff.mpr (mul_nonneg hk hs.1)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
    have hqder : ∀ s, HasDerivAt q (k*q s) s := by
      intro s
      have hd : HasDerivAt q (ε*(Real.exp (k*s)*k)) s :=
        by simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul k).exp).const_mul ε
      convert! hd using 1
      dsimp [q]
      ring
    have hqcont : Continuous q := by fun_prop
    have hpder : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ 1+z^2) (2*y) y := by
      intro y
      convert! ((hasDerivAt_id y).pow 2).const_add 1 using 1
      simp
    have hcmp := parabolic_barrier (C := C) (ε := 0) hT hA0 le_rfl
      (u := fun s y ↦ u s y+q s*(1+y^2))
      (ut := fun s y ↦ ut s y+k*q s*(1+y^2))
      (ux := fun s y ↦ ux s y+q s*(2*y))
      (uxx := fun s y ↦ uxx s y+2*q s) (β := β) (c := c)
      ((hc.mono (fun p hp ↦ ⟨hp.1,hp.2.1⟩)).add
        (((hqcont.comp continuous_fst).mul (continuous_const.add
          (continuous_snd.pow 2))).continuousOn))
      (by
        intro s hs y hy
        exact (hdt s hs y hy.1).add ((hqder s).mul_const (1+y^2)))
      (by
        intro s hs y hy
        exact (hdx s hs y).add ((hpder y).const_mul (q s)))
      (by
        intro s hs y hy
        have he : deriv (fun z ↦ u s z+q s*(1+z^2))=
            fun z ↦ ux s z+q s*(2*z) := by
          funext z
          exact ((hdx s hs z).add ((hpder z).const_mul (q s))).deriv
        rw [he]
        convert! (hdxx s hs y).add (((hasDerivAt_id y).const_mul 2).const_mul (q s)) using 1
        simp
        ring)
      (by
        intro y hy
        exact add_nonneg (hinit y hy.1) (mul_nonneg (hqpos _) (by positivity)))
      (by
        intro s hs
        simpa only [neg_zero,zero_pow (by decide : 2≠0),add_zero,mul_one] using
          add_nonneg (hleft s hs) (hqpos s))
      (by
        intro s hs
        have hb := hbound s hs A hA0
        have hq := mul_le_mul_of_nonneg_right (hqε s hs) (show 0≤1+A^2 by positivity)
        change - (0 : ℝ)≤u s A+q s*(1+A^2)
        linarith)
      (by intro s hs y hy; exact hcbd s hs y hy.1)
      (by
        intro s hs y hy
        have hp := hpde s hs y hy.1
        have hb := hβ s hs y hy.1
        have hc' := hcbd s hs y hy.1
        have hkC : B+2≤k-c s y := by dsimp [k]; linarith [le_max_left C 0]
        have hh1 := mul_nonneg (sub_nonneg.mpr hkC) (show 0≤1+y^2 by positivity)
        have hh2 := mul_nonneg (sub_nonneg.mpr hb) hy.1.le
        have hh3 := mul_nonneg hB (sq_nonneg (y-1))
        have hbr : 0≤(k-c s y)*(1+y^2)-1-2*β s y*y := by nlinarith [sq_nonneg y]
        have hbq := mul_nonneg (hqpos s) hbr
        nlinarith only [hp,hbq]) t ht x ⟨hx,hxA⟩
    simp only [neg_zero,zero_mul] at hcmp
    dsimp [q] at hcmp
    linarith
  intro t ht x hx
  by_contra hn
  have hu : u t x<0 := lt_of_not_ge hn
  let D := Real.exp (k*t)*(1+x^2)
  have hD : 0<D := mul_pos (Real.exp_pos _) (by positivity)
  have he : 0<(-u t x)/(2*D) := div_pos (neg_pos.mpr hu) (mul_pos (by norm_num) hD)
  have hh := hεbound ((-u t x)/(2*D)) he t ht x hx
  have heq : -((-u t x)/(2*D))*Real.exp (k*t)*(1+x^2)=u t x/2 := by
    dsimp [D]
    field_simp
  rw [heq] at hh
  linarith

end SKValue

end

end OAI
