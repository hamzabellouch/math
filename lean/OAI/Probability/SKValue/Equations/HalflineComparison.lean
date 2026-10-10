import Mathlib
import OAI.Probability.SKValue.Equations.ParabolicComparison

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

lemma halfline_parabolic_nonneg {T B C M : ℝ} (hT : 0≤T) (hB : 0≤B) (_ : 0≤M)
    {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Ici 0)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioi (0 : ℝ), HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (ux t) (uxx t x) x)
    (hinit : ∀ x, 0≤x → 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t 0)
    (hbound : ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → -M≤u t x)
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
    let A := max 1 (max x (M/ε+1))
    have hA1 : 1≤A := le_max_left _ _
    have hA0 : 0≤A := le_trans zero_le_one hA1
    have hxA : x≤A := (le_max_left _ _).trans (le_max_right _ _)
    have hMA : M≤ε*A := by
      have hA := (le_max_right x (M/ε+1)).trans (le_max_right 1 (max x (M/ε+1)))
      have hh := mul_le_mul_of_nonneg_left hA hε.le
      rw [mul_add,mul_div_cancel₀ M hε.ne'] at hh
      linarith
    have hMA2 : M≤ε*(1+A^2) := by
      have hAA : A≤A^2 := by nlinarith
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hAA)]
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
      convert! hd using 1; dsimp [q]; ring
    have hqcont : Continuous q := by fun_prop
    have hpder : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ 1+z^2) (2*y) y := by
      intro y
      convert! ((hasDerivAt_id y).pow 2).const_add 1 using 1; simp
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
        convert! (hdxx s hs y).add (((hasDerivAt_id y).const_mul 2).const_mul (q s)) using 1; simp; ring)
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
