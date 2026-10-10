import Mathlib
import OAI.Probability.SKValue.Equations.HalflineComparison
import OAI.Probability.SKValue.Equations.LineComparison

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

structure ForwardBurgers (T : ℝ) where
  jet : ℕ → ℝ → ℝ → ℝ
  continuous : ∀ n, Continuous (fun p : ℝ×ℝ ↦ jet n p.1 p.2)
  space : ∀ n t x, HasDerivAt (jet n t) (jet (n+1) t x) x
  time0 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 0 · x)
    ((1/2:ℝ)*jet 2 t x-jet 0 t x*jet 1 t x) t
  time1 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 1 · x)
    ((1/2:ℝ)*jet 3 t x-(jet 1 t x)^2-jet 0 t x*jet 2 t x) t
  time2 : ∀ t∈Ioc (0:ℝ) T, ∀ x, HasDerivAt (jet 2 · x)
    ((1/2:ℝ)*jet 4 t x-3*jet 1 t x*jet 2 t x-jet 0 t x*jet 3 t x) t
  bound : ∀ n, ∃ C:ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x, |jet (n+1) t x|≤C
  growth : ∃ C:ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x, |jet 0 t x|≤C*(1+|x|)
  zero0 : ∀ t, jet 0 t 0=0
  zero2 : ∀ t, jet 2 t 0=0

namespace ForwardBurgers
variable {T : ℝ} (F : ForwardBurgers T)

lemma preserve_slope {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x) {t : ℝ} (ht : t∈Icc (0:ℝ) T) (x : ℝ) :
    1/(a+t)≤F.jet 1 t x := by
  obtain ⟨C,hC,hc⟩ := F.bound 0
  obtain ⟨L,hL,hl⟩ := F.growth
  have hap (s : ℝ) (hs : 0≤ s) : 0<a+s := by linarith
  have hi (s : ℝ) (hs : 0≤ s) : 0≤1/(a+s) ∧ 1/(a+s)≤1/a :=
    ⟨one_div_nonneg.mpr (hap s hs).le,one_div_le_one_div_of_le ha (by linarith)⟩
  have hd (s : ℝ) (hs : 0≤ s) : HasDerivAt (fun z : ℝ ↦ 1/(a+z)) (-(1/(a+s))^2) s := by
    have hh := ((hasDerivAt_id s).const_add a).inv (hap s hs).ne'
    convert! hh using 1
    · funext z; simp only [one_div, Pi.inv_apply, id_eq]
    · simp only [one_div, inv_pow, id_eq]; ring
  have hcont : ContinuousOn (fun p : ℝ×ℝ ↦ 1/(a+p.1)) ((Icc (0:ℝ) T)×ˢuniv) :=
    continuousOn_const.div (continuous_const.add continuous_fst).continuousOn
      (fun p hp ↦ (hap p.1 hp.1.1).ne')
  have hh := line_parabolic_nonneg (T := T) (B := 2*L) (C := C) (M := C+1/a)
    hT (by positivity) (add_nonneg hC (one_div_nonneg.mpr ha.le))
    (u := fun s y ↦ F.jet 1 s y-1/(a+s))
    (ut := fun s y ↦ (1/2:ℝ)*F.jet 3 s y-(F.jet 1 s y)^2-F.jet 0 s y*F.jet 2 s y+(1/(a+s))^2)
    (ux := F.jet 2) (uxx := F.jet 3)
    (β := fun s y ↦ -F.jet 0 s y) (c := fun s y ↦ -(F.jet 1 s y+1/(a+s)))
    ((F.continuous 1).continuousOn.sub hcont)
    (by intro s hs y; convert! (F.time1 s hs y).sub (hd s hs.1.le) using 1; ring)
    (by intro s hs y; simpa using (F.space 1 s y).sub_const (1/(a+s)))
    (by intro s hs y; exact F.space 2 s y)
    (by intro y; simpa only [add_zero] using sub_nonneg.mpr (hinit y))
    (by
      intro s hs y
      have h1 := (abs_le.mp (hc s hs y)).1
      have h2 := (hi s hs.1).2
      linarith)
    (by
      intro s hs y
      have h1 : -(F.jet 0 s y*y)≤L*(1+|y|)*|y| := calc
        _ ≤ |F.jet 0 s y*y| := neg_le_abs _
        _ = |F.jet 0 s y| *|y| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hl s ⟨hs.1.le,hs.2⟩ y) (abs_nonneg y)
      have h2 := mul_nonneg hL (sq_nonneg (|y|-1))
      have he : (-F.jet 0 s y)*y= -(F.jet 0 s y*y) := by ring
      rw [he]
      nlinarith [sq_nonneg y,sq_abs y])
    (by
      intro s hs y
      have h1 := (abs_le.mp (hc s ⟨hs.1.le,hs.2⟩ y)).1
      have h2 := (hi s hs.1.le).1
      linarith)
    (by intro s hs y; ring_nf; exact le_rfl) t ht x
  linarith

lemma score_nonneg {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x) {t : ℝ} (ht : t∈Icc (0:ℝ) T)
    {x : ℝ} (hx : 0≤x) : 0≤F.jet 0 t x := by
  have hm : Monotone (F.jet 0 t) := monotone_of_deriv_nonneg (fun y ↦ (F.space 0 t y).differentiableAt)
    (fun y ↦ by
      rw [(F.space 0 t y).deriv]
      exact (one_div_nonneg.mpr (by linarith [ht.1] : 0≤a+t)).trans (F.preserve_slope ha hT hinit ht y))
  simpa only [F.zero0] using hm hx

lemma preserve_concavity {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x)
    (hbinit : ∀ x,0≤x → F.jet 2 0 x≤0) {t : ℝ} (ht : t∈Icc (0:ℝ) T)
    {x : ℝ} (hx : 0≤x) : F.jet 2 t x≤0 := by
  obtain ⟨M,hM,hm⟩ := F.bound 1
  have hh := halfline_parabolic_nonneg (T := T) (B := 0) (C := 0) (M := M) hT le_rfl hM
    (u := fun s y ↦ -F.jet 2 s y)
    (ut := fun s y ↦ -((1/2:ℝ)*F.jet 4 s y-3*F.jet 1 s y*F.jet 2 s y-F.jet 0 s y*F.jet 3 s y))
    (ux := fun s y ↦ -F.jet 3 s y) (uxx := fun s y ↦ -F.jet 4 s y)
    (β := fun s y ↦ -F.jet 0 s y) (c := fun s y ↦ -3*F.jet 1 s y)
    (F.continuous 2).neg.continuousOn
    (by intro s hs y hy; exact (F.time2 s hs y).neg)
    (by intro s hs y; exact (F.space 2 s y).neg)
    (by intro s hs y; exact (F.space 3 s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hbinit y hy))
    (by intro s hs; simp only [F.zero2,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s hs y); linarith)
    (by intro s hs y hy; exact neg_nonpos.mpr (F.score_nonneg ha hT hinit ⟨hs.1.le,hs.2⟩ hy.le))
    (by
      intro s hs y hy
      have hp := F.preserve_slope ha hT hinit ⟨hs.1.le,hs.2⟩ y
      have hpos := one_div_nonneg.mpr (show 0≤a+s by linarith [hs.1])
      nlinarith)
    (by intro s hs y hy; ring_nf; exact le_rfl) t ht x hx
  linarith

end ForwardBurgers
end SKValue

end

end OAI
