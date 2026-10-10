import Mathlib
import OAI.Probability.SKSupport.Parabolic.BurgersConstruction

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

structure SmoothForward (s : ℝ → ℝ → ℝ) : Prop where
  family : AffineSmoothFamily s
  deriv_family : BoundedSmoothFamily (fun t => deriv (s t))
  time_derivative : ∀ n t, 0 < t → ∀ x,
    HasDerivAt (fun u => iteratedDeriv n (s u) x) (iteratedDeriv n (scoreRate s t) x) t

lemma scoreRate_affine {s : ℝ → ℝ → ℝ} (hs : AffineSmoothFamily s)
    (hds : BoundedSmoothFamily (fun t => deriv (s t))) : AffineSmoothFamily (scoreRate s) := by
  have hc := hs.deriv.continuous
  have h₂c := hs.deriv.deriv.continuous
  convert ((hds.deriv.affine h₂c).const_mul (1/2:ℝ)).add
    ((hs.mul_bounded hds hc).const_mul (-1)) using 1
  funext t x
  simp only [scoreRate,iteratedDeriv_succ,iteratedDeriv_zero,neg_one_mul,sub_eq_add_neg]

theorem forwardScore_smooth {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) : SmoothForward (forwardScore a f) := by
  have hs := forwardScore_affine ha hf hLip
  have hds := forwardScore_deriv_family ha hf hLip
  refine ⟨hs,hds,fun n t ht x => ?_⟩
  exact hasDerivAt_affine_evolution_jet hs.continuous (scoreRate_affine hs hds) hs.smooth
    (fun t htt x => hasDerivAt_forwardScore ha hf hLip htt x) ht n x

namespace SmoothForward
variable {s : ℝ → ℝ → ℝ} (hs : SmoothForward s)
include hs

lemma jet_spatial (n : ℕ) (t x : ℝ) :
    HasDerivAt (iteratedDeriv n (s t)) (iteratedDeriv (n+1) (s t) x) x :=
  hasDerivAt_spatialJet (hs.family.smooth t) n x

lemma jet_continuous (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (s p.1) p.2) :=
  (hs.family.iteratedDeriv n).continuous

lemma jet_family (n : ℕ) : BoundedSmoothFamily (fun t => iteratedDeriv (n+1) (s t)) := by
  simpa only [iteratedDeriv_succ'] using hs.deriv_family.iteratedDeriv n

lemma rate_deriv (t x : ℝ) : deriv (scoreRate s t) x =
    (1/2:ℝ)*iteratedDeriv 3 (s t) x-(deriv (s t) x)^2-s t x*iteratedDeriv 2 (s t) x := by
  have hd := ((hs.jet_spatial 2 t x).const_mul (1/2:ℝ)).sub
    ((hs.jet_spatial 0 t x).mul (hs.jet_spatial 1 t x))
  have hd' : HasDerivAt (scoreRate s t) ((1/2:ℝ)*iteratedDeriv 3 (s t) x-
      (deriv (s t) x)^2-s t x*iteratedDeriv 2 (s t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only [scoreRate,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma rate_jet2 (t x : ℝ) : iteratedDeriv 2 (scoreRate s t) x =
    (1/2:ℝ)*iteratedDeriv 4 (s t) x-3*deriv (s t) x*iteratedDeriv 2 (s t) x-
      s t x*iteratedDeriv 3 (s t) x := by
  have he : deriv (scoreRate s t) = fun y => (1/2:ℝ)*iteratedDeriv 3 (s t) y-
      (deriv (s t) y)^2-s t y*iteratedDeriv 2 (s t) y := funext (hs.rate_deriv t)
  have hd := (((hs.jet_spatial 3 t x).const_mul (1/2:ℝ)).sub
    ((hs.jet_spatial 1 t x).pow 2)).sub ((hs.jet_spatial 0 t x).mul (hs.jet_spatial 2 t x))
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  apply HasDerivAt.deriv
  convert hd using 1 <;> first | rfl | ((try funext y); simp only [iteratedDeriv_succ,iteratedDeriv_zero,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply] <;> ring)

lemma second_odd (ho : ∀ t, Function.Odd (s t)) (t : ℝ) :
    Function.Odd (iteratedDeriv 2 (s t)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
   (even_deriv_odd ((hs.deriv_family.regular t).smooth.differentiable (by simp))
    (odd_deriv_even ((hs.family.smooth t).differentiable (by simp)) (ho t)))

end SmoothForward

lemma forwardScore_odd {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f) (t : ℝ) :
    Function.Odd (forwardScore a f t) := by
  have hd := even_deriv_odd ((forwardCorrection_smooth (a := a) hf hLip t).differentiable (by simp))
    (forwardCorrection_even hf hLip he t)
  intro x
  simp only [forwardScore,neg_div,hd x]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open Set Filter
open scoped Topology

namespace ZeroTemperatureSK.Parabolic

theorem second_derivative_nonnegative_at_min {f : ℝ → ℝ} {x d₂ : ℝ}
    (hf : Continuous f) (hm : IsLocalMin f x)
    (hd₂ : HasDerivAt (deriv f) d₂ x) : 0 ≤ d₂ := by
  by_contra hn
  have hneg : d₂ < 0 := lt_of_not_ge hn
  have hzero : deriv f x = 0 := hm.deriv_eq_zero
  have hr := (hasDerivAt_iff_tendsto_slope_left_right.mp hd₂).2
  have he : ∀ᶠ y in 𝓝[>] x, deriv f y < 0 := by
    filter_upwards [hr.eventually (Iio_mem_nhds hneg), self_mem_nhdsWithin] with y hy hxy
    have hpos : 0 < y-x := sub_pos.mpr hxy
    simpa only [slope_def_field, hzero, sub_zero, div_lt_iff₀ hpos, zero_mul] using hy
  have he' : ∀ᶠ y in 𝓝[>] x, deriv f y < 0 ∧ f x ≤ f y :=
    he.and (hm.filter_mono nhdsWithin_le_nhds)
  obtain ⟨b, hxb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he'
  obtain ⟨y, hxy, hyb⟩ := exists_between (show x < b from hxb)
  have hanti : StrictAntiOn f (Icc x y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x y) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    exact (hb ⟨ht.1, ht.2.trans hyb⟩).1
  have hlt := hanti (left_mem_Icc.mpr hxy.le) (right_mem_Icc.mpr hxy.le) hxy
  exact (not_lt_of_ge (hb ⟨hxy, hyb⟩).2) hlt

theorem time_derivative_nonpositive {f : ℝ → ℝ} {a b x d : ℝ}
    (hax : a < x) (hxb : x ≤ b)
    (hd : HasDerivWithinAt f d (Icc a b) x)
    (hm : IsMinOn f (Icc a b) x) : d ≤ 0 := by
  have hd' : HasDerivWithinAt f d (Icc a x) x :=
    hd.mono (Icc_subset_Icc_right hxb)
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd'
  have hset : Icc a x \ {x} = Ico a x := by
    ext y
    simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ico]
    constructor
    · rintro ⟨⟨hay, hyx⟩, hne⟩
      exact ⟨hay, lt_of_le_of_ne hyx hne⟩
    · rintro ⟨hay, hyx⟩
      exact ⟨⟨hay, hyx.le⟩, hyx.ne⟩
  rw [hset, nhdsWithin_Ico_eq_nhdsLT hax] at hs
  apply le_of_tendsto hs
  have hmem : ∀ᶠ y in 𝓝[<] x, y ∈ Ico a x := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hax]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with y hy
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr (hm ⟨hy.1, hy.2.le.trans hxb⟩)) (sub_nonpos.mpr hy.2.le)

theorem nonnegative_of_parabolic_inequality
    {u ut ux uxx κ β ℓ : ℝ → ℝ → ℝ} {t₀ t₁ a b : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ Icc a b))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hk : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 ≤ κ t x)
    (hl : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 < ℓ t x)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      0 ≤ ut t x - κ t x * uxx t x - β t x * ux t x + ℓ t x * u t x)
    (hinit : ∀ x ∈ Icc a b, 0 ≤ u t₀ x)
    (hleft : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t a)
    (hright : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t b) :
    ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc a b, 0 ≤ u t x := by
  intro t htmem x hxmem
  by_contra hn
  have hnegative : u t x < 0 := lt_of_not_ge hn
  obtain ⟨p, hp, hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(t,x), htmem, hxmem⟩ hc
  have hpneg : u p.1 p.2 < 0 := lt_of_le_of_lt (hm (show (t, x) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨htmem, hxmem⟩)) hnegative
  have hpt : p.1 ∈ Ioc t₀ t₁ := by
    refine ⟨lt_of_le_of_ne hp.1.1 ?_, hp.1.2⟩
    intro heq
    have hz := hinit p.2 hp.2
    rw [heq] at hz
    exact (not_lt_of_ge hz) hpneg
  have hpx : p.2 ∈ Ioo a b := by
    constructor
    · refine lt_of_le_of_ne hp.2.1 ?_
      intro heq
      have hz := hleft p.1 hp.1
      rw [heq] at hz
      exact (not_lt_of_ge hz) hpneg
    · refine lt_of_le_of_ne hp.2.2 ?_
      intro heq
      have hz := hright p.1 hp.1
      rw [← heq] at hz
      exact (not_lt_of_ge hz) hpneg
  have hmintime : IsMinOn (fun s => u s p.2) (Icc t₀ t₁) p.1 := by
    intro s hs
    exact hm (show (s, p.2) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨hs, hp.2⟩)
  have hut : ut p.1 p.2 ≤ 0 :=
    time_derivative_nonpositive hpt.1 hpt.2 (ht p.1 hpt p.2 hpx) hmintime
  have hminspace : IsMinOn (u p.1) (Icc a b) p.2 := by
    intro y hy
    exact hm (show (p.1, y) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨hp.1, hy⟩)
  have hlocal := hminspace.isLocalMin (Icc_mem_nhds hpx.1 hpx.2)
  have hux : ux p.1 p.2 = 0 := hlocal.hasDerivAt_eq_zero (hx p.1 hpt p.2 hpx)
  have huxx : 0 ≤ uxx p.1 p.2 :=
    second_derivative_nonnegative_at_min (hs p.1 hp.1) hlocal (hxx p.1 hpt p.2 hpx)
  have h1 := mul_nonneg (hk p.1 hpt p.2 hpx) huxx
  have h2 := mul_neg_of_pos_of_neg (hl p.1 hpt p.2 hpx) hpneg
  have h3 := hpde p.1 hpt p.2 hpx
  rw [hux, mul_zero, sub_zero] at h3
  linarith

theorem exponential_lower_barrier
    {u ut ux uxx κ β c : ℝ → ℝ → ℝ} {t₀ t₁ a b C ε : ℝ}
    (hε : 0 ≤ ε)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ Icc a b))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hk : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 ≤ κ t x)
    (hbound : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, c t x ≤ C)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      0 ≤ ut t x - κ t x * uxx t x - β t x * ux t x - c t x * u t x)
    (hinit : ∀ x ∈ Icc a b, 0 ≤ u t₀ x)
    (hleft : ∀ t ∈ Icc t₀ t₁, -ε ≤ u t a)
    (hright : ∀ t ∈ Icc t₀ t₁, -ε ≤ u t b) :
    ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc a b,
      -ε * Real.exp ((max C 0 + 1) * (t - t₀)) ≤ u t x := by
  let k := max C 0 + 1
  let E := fun t : ℝ => Real.exp (-k * (t-t₀))
  let V := fun t x => E t * u t x + ε
  have hEpos : ∀ t, 0 < E t := fun _ => Real.exp_pos _
  have hkpos : 0 < k := by dsimp [k]; linarith [le_max_right C 0]
  have hEderiv : ∀ t, HasDerivAt E (-k * E t) t := by
    intro t
    convert! ((((hasDerivAt_id t).sub_const t₀).const_mul (-k)).exp) using 1
    dsimp [E, id]
    ring
  have hEle : ∀ t ∈ Icc t₀ t₁, E t ≤ 1 := by
    intro t ht
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) (sub_nonneg.mpr ht.1)
  have hVcont : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc t₀ t₁ ×ˢ Icc a b) := by
    exact (((show Continuous (fun p : ℝ × ℝ => E p.1) by dsimp [E]; fun_prop).continuousOn).mul hc).add_const ε
  have hVs : ∀ t ∈ Icc t₀ t₁, Continuous (V t) := by
    intro t ht
    exact ((hs t ht).const_mul (E t)).add_const ε
  have hVt : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => V s x) (E t * (ut t x - k * u t x)) (Icc t₀ t₁) t := by
    intro t htmem x hxmem
    convert! (((hEderiv t).hasDerivWithinAt.mul (ht t htmem x hxmem)).add_const ε) using 1
    ring
  have hVx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivAt (V t) (E t * ux t x) x := by
    intro t htmem x hxmem
    exact ((hx t htmem x hxmem).const_mul (E t)).add_const ε
  have hVxx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivAt (deriv (V t)) (E t * uxx t x) x := by
    intro t htmem x hxmem
    have heq : deriv (V t) = fun x => E t * deriv (u t) x := by
      funext x
      simp only [V, deriv_add_const, deriv_const_mul_field]
    rw [heq]
    exact (hxx t htmem x hxmem).const_mul (E t)
  have hl : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 < k - c t x := by
    intro t htmem x hxmem
    have := hbound t htmem x hxmem
    dsimp [k]
    linarith [le_max_left C 0]
  have hVpde : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      0 ≤ E t * (ut t x - k * u t x) - κ t x * (E t * uxx t x) -
        β t x * (E t * ux t x) + (k-c t x) * V t x := by
    intro t htmem x hxmem
    have h1 := mul_nonneg (hEpos t).le (hpde t htmem x hxmem)
    have h2 := mul_nonneg (hl t htmem x hxmem).le hε
    dsimp [V]
    nlinarith
  have hVinit : ∀ x ∈ Icc a b, 0 ≤ V t₀ x := by
    intro x hxmem
    exact add_nonneg (mul_nonneg (hEpos t₀).le (hinit x hxmem)) hε
  have boundary : ∀ t ∈ Icc t₀ t₁, ∀ z, -ε ≤ u t z → 0 ≤ V t z := by
    intro t htmem z hz
    have h1 := mul_le_mul_of_nonneg_left hz (hEpos t).le
    have h2 := mul_le_mul_of_nonneg_right (hEle t htmem) hε
    dsimp [V]
    nlinarith
  have hnonneg := nonnegative_of_parabolic_inequality hVcont hVs hVt hVx hVxx hk hl hVpde
    hVinit (fun t ht => boundary t ht a (hleft t ht)) (fun t ht => boundary t ht b (hright t ht))
  intro t htmem x hxmem
  have hv := hnonneg t htmem x hxmem
  have hinv : E t * Real.exp (k * (t-t₀)) = 1 := by
    dsimp [E]
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  apply (mul_le_mul_iff_right₀ (hEpos t)).mp
  change E t * (-ε * Real.exp (k * (t-t₀))) ≤ E t * u t x
  calc
    E t * (-ε * Real.exp (k * (t-t₀))) = -ε := by nlinarith [hinv]
    _ ≤ E t * u t x := by dsimp [V] at hv; linarith

end ZeroTemperatureSK.Parabolic

end

end OAI
