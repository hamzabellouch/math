import Mathlib
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

lemma derivative_tower_bounded {ι : Type*} (R : ℕ → ι → ℝ → ℝ)
    (hs : ∀ j a, ContDiff ℝ ∞ (R j a))
    (hd : ∀ j a, deriv (R j a) = fun x ↦ R (j+1) a x-R j a x*R 1 a x)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |R j a x|≤C) :
    ∀ n j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ a x, |iteratedDeriv n (R j a) x|≤C := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j; simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j : ℕ, ∃ C : ℝ, 0≤C ∧
          (k≤n → ∀ a x, |iteratedDeriv k (R j a) x|≤C) := by
        intro k j
        by_cases hk : k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1), (n.choose k : ℝ)*C k j*C (n-k) 1,?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hC _ _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hs 1 a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hs 1 a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbound (n-k) 1 (Nat.sub_le ..) a x) (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

noncomputable def normalizedJet {ι : Type*} (F : ι → ℝ → ℝ) (j : ℕ) (a : ι) (x : ℝ) : ℝ :=
  iteratedDeriv j (F a) x/F a x

lemma normalizedJet_smooth {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0) (j : ℕ) (a : ι) :
    ContDiff ℝ ∞ (normalizedJet F j a) :=
  (smooth_iteratedDeriv (hs a) j).div (hs a) (hp a)

lemma normalizedJet_deriv {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0) (j : ℕ) (a : ι) :
    deriv (normalizedJet F j a) =
      fun x ↦ normalizedJet F (j+1) a x-normalizedJet F j a x*normalizedJet F 1 a x := by
  funext x
  have hd := (((hs a).differentiable_iteratedDeriv j
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) x).hasDerivAt
  have hF := (((hs a).differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
  change deriv (fun y ↦ iteratedDeriv j (F a) y/F a y) x = _
  convert! (hd.div hF (hp a x)).deriv using 1
  dsimp only [normalizedJet]
  rw [iteratedDeriv_succ,iteratedDeriv_one]
  field_simp [hp a x]

lemma normalizedJet_uniform_bounded {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |normalizedJet F j a x|≤C) :
    ∀ n j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ a x, |iteratedDeriv n (normalizedJet F j a) x|≤C :=
  derivative_tower_bounded (normalizedJet F) (normalizedJet_smooth hs hp)
    (normalizedJet_deriv hs hp) hb

lemma normalizedJet_boundedSmooth {ι : Type*} {F : ι → ℝ → ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (F a)) (hp : ∀ a x, F a x≠0)
    (hb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a x, |normalizedJet F j a x|≤C) (j : ℕ) (a : ι) :
    BoundedSmooth (normalizedJet F j a) := by
  refine ⟨normalizedJet_smooth hs hp j a,?_⟩
  intro n
  obtain ⟨C,hC,hbC⟩ := normalizedJet_uniform_bounded hs hp hb n j
  exact ⟨C,hC,hbC a⟩

lemma heat_relative_bound {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ExpGrowth f) (hgg : ExpGrowth g) {C : ℝ}
    (hb : ∀ x, |g x|≤C*f x) (h x : ℝ) :
    |heat h g x|≤C*heat h f x := by
  apply abs_integral_le_integral_abs.trans
  rw [heat,←integral_const_mul]
  apply integral_mono (hgg.shift_integrable hg x (Real.sqrt h)).abs
    ((hfg.shift_integrable hf x (Real.sqrt h)).const_mul C)
  exact fun z ↦ hb _

lemma exp_heat_normalizedJet_bound {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0≤c) :
    ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ h x,
      |normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) j h x|≤C := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have heg := exp_iteratedDeriv_growth hψl hψs hψ hc
  intro j
  obtain ⟨C,hC,hJ⟩ := (expJet_boundedSmooth hψ c j).bound_zero
  refine ⟨C,hC,?_⟩
  intro h x
  dsimp only [normalizedJet]
  rw [heat_iteratedDeriv hes heg,abs_div]
  have hp : 0 < heat h (fun y ↦ Real.exp (c*ψ y)) x :=
    lipschitz_exp_integral_pos hψl hc x (Real.sqrt h)
  rw [abs_of_pos hp]
  apply (div_le_iff₀ (lipschitz_exp_integral_pos hψl hc x (Real.sqrt h))).mpr
  exact heat_relative_bound hes.continuous.measurable
    (smooth_iteratedDeriv hes j).continuous.measurable
    (ExpGrowth.exp_lipschitz hψl hc) (heg j)
    (fun y ↦ by
      rw [exp_iteratedDeriv hψs hψ c j,abs_mul,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hJ y) (Real.exp_pos (c*ψ y)).le) h x

lemma coleHopf_deriv_eq_normalizedJet {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0<c) (h : ℝ) :
    deriv (coleHopf c h ψ) = fun x ↦
      c⁻¹*normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) 1 h x := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  have hHs := heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) h
  have heq : coleHopf c h ψ = fun x ↦ Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c := by
    funext x
    simp only [coleHopf,ite_eq_right hc.ne']
  rw [heq]
  funext x
  have hHd := ((hHs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0))) x).hasDerivAt
  have hd := (hHd.log (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt h)).ne').div_const c
  convert! hd.deriv using 1
  simp only [normalizedJet,iteratedDeriv_one,div_eq_mul_inv]
  ring

lemma coleHopf_deriv_boundedSmooth_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0<c) (h : ℝ) :
    BoundedSmooth (deriv (coleHopf c h ψ)) := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  rw [coleHopf_deriv_eq_normalizedJet hψl hψs hψ hc h]
  exact (normalizedJet_boundedSmooth
    (fun t ↦ heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) t)
    (fun t x ↦ (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt t)).ne')
    (exp_heat_normalizedJet_bound hψl hψs hψ hc.le) 1 h).const_mul _

lemma coleHopf_deriv_uniform_bounds_of_pos {ψ : ℝ → ℝ} (hψl : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ ∞ ψ) (hψ : BoundedSmooth (deriv ψ)) {c : ℝ} (hc : 0<c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψs).exp
  intro n
  obtain ⟨C,hC,hb⟩ := normalizedJet_uniform_bounded
    (fun t ↦ heat_contDiff hes (exp_iteratedDeriv_growth hψl hψs hψ hc.le) t)
    (fun t x ↦ (lipschitz_exp_integral_pos hψl hc.le x (Real.sqrt t)).ne')
    (exp_heat_normalizedJet_bound hψl hψs hψ hc.le) n 1
  refine ⟨|c⁻¹| * C,by positivity,?_⟩
  intro h x
  rw [coleHopf_deriv_eq_normalizedJet hψl hψs hψ hc h,iteratedDeriv_const_mul_field,abs_mul]
  exact mul_le_mul_of_nonneg_left (hb h x) (abs_nonneg _)

end SKValue

end

end OAI
