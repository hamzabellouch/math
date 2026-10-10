import OAI.Geometry.TranslativeCovering.LensDeployment

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace LensQuantitative
open Set MeasureTheory SphericalLaw CapGeometry CapCost LensDeployment
open scoped ENNReal NNReal

lemma cap_eq_mass {n : ℕ} (e f : Sphere n) (t : ℝ) :
    (σ n).real (cap e.val t) = (σ n).real (cap f.val t) := by
  apply congrArg ENNReal.toReal
  exact cap_equal_norm (by rw [mem_sphere_zero_iff_norm.mp e.property,
    mem_sphere_zero_iff_norm.mp f.property]) t

lemma halfcap_eq_mass {n : ℕ} (e f : Sphere n) (t : ℝ) :
    (σ n).real (halfcap e.val t) = (σ n).real (halfcap f.val t) := by
  apply congrArg ENNReal.toReal
  exact halfcap_equal_norm (by rw [mem_sphere_zero_iff_norm.mp e.property,
    mem_sphere_zero_iff_norm.mp f.property]) t

lemma intensity_lens {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [Nonempty I]
    (e e₀ : Sphere n) (axes : I → Sphere n) (τ : I → ℝ)
    {l u t t₀ Φ : ℝ}
    (hl : 0 < l) (hu : u < 1) (_ht : 0 ≤ t) (ht1 : t < 1)
    (ht₀ : l ≤ t₀) (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,ProjectiveCaps.angle e₀.val (axes i).val ≤ Φ)
    (hτ : ∀ i,τ i ≤ t₀)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hsmall : let h := Real.sqrt (4*Real.log (2*(Fintype.card I:ℝ))/((n:ℝ)*l))
      Real.sqrt ((t₀+Φ^2/2+Φ*h)^2+h^2) ≤ u) :
    let h := Real.sqrt (4*Real.log (2*(Fintype.card I:ℝ))/((n:ℝ)*l))
    let δ := Φ^2/2+Φ*h
    (intensity e t).real (cap e₀.val t₀)/4 *
      Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤
        (intensity e t).real (⋂ i,cap (axes i).val (τ i)) := by
  let m : ℝ := Fintype.card I
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := I))
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hlog : 0 ≤ Real.log (2*m) := Real.log_nonneg (by linarith)
  let h := Real.sqrt (4*Real.log (2*m)/((n:ℝ)*l))
  let δ := Φ^2/2+Φ*h
  have hsmall' : Real.sqrt ((t₀+δ)^2+h^2) ≤ u := by
    simpa only [δ,h,m,add_assoc] using hsmall
  have hh : 0 ≤ h := Real.sqrt_nonneg _
  have hh2 : h^2 = 4*Real.log (2*m)/((n:ℝ)*l) := Real.sq_sqrt (by positivity)
  have hexp : m*Real.exp (-(n:ℝ)*l*h^2/4) = 1/2 := by
    rw [hh2]
    have he : -(n:ℝ)*l*(4*Real.log (2*m)/((n:ℝ)*l))/4 = -Real.log (2*m) := by
      field_simp
    rw [he,Real.exp_neg,Real.exp_log (by linarith : 0 < 2*m)]
    field_simp
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsu : t₀+δ ≤ u := by
    have hsq : t₀+δ ≤ Real.sqrt ((t₀+δ)^2+h^2) :=
      le_trans (le_abs_self _) (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith))
    exact hsq.trans hsmall'
  have hmLens := projective_lens e₀ axes τ hΦ hΦsmall hangle hl hu
    (ht₀.trans (le_add_of_nonneg_right hδ)) hh hsmall' hdim
    (fun i => by dsimp [δ]; linarith [hτ i])
  change (1-m*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e₀.val (t₀+δ)) ≤ _ at hmLens
  rw [hexp] at hmLens
  have ht₀pos := halfcap_real_pos e₀ ((le_add_of_nonneg_right hδ).trans_lt (hsu.trans_lt hu))
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hu0 := hl.trans_le (ht₀.trans (le_add_of_nonneg_right hδ) |>.trans hsu)
    have h1 : 0 < 1-u^2 := by nlinarith
    positivity
  have hratio := (halfcap_ratio e₀ hl hu ht₀ (le_add_of_nonneg_right hδ) hsu).1
  have hexple : Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤
      Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(t₀+δ-t₀)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hA hδ]
  have hratio' := (le_div_iff₀ ht₀pos).mp (hexple.trans hratio)
  have hmass := CapAffinity.cap_mass e₀ (hl.trans_le ht₀).le
  simp_rw [intensity_real]
  rw [hmass]
  change (2*(σ n).real (halfcap e₀.val t₀)/(σ n).real (cap e.val t)/4)*
    Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤ _
  calc
    _ = ((σ n).real (halfcap e₀.val t₀)*
      Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ)/2)/(σ n).real (cap e.val t) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [hratio']) (cap_real_pos e ht1).le

end LensQuantitative

end OAI
