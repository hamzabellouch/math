import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # The weak C² chain rule with a nonzero derivative at zero

Subtract the affine part, apply the zero-derivative chain rule, and add
back the corresponding multiple of the actual weak Laplacian.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weakLaplacian_comp_C2_affine (u : SobolevSpace μ hQ) (d q : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d)
    {Φ φ ψ : ℝ → ℝ} {C D : ℝ≥0} (hΦ : LipschitzWith C Φ) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith D φ) (hψ : Continuous ψ)
    (hdΦ : ∀ a, HasDerivAt Φ (φ a) a) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |φ a|≤B) (hE : ∀ a, |ψ a|≤E)
    (hq : q =ᵐ[μ] fun x => φ (SobolevSpace.toLp μ hQ u x)*d x+
      ψ (SobolevSpace.toLp μ hQ u x)*localGamma μ hQ u u x) :
    IsWeakLaplacian μ hQ (SobolevSpace.comp μ hQ hΦ hΦ0 u) q := by
  let c := φ 0
  let α := fun a => Φ a-c*a
  let β := fun a => φ a-c
  have hα : LipschitzWith (C+‖c‖₊) α := by
    simpa only [mul_one,id_eq] using hΦ.sub (lipschitzWith_const_mul_real LipschitzWith.id c)
  have hβ : LipschitzWith D β := by
    simpa only [add_zero] using hφ.sub (LipschitzWith.const c)
  have hα0 : α 0=0 := by simp only [α,hΦ0,mul_zero,sub_self]
  have hβ0 : β 0=0 := sub_self _
  have hdα (a : ℝ) : HasDerivAt α (β a) a := by
    convert! (hdΦ a).sub ((hasDerivAt_id a).const_mul c) using 1; simp [β]
  have hdβ (a : ℝ) : HasDerivAt β (ψ a) a := (hdφ a).sub_const c
  have hβB (a : ℝ) : |β a|≤(B+‖c‖₊:ℝ≥0) := by
    calc
      _ ≤ |φ a|+|c| := abs_sub _ _
      _ ≤ B+|c| := add_le_add (hB a) le_rfl
      _ = _ := by simp only [NNReal.coe_add,coe_nnnorm,Real.norm_eq_abs]
  let q' := q-c • d
  have hq' : q' =ᵐ[μ] fun x => β (SobolevSpace.toLp μ hQ u x)*d x+
      ψ (SobolevSpace.toLp μ hQ u x)*localGamma μ hQ u u x := by
    filter_upwards [Lp.coeFn_sub q (c • d),Lp.coeFn_smul c d,hq] with x hx hy hz
    change (q-c • d) x = _
    simp only [hx,hy,hz,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,β]
    ring
  have h := weakLaplacian_comp_C2 μ hQ u d q' hd hα hα0 hβ hβ0 hψ hdα hdβ
    (B+‖c‖₊) E hβB hE hq'
  have he : SobolevSpace.comp μ hQ hα hα0 u+c • u = SobolevSpace.comp μ hQ hΦ hΦ0 u := by
    apply Subtype.ext
    apply Lp.ext
    change (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hα hα0 u)+
      c • SobolevSpace.toLp μ hQ u) =ᵐ[μ] SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hΦ hΦ0 u)
    filter_upwards [Lp.coeFn_add (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hα hα0 u))
      (c • SobolevSpace.toLp μ hQ u),Lp.coeFn_smul c (SobolevSpace.toLp μ hQ u),
      SobolevSpace.comp_coe μ hQ hα hα0 u,SobolevSpace.comp_coe μ hQ hΦ hΦ0 u] with x ha hs hαx hΦx
    simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hαx,hΦx,Function.comp_apply,α]
    ring
  have hh := h.add μ hQ (hd.smul μ hQ c)
  rw [he] at hh
  simpa only [q',sub_add_cancel] using hh

end RegularPointCoordinates

end

end OAI
