import OAI.Geometry.Perimeter.Regularity.EllipticContraction
import OAI.Geometry.Perimeter.Regularity.VectorQuotient

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem WeakFluxEquation.mono {V : Euc n → Euc n} {U W : Set (Euc n)}
    (h : WeakFluxEquation V U) (hWU : W⊆U) : WeakFluxEquation V W := by
  intro φ
  exact h ⟨φ.val,φ.property.1,φ.property.2.1,φ.property.2.2.trans hWU⟩

 theorem weakLinear_iff_flux {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U : Set (Euc n)}
    (hA : Continuous A) (hf : ContDiff ℝ 1 f) (hF : Continuous F) :
    WeakLinearEquation A f F U ↔ WeakFluxEquation (fun x ↦ A x (gradient f x)-F x) U := by
  have hc := hA.clm_apply (gradient_continuous_C1 hf)
  constructor <;> intro h φ
  · have hh := h φ
    simp only [inner_sub_left]
    rw [integral_sub (inner_gradient_pairing_integrable hc φ) (inner_gradient_pairing_integrable hF φ)]
    exact sub_eq_zero.mpr hh
  · have hh := h φ
    simp only [inner_sub_left] at hh
    rw [integral_sub (inner_gradient_pairing_integrable hc φ) (inner_gradient_pairing_integrable hF φ)] at hh
    exact sub_eq_zero.mp hh

 theorem weak_linear_difference {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U W : Set (Euc n)}
    (hA : Continuous A) (hf : ContDiff ℝ 1 f) (hF : Continuous F)
    (h : WeakLinearEquation A f F U) (hWU : W⊆U)
    (e : Euc n) (s : ℝ) (hs : ∀ x∈W, x+s•e∈U) :
    WeakLinearEquation A (differenceQuotient f e s)
      (fun x ↦ vectorQuotient F e s x-vectorQuotient A e s x (gradient f (x+s•e))) W := by
  let V := fun x ↦ A x (gradient f x)-F x
  have hV : Continuous V := (hA.clm_apply (gradient_continuous_C1 hf)).sub hF
  have hflux := (weakLinear_iff_flux hA hf hF).mp h
  have hq := ((hflux.translate (s•e) hs).sub
    (hV.comp (continuous_id.add continuous_const)) hV (hflux.mono hWU)).const_smul s⁻¹
  have hqA : Continuous (vectorQuotient A e s) := by
    unfold vectorQuotient
    exact ((hA.comp (continuous_id.add continuous_const)).sub hA).const_smul s⁻¹
  have hqF : Continuous (fun x ↦ vectorQuotient F e s x-
      vectorQuotient A e s x (gradient f (x+s•e))) :=
    (vectorQuotient_continuous hF e s).sub (hqA.clm_apply
      ((gradient_continuous_C1 hf).comp (continuous_id.add continuous_const)))
  apply (weakLinear_iff_flux hA (differenceQuotient_contDiff hf e s) hqF).mpr
  have he (x : Euc n) : A x (gradient (differenceQuotient f e s) x)-
      (vectorQuotient F e s x-vectorQuotient A e s x (gradient f (x+s•e)))=
      s⁻¹•(V (x+s•e)-V x) := by
    rw [differenceQuotient_gradient (hf.differentiable (by simp))]
    simp only [vectorQuotient,smul_apply,sub_apply,map_smul,map_sub,V]
    module
  simpa only [he,Function.comp_def,Pi.add_apply,id_eq] using hq

end RPISingularHarnack

end

end OAI
