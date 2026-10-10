import OAI.Analysis.Pureness.States.FiniteFamilyPullback

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem finiteFamily_extreme_restriction_central_projection_split
    (F : CompatibleFiniteQuasitrace D)
    (hmono : ∀ n, Monotone (fun a : CuntzTrace.Positive (CuntzTrace.FinMatrix D n) => (F.level n a.1).re))
    (hF : F.level 1 1=1) (α : A →⋆ₐ[ℂ] D)
    (hext : (fun x => F.toTwoQuasitrace.base (α x)) ∈
      (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ)
    (p : D) (hp : IsStarProjection p) (hc : ∀ x, Commute p x)
    (hcpos : 0 < (F.toTwoQuasitrace.base p).re) (hdpos : 0 < (F.toTwoQuasitrace.base (1-p)).re) (x : A) :
    F.toTwoQuasitrace.base (p * α x) = F.toTwoQuasitrace.base p * F.toTwoQuasitrace.base (α x) := by
  have hT := F.toTwoQuasitrace_unit hF
  have hq : ∀ z : D, Commute (1-p) z := fun z => (Commute.one_left z).sub_left (hc z)
  have hsum : F.toTwoQuasitrace.base p + F.toTwoQuasitrace.base (1-p) = 1 := by
    simpa only [mul_one, hT] using (F.toTwoQuasitrace.base.central_projection_split p hp hc 1).symm
  let c := (F.toTwoQuasitrace.base p).re
  let d := (F.toTwoQuasitrace.base (1-p)).re
  have hcp : F.toTwoQuasitrace.base p = (c : ℂ) := Complex.eq_re_of_ofReal_le (F.toTwoQuasitrace.base.nonneg p hp.nonneg)
  have hdq : F.toTwoQuasitrace.base (1-p) = (d : ℂ) :=
    Complex.eq_re_of_ofReal_le (F.toTwoQuasitrace.base.nonneg (1-p) hp.one_sub.nonneg)
  have hcd : c+d=1 := congrArg Complex.re hsum
  let φ := (centralProjectionHom p hp hc).comp α.toNonUnitalStarAlgHom
  let ψ := (centralProjectionHom (1-p) hp.one_sub hq).comp α.toNonUnitalStarAlgHom
  let U : A → ℂ := fun x => ((c⁻¹ : ℝ) : ℂ)*F.toTwoQuasitrace.base (φ x)
  let V : A → ℂ := fun x => ((d⁻¹ : ℝ) : ℂ)*F.toTwoQuasitrace.base (ψ x)
  have hUc : U ∈ normalizedFiniteBaseQuasitraceCarrier :=
    F.normalized_comap_mem hmono φ c hcpos (by
      change F.toTwoQuasitrace.base (p*α 1)=(c : ℂ)
      simpa only [map_one,mul_one] using hcp)
  have hVc : V ∈ normalizedFiniteBaseQuasitraceCarrier :=
    F.normalized_comap_mem hmono ψ d hdpos (by
      change F.toTwoQuasitrace.base ((1-p)*α 1)=(d : ℂ)
      simpa only [map_one,mul_one] using hdq)
  have hseg : (fun z => F.toTwoQuasitrace.base (α z)) ∈ openSegment ℝ U V := by
    refine ⟨c,d,hcpos,hdpos,hcd,?_⟩
    funext z
    change (c : ℂ)*((c⁻¹ : ℝ)*F.toTwoQuasitrace.base (p*α z)) +
      (d : ℂ)*((d⁻¹ : ℝ)*F.toTwoQuasitrace.base ((1-p)*α z)) = F.toTwoQuasitrace.base (α z)
    rw [Complex.ofReal_inv, Complex.ofReal_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hcpos.ne'),
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hdpos.ne'), one_mul, one_mul]
    exact (F.toTwoQuasitrace.base.central_projection_split p hp hc (α z)).symm
  have hUeq : U = fun z => F.toTwoQuasitrace.base (α z) := hext.2 hUc hVc hseg
  have he := congrArg (fun g : A → ℂ => g x) hUeq
  change (c⁻¹ : ℝ)*F.toTwoQuasitrace.base (p*α x) = F.toTwoQuasitrace.base (α x) at he
  have hm := congrArg (fun z : ℂ => (c : ℂ)*z) he
  rw [← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hcpos.ne'), one_mul] at hm
  simpa only [hcp] using hm
end CuntzPureness

end

end OAI
