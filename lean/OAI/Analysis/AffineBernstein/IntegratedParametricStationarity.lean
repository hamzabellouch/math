import Mathlib
import OAI.Analysis.AffineBernstein.AffineParametricStationarity
import OAI.Analysis.AffineBernstein.CompactDifferentiation
import OAI.Analysis.AffineBernstein.ParametricSmoothness

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma graphVariationArea_eq_of_notMem {n : ℕ} {K : Set (Space n)}
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hβK : tsupport β ⊆ K) (haK : ∀ k, tsupport (a k) ⊆ K)
    {x : Space n} (hx : x ∉ K) (t : ℝ) :
    graphVariationArea u β a x t = affineAreaDensity u x := by
  have hd (f : Space n → ℝ) (hf : tsupport f ⊆ K) (i : Fin n) :
      dirDeriv (coordinateVector n i) f x = 0 := by
    unfold dirDeriv
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hf h))]
    rfl
  have hh (f : Space n → ℝ) (hf : tsupport f ⊆ K) (i j : Fin n) :
      hessian f x i j = 0 := by
    unfold hessian
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hf (tsupport_fderiv_apply_subset ℝ _ h)))]
    rfl
  have hB : hessian β x = 0 := Matrix.ext (fun i j => hh β hβK i j)
  have hC (k : Fin n) : hessian (a k) x = 0 := Matrix.ext (fun i j => hh (a k) (haK k) i j)
  have hJ : horizontalJacobian a x = 0 := Matrix.ext (fun i j => hd (a i) (haK i) j)
  have hzero : Matrix.of (t • fun (_ _ : Fin n) => (0 : ℝ)) = 0 := by
    ext i j
    simp
  simp [graphVariationArea, variationAreaDensity, variationSecondForm, hB, hC, hJ, hzero,
    affineAreaDensity, smul_zero]

lemma fderiv_param_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → ℝ} {x : E} (hF : DifferentiableAt ℝ F (0,x)) :
    fderiv ℝ F (0,x) (1,0) = deriv (fun t => F (t,x)) 0 := by
  have hh := hF.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
  have hh' : HasDerivAt (fun t => F (t,x)) (fderiv ℝ F (0,x) (1,0)) 0 := by
    convert! hh using 1
  exact hh'.deriv.symm

/- Actual differentiation of the compact affine-area functional, not just
an integrated pointwise derivative. -/
theorem affineMaximal_parametric_area_stationary {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    HasDerivAt (fun t : ℝ => ∫ x in K, graphVariationArea u β a x t) 0 0 := by
  let U := graphVariationRegular Ω u β a
  let F := fun p : ℝ × Space n => graphVariationArea u β a p.2 p.1
  have hU : IsOpen U := isOpen_graphVariationRegular hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn)
  have hF : ContDiffOn ℝ ∞ F U := contDiffOn_graphVariationArea hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn)
  have h0 (x : Space n) (hx : x ∈ Ω) : (0,x) ∈ U :=
    zero_mem_graphVariationRegular hx (hp x hx)
  have hD := hasDerivAt_setIntegral_compact (μ := volume) hK hU
    (by rintro ⟨t,x⟩ ⟨ht,hx⟩; simp only [mem_singleton_iff] at ht; subst t; exact h0 x (hKΩ hx)) hF
  have he (x : Space n) (hx : x ∈ K) :
      fderiv ℝ F (0,x) (1,0) = deriv (graphVariationArea u β a x) 0 := by
    exact fderiv_param_eq_deriv ((hF.contDiffAt
      (hU.mem_nhds (h0 x (hKΩ hx)))).differentiableAt (by simp))
  have hz (x : Space n) (hx : x ∉ K) : deriv (graphVariationArea u β a x) 0 = 0 := by
    have heq : graphVariationArea u β a x = fun _ => affineAreaDensity u x :=
      funext (graphVariationArea_eq_of_notMem hβK haK hx)
    rw [heq, deriv_const]
  have hi := affineMaximal_parametric_first_variation hΩ hK hKΩ hu hp hm hβ hβK ha haK
  have hI : (∫ x in K, fderiv ℝ F (0,x) (1,0)) = 0 := by
    rw [setIntegral_congr_fun hK.measurableSet he,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hz x (fun hk => hx (hKΩ hk)))] at hi
    exact hi.2
  simpa only [F, hI] using hD

/- The compact affine-area functional of every arbitrary affine image is
stationary. All derivatives and integrals are the literal geometric density. -/
theorem affineMaximal_affine_parametric_area_stationary {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, affineParametricVariationArea L v u β a x t) 0 0 := by
  let c := Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2))
  have he : (fun t : ℝ => ∫ x in K, affineParametricVariationArea L v u β a x t) =
      fun t => c * ∫ x in K, graphVariationArea u β a x t := by
    funext t
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hK.measurableSet (fun x hx =>
      affineParametricVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn) L v (hKΩ hx) t)
  rw [he]
  simpa using (affineMaximal_parametric_area_stationary hΩ hK hKΩ hu hp hm hβ hβK ha haK).const_mul c

end AffineBernstein
end

end OAI
