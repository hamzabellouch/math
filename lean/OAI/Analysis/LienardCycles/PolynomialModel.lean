import OAI.Analysis.LienardCycles.CanonicalAnalytic

namespace OAI

universe uE uF

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PolynomialModel

lemma local_flow_equiv {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (V : E → E) (W : F → F)
    (he : ∀ x, W (e x) = e (V x)) {x : E}
    (hf : ∃ f : F × ℝ → F, ContDiffAt ℝ ω f (e x,0) ∧
      ∀ᶠ q in 𝓝 (e x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun t => f (q.1,t)) (W (f q)) q.2) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun t => f (q.1,t)) (V (f q)) q.2 := by
  obtain ⟨f,hfd,hfe⟩ := hf
  let lift : E × ℝ → F × ℝ := fun q => (e q.1,q.2)
  have hl : ContDiff ℝ ω lift := (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  refine ⟨fun q => e.symm (f (lift q)),
    e.symm.contDiff.contDiffAt.comp (x,0) (hfd.comp (x,0) hl.contDiffAt),?_⟩
  filter_upwards [hl.continuous.continuousAt.eventually hfe] with q hq
  constructor
  · simp [lift,hq.1]
  · have hd := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt q.2 hq.2
    have hw : e.symm (W (f (lift q))) = V (e.symm (f (lift q))) := by
      rw [←e.apply_symm_apply (f (lift q)),he,e.symm_apply_apply,e.symm_apply_apply]
    simpa only [Function.comp_def,ContinuousLinearEquiv.coe_coe,hw] using hd

abbrev ModelState := (ℝ × ℝ) × (ℝ × ℝ)

noncomputable def stateEquiv : ModelState ≃L[ℝ] (Fin 4 → ℝ) :=
  (show ModelState ≃ₗ[ℝ] (Fin 4 → ℝ) from
    { toFun := fun z => ![z.1.1,z.1.2,z.2.1,z.2.2]
      invFun := fun v => ((v 0,v 1),(v 2,v 3))
      left_inv := by intro z; rfl
      right_inv := by intro v; ext i; fin_cases i <;> rfl
      map_add' := by intros; ext i; fin_cases i <;> rfl
      map_smul' := by intros; ext i; fin_cases i <;> rfl }).toContinuousLinearEquiv

lemma stateEquiv_apply (z : ModelState) : stateEquiv z = ![z.1.1,z.1.2,z.2.1,z.2.2] := rfl

noncomputable def profile (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.1*q.2 + q.1.2/2*q.2^2

lemma profile_contDiff : ContDiff ℝ ω profile :=
  (contDiff_fst.fst.mul contDiff_snd).add
    ((contDiff_fst.snd.div_const 2).mul (contDiff_snd.pow 2))

open MvPolynomial in
noncomputable def polynomials : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![0,0,X 0*X 2+C (1/2)*(X 1*X 2^2)-X 3,1]

lemma polynomial_representation (x : ModelState) :
    (fun i => MvPolynomial.eval (stateEquiv x) (polynomials i)) =
      stateEquiv (ArcFamilies.field profile x) := by
  ext i
  fin_cases i <;> simp [polynomials,stateEquiv_apply,ArcFamilies.field,profile]
  ring

theorem model_local_flow (x : ModelState) :
    ∃ f : ModelState × ℝ → ModelState, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (ArcFamilies.field profile (f q)) q.2 :=
  local_flow_equiv stateEquiv (ArcFamilies.field profile)
    (fun x i => MvPolynomial.eval x (polynomials i)) polynomial_representation
    (SmoothFlow.polynomial_local_flow polynomials (stateEquiv x))

theorem endpoints_analytic {p : ℝ × ℝ} {t h : ℝ} (hht : h < t) :
    ContDiffAt ℝ ω (ArcEndpoints.lowerFamily profile) ((p,t),h) ∧
    ContDiffAt ℝ ω (ArcEndpoints.upperFamily profile) ((p,t),h) :=
  CanonicalAnalytic.endpoints profile profile_contDiff model_local_flow hht

end QuinticLienard.PolynomialModel

end OAI
