import Mathlib

namespace OAI

/-! Smooth inverses and mixed maps near the identity. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def nearIdentityHomeomorph (f : E → E) (hf : ContDiff ℝ ∞ f)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) : E ≃ₜ E := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hl : LipschitzWith c (fun x => f x - x) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hd.sub differentiable_id)
    intro x
    rw [fderiv_sub (hd x) differentiableAt_id, fderiv_id]
    exact_mod_cast hb x
  have ha : ApproximatesLinearOn f
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ c :=
    hl.lipschitzOnWith.approximatesLinearOn
  apply ha.toHomeomorph f
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Or.inl hE
  · right
    simpa using hc

lemma nearIdentityHomeomorph_apply (f : E → E) (hf : ContDiff ℝ ∞ f)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) (x : E) :
    nearIdentityHomeomorph f hf c hc hb x = f x := rfl

def nearIdentityDerivative (f : E → E) (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub
    (ContinuousLinearMap.id ℝ E - fderiv ℝ f x)
    (by rw [norm_sub_rev]; exact (hb x).trans_lt (by exact_mod_cast hc)))

lemma nearIdentityDerivative_coe (f : E → E) (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) (x : E) :
    (nearIdentityDerivative f c hc hb x : E →L[ℝ] E) = fderiv ℝ f x := by
  change (1 : E →L[ℝ] E) - (ContinuousLinearMap.id ℝ E - fderiv ℝ f x) = _
  change ContinuousLinearMap.id ℝ E - (ContinuousLinearMap.id ℝ E - _) = _
  abel

theorem nearIdentityHomeomorph_smooth_inverse (f : E → E) (hf : ContDiff ℝ ∞ f)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) :
    ContDiff ℝ ∞ (nearIdentityHomeomorph f hf c hc hb).symm := by
  apply Homeomorph.contDiff_symm (f₀' := nearIdentityDerivative f c hc hb)
  · intro x
    rw [nearIdentityDerivative_coe]
    exact (hf.differentiable (by simp) x).hasFDerivAt
  · exact hf

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mixedMap (ψ : E × E → E × E) (z : E × E) : E × E := ((ψ z).1, z.2)

def spatialBlock : E × E →L[ℝ] E × E := (fst ℝ E E).prod 0

lemma spatialBlock_apply (v : E × E) : spatialBlock v = (v.1,0) := rfl

lemma norm_spatialBlock_le : ‖spatialBlock (E := E)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp only [spatialBlock_apply, Prod.norm_def, norm_zero, one_mul]
  exact max_le_max le_rfl (norm_nonneg _)

lemma contDiff_mixedMap {ψ : E × E → E × E} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (mixedMap ψ) := hψ.fst.prodMk contDiff_snd

lemma hasFDerivAt_mixedMap {ψ : E × E → E × E} {z : E × E}
    (hψ : DifferentiableAt ℝ ψ z) :
    HasFDerivAt (mixedMap ψ) (((fst ℝ E E).comp (fderiv ℝ ψ z)).prod (snd ℝ E E)) z :=
  hψ.hasFDerivAt.fst.prodMk hasFDerivAt_snd

lemma mixedMap_fderiv_sub {ψ : E × E → E × E} {z : E × E}
    (hψ : DifferentiableAt ℝ ψ z) :
    fderiv ℝ (mixedMap ψ) z - ContinuousLinearMap.id ℝ (E × E) =
      spatialBlock.comp (fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)) := by
  rw [(hasFDerivAt_mixedMap hψ).fderiv]
  ext v <;> simp [spatialBlock]

lemma mixedMap_small {ψ : E × E → E × E} {z : E × E}
    (hψ : DifferentiableAt ℝ ψ z) {c : ℝ} 
    (hb : ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c) :
    ‖fderiv ℝ (mixedMap ψ) z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c := by
  rw [mixedMap_fderiv_sub hψ]
  exact (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right norm_spatialBlock_le
    (norm_nonneg _)).trans (by simpa using hb))

variable [CompleteSpace E]

def mixedHomeomorph (ψ : E × E → E × E) (hψ : ContDiff ℝ ∞ ψ)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c) :
    (E × E) ≃ₜ (E × E) :=
  nearIdentityHomeomorph (mixedMap ψ) (contDiff_mixedMap hψ) c hc
    (fun z => mixedMap_small (hψ.differentiable (by simp) z) (hb z))

lemma mixedHomeomorph_apply (ψ : E × E → E × E) (hψ : ContDiff ℝ ∞ ψ)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c) (z : E × E) :
    mixedHomeomorph ψ hψ c hc hb z = ((ψ z).1,z.2) := rfl

lemma contDiff_mixedHomeomorph_symm (ψ : E × E → E × E) (hψ : ContDiff ℝ ∞ ψ)
    (c : ℝ≥0) (hc : c < 1)
    (hb : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ c) :
    ContDiff ℝ ∞ (mixedHomeomorph ψ hψ c hc hb).symm :=
  nearIdentityHomeomorph_smooth_inverse (mixedMap ψ) (contDiff_mixedMap hψ) c hc
    (fun z => mixedMap_small (hψ.differentiable (by simp) z) (hb z))

end NearbyLagrangian.Transport

end

end OAI
