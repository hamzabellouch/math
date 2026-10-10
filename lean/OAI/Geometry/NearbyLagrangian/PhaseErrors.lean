import Mathlib
import OAI.Geometry.NearbyLagrangian.StepData

namespace OAI

/-! Uniform phase and joint derivative error estimates. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter Set
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def shiftError (F : E × W → ℝ) (κ : E → W → E → ℝ)
    (q : E × (W × E)) : ℝ :=
  F (q.1+κ q.1 q.2.1 q.2.2 • q.2.2,q.2.1) - F (q.1,q.2.1)

omit [NormedSpace ℝ W] in
lemma shiftError_hasCompactSupport (F : E × W → ℝ) {ζ β : E → ℝ} {χ : W → ℝ}
    (hζ : HasCompactSupport ζ) (hβ : HasCompactSupport β) (hχ : HasCompactSupport χ) :
    HasCompactSupport (shiftError F (productCutoff ζ β χ)) := by
  apply HasCompactSupport.intro (hζ.prod (hχ.prod hβ))
  intro q hq
  have hcut : productCutoff ζ β χ q.1 q.2.1 q.2.2 = 0 := by
    by_cases hz : q.1 ∈ tsupport ζ
    · by_cases hw : q.2.1 ∈ tsupport χ
      · have hz' : q.2.2 ∉ tsupport β := fun hp => hq ⟨hz,hw,hp⟩
        simp only [productCutoff,image_eq_zero_of_notMem_tsupport hz',mul_zero,zero_mul]
      · simp only [productCutoff,image_eq_zero_of_notMem_tsupport hw,mul_zero]
    · simp only [productCutoff,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  simp only [shiftError,hcut,zero_smul,add_zero,sub_self]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] in
lemma compactSmooth_uniform_jet_bounds {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : V → ℝ} (hs : HasCompactSupport f) (hc : ContDiff ℝ ∞ f) :
    ∃ M₀ M₁ : ℝ, (∀ q, ‖f q‖ ≤ M₀) ∧ (∀ q, ‖fderiv ℝ f q‖ ≤ M₁) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv (by simp)
  have hds : HasCompactSupport (fderiv ℝ f) := hs.fderiv (𝕜 := ℝ)
  obtain ⟨M₀,hM₀⟩ := hs.exists_bound_of_continuous hc.continuous
  obtain ⟨M₁,hM₁⟩ := hds.exists_bound_of_continuous hd
  exact ⟨M₀,M₁,hM₀,hM₁⟩

namespace StepData

variable (S : StepData (E := E) (W := W))

lemma contDiff_shiftError (hζU : tsupport S.ζ ⊆ S.U) :
    ContDiff ℝ ∞ (shiftError S.F S.κ) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.1 ∈ tsupport S.ζ
  · have hk : ContDiffAt ℝ ∞ (fun r : E × (W × E) => S.κ r.1 r.2.1 r.2.2) q :=
      (((S.smooth_ζ.comp contDiff_fst).mul (S.smooth_β.comp contDiff_snd.snd)).mul
        (S.smooth_χ.comp contDiff_snd.fst)).contDiffAt
    have hshift := (contDiffAt_fst.add (hk.smul contDiffAt_snd.snd)).prodMk contDiffAt_snd.fst
    exact ((S.smooth_F _ (S.shift_mem _ (hζU hq) _ _) _).comp q hshift).sub
      ((S.smooth_F _ (hζU hq) _).comp q (contDiffAt_fst.prodMk contDiffAt_snd.fst))
  · have hζ : S.ζ =ᶠ[𝓝 q.1] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have he : shiftError S.F S.κ =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(continuous_fst.continuousAt (x := q)).eventually hζ] with r hr
      simp only [shiftError,κ,productCutoff,hr,zero_mul,zero_smul,add_zero,sub_self]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem shiftError_uniform_bounds (hζU : tsupport S.ζ ⊆ S.U)
    (hζ : HasCompactSupport S.ζ) (hβ : HasCompactSupport S.β) (hχ : HasCompactSupport S.χ) :
    ∃ M₀ M₁ : ℝ, (∀ q, ‖shiftError S.F S.κ q‖ ≤ M₀) ∧
      (∀ q, ‖fderiv ℝ (shiftError S.F S.κ) q‖ ≤ M₁) := by
  exact compactSmooth_uniform_jet_bounds
    (shiftError_hasCompactSupport S.F hζ hβ hχ) (S.contDiff_shiftError hζU)

end StepData
end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter Set
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def homogeneousReference (g : E × W → ℝ) (X : E) (v : W × (E × E)) : ℝ :=
  g (X,v.1) - inner ℝ v.2.1 v.2.2

def phaseError (F g : E × W → ℝ) (σ : E × E → ℝ) (κ : E → W → E → ℝ)
    (X : E) (v : W × (E × E)) : ℝ :=
  shiftedPhase F σ κ X v.1 v.2.1 v.2.2 - homogeneousReference g X v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
lemma phaseError_eq (F g : E × W → ℝ) (σ : E × E → ℝ) (κ : E → W → E → ℝ)
    (X : E) (v : W × (E × E)) :
    phaseError F g σ κ X v = shiftError F κ (X,v.1,v.2.1) +
      (F (X,v.1)-g (X,v.1)) + σ (X,v.2.2) := by
  unfold phaseError shiftedPhase homogeneousReference shiftError
  ring

def verticalForget : W × (E × E) →L[ℝ] E × (W × E) :=
  (0 : W × (E × E) →L[ℝ] E).prod ((fst ℝ W (E × E)).prod
    ((fst ℝ E E).comp (snd ℝ W (E × E))))

lemma verticalForget_apply (v : W × (E × E)) :
    verticalForget (E := E) (W := W) v = (0,v.1,v.2.1) := rfl

lemma norm_verticalForget_le : ‖verticalForget (E := E) (W := W)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp only [verticalForget_apply,Prod.norm_def,norm_zero,one_mul]
  apply max_le
  · exact le_trans (norm_nonneg v.1) (le_max_left _ _)
  · exact max_le_max le_rfl (le_max_left _ _)

def verticalMomentum : W × (E × E) →L[ℝ] E × E :=
  (0 : W × (E × E) →L[ℝ] E).prod ((snd ℝ E E).comp (snd ℝ W (E × E)))

lemma verticalMomentum_apply (v : W × (E × E)) :
    verticalMomentum (E := E) (W := W) v = (0,v.2.2) := rfl

lemma norm_verticalMomentum_le : ‖verticalMomentum (E := E) (W := W)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp only [verticalMomentum_apply,Prod.norm_def,norm_zero,one_mul]
  exact max_le (le_trans (norm_nonneg _) (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_right _ _))

lemma hasFDerivAt_phaseError {F g : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} (X : E) (v : W × (E × E))
    (hshift : DifferentiableAt ℝ (shiftError F κ) (X,v.1,v.2.1))
    (hR : DifferentiableAt ℝ (fun w => F (X,w)-g (X,w)) v.1)
    (hσ : DifferentiableAt ℝ σ (X,v.2.2)) :
    HasFDerivAt (phaseError F g σ κ X)
      ((fderiv ℝ (shiftError F κ) (X,v.1,v.2.1)).comp verticalForget +
        (fderiv ℝ (fun w => F (X,w)-g (X,w)) v.1).comp (fst ℝ W (E × E)) +
        (fderiv ℝ σ (X,v.2.2)).comp verticalMomentum) v := by
  have ha : HasFDerivAt (fun r : W × (E × E) => (X,r.1,r.2.1))
      (verticalForget (E := E) (W := W)) v :=
    (hasFDerivAt_const X v).prodMk
      (hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp v hasFDerivAt_snd))
  have hb : HasFDerivAt (fun r : W × (E × E) => (X,r.2.2))
      (verticalMomentum (E := E) (W := W)) v :=
    (hasFDerivAt_const X v).prodMk
      (hasFDerivAt_snd.comp v hasFDerivAt_snd)
  have h := ((hshift.hasFDerivAt.comp v ha).add
    (hR.hasFDerivAt.comp v hasFDerivAt_fst)).add (hσ.hasFDerivAt.comp v hb)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r => phaseError_eq F g σ κ X r))

lemma norm_phaseError_fderiv_le {F g : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} (X : E) (v : W × (E × E))
    (hshift : DifferentiableAt ℝ (shiftError F κ) (X,v.1,v.2.1))
    (hR : DifferentiableAt ℝ (fun w => F (X,w)-g (X,w)) v.1)
    (hσ : DifferentiableAt ℝ σ (X,v.2.2)) :
    ‖fderiv ℝ (phaseError F g σ κ X) v‖ ≤
      ‖fderiv ℝ (shiftError F κ) (X,v.1,v.2.1)‖ +
      ‖fderiv ℝ (fun w => F (X,w)-g (X,w)) v.1‖ + ‖fderiv ℝ σ (X,v.2.2)‖ := by
  let A := fderiv ℝ (shiftError F κ) (X,v.1,v.2.1)
  let B := fderiv ℝ (fun w => F (X,w)-g (X,w)) v.1
  let C := fderiv ℝ σ (X,v.2.2)
  have hA : ‖A.comp (verticalForget (E := E) (W := W))‖ ≤ ‖A‖ :=
    (A.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg A) norm_verticalForget_le)
  have hB : ‖B.comp (fst ℝ W (E × E))‖ ≤ ‖B‖ :=
    (B.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg B) (norm_fst_le ..))
  have hC : ‖C.comp (verticalMomentum (E := E) (W := W))‖ ≤ ‖C‖ :=
    (C.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg C) norm_verticalMomentum_le)
  rw [(hasFDerivAt_phaseError X v hshift hR hσ).fderiv]
  calc
    _ ≤ ‖A.comp verticalForget + B.comp (fst ℝ W (E × E))‖ +
        ‖C.comp (verticalMomentum (E := E) (W := W))‖ :=
          norm_add_le (A.comp verticalForget + B.comp (fst ℝ W (E × E)))
            (C.comp verticalMomentum)
    _ ≤ (‖A.comp verticalForget‖ + ‖B.comp (fst ℝ W (E × E))‖) +
        ‖C.comp (verticalMomentum (E := E) (W := W))‖ := add_le_add
          (norm_add_le (A.comp verticalForget) (B.comp (fst ℝ W (E × E)))) le_rfl
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := add_le_add (add_le_add hA hB) hC

namespace StepData

variable (S : StepData (E := E) (W := W))

theorem phaseError_uniform_bounds {g : E × W → ℝ}
    (hζU : tsupport S.ζ ⊆ S.U)
    (hζ : HasCompactSupport S.ζ) (hβ : HasCompactSupport S.β) (hχ : HasCompactSupport S.χ)
    (hσ : HasCompactSupport S.σ)
    (hR : ∀ X ∈ S.U, Differentiable ℝ (fun w => S.F (X,w)-g (X,w)))
    (bR₀ : ∃ M : ℝ, ∀ X ∈ S.U, ∀ w, ‖S.F (X,w)-g (X,w)‖ ≤ M)
    (bR₁ : ∃ M : ℝ, ∀ X ∈ S.U, ∀ w,
      ‖fderiv ℝ (fun w => S.F (X,w)-g (X,w)) w‖ ≤ M) :
    ∃ M₀ M₁ : ℝ, (∀ X ∈ S.U, ∀ v, ‖phaseError S.F g S.σ S.κ X v‖ ≤ M₀) ∧
      (∀ X ∈ S.U, ∀ v, ‖fderiv ℝ (phaseError S.F g S.σ S.κ X) v‖ ≤ M₁) := by
  obtain ⟨A₀,A₁,hA₀,hA₁⟩ := S.shiftError_uniform_bounds hζU hζ hβ hχ
  obtain ⟨B₀,hB₀⟩ := bR₀
  obtain ⟨B₁,hB₁⟩ := bR₁
  obtain ⟨C₀,C₁,hC₀,hC₁⟩ := compactSmooth_uniform_jet_bounds hσ S.smooth_σ
  refine ⟨A₀+B₀+C₀,A₁+B₁+C₁,?_,?_⟩
  · intro X hX v
    rw [phaseError_eq]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hA₀ _) (hB₀ X hX _))) (hC₀ _))
  · intro X hX v
    exact (norm_phaseError_fderiv_le X v
      ((S.contDiff_shiftError hζU).differentiable (by simp) _)
      (hR X hX _) (S.smooth_σ.differentiable (by simp) _)).trans
      (add_le_add (add_le_add (hA₁ _) (hB₁ X hX _)) (hC₁ _))

end StepData
end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def jointForget : E × (W × (E × E)) →L[ℝ] E × (W × E) :=
  (fst ℝ E (W × (E × E))).prod
    (((fst ℝ W (E × E)).comp (snd ℝ E (W × (E × E)))).prod
      ((fst ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))))

def jointOld : E × (W × (E × E)) →L[ℝ] E × W :=
  (fst ℝ E (W × (E × E))).prod
    ((fst ℝ W (E × E)).comp (snd ℝ E (W × (E × E))))

def jointMixed : E × (W × (E × E)) →L[ℝ] E × E :=
  (fst ℝ E (W × (E × E))).prod
    ((snd ℝ E E).comp ((snd ℝ W (E × E)).comp (snd ℝ E (W × (E × E)))))

lemma norm_jointForget_le : ‖jointForget (E := E) (W := W)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change max ‖v.1‖ (max ‖v.2.1‖ ‖v.2.2.1‖) ≤ 1 * ‖v‖
  rw [one_mul]
  exact max_le (norm_fst_le v) (max_le ((norm_fst_le v.2).trans (norm_snd_le v))
    ((norm_fst_le v.2.2).trans ((norm_snd_le v.2).trans (norm_snd_le v))))

lemma norm_jointOld_le : ‖jointOld (E := E) (W := W)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change max ‖v.1‖ ‖v.2.1‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact max_le (norm_fst_le v) ((norm_fst_le v.2).trans (norm_snd_le v))

lemma norm_jointMixed_le : ‖jointMixed (E := E) (W := W)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change max ‖v.1‖ ‖v.2.2.2‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact max_le (norm_fst_le v)
    ((norm_snd_le v.2.2).trans ((norm_snd_le v.2).trans (norm_snd_le v)))

lemma hasFDerivAt_jointPhaseError {F g : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} (q : E × (W × (E × E)))
    (hshift : DifferentiableAt ℝ (shiftError F κ) (q.1,q.2.1,q.2.2.1))
    (hR : DifferentiableAt ℝ (F-g) (q.1,q.2.1))
    (hσ : DifferentiableAt ℝ σ (q.1,q.2.2.2)) :
    HasFDerivAt (fun q : E × (W × (E × E)) => phaseError F g σ κ q.1 q.2)
      ((fderiv ℝ (shiftError F κ) (q.1,q.2.1,q.2.2.1)).comp jointForget +
       (fderiv ℝ (F-g) (q.1,q.2.1)).comp jointOld +
       (fderiv ℝ σ (q.1,q.2.2.2)).comp jointMixed) q := by
  have h := ((hshift.hasFDerivAt.comp q (jointForget (E := E) (W := W)).hasFDerivAt).add
    (hR.hasFDerivAt.comp q (jointOld (E := E) (W := W)).hasFDerivAt)).add
    (hσ.hasFDerivAt.comp q (jointMixed (E := E) (W := W)).hasFDerivAt)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r =>
    phaseError_eq F g σ κ r.1 r.2)

lemma norm_jointPhaseError_fderiv_le {F g : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} (q : E × (W × (E × E)))
    (hshift : DifferentiableAt ℝ (shiftError F κ) (q.1,q.2.1,q.2.2.1))
    (hR : DifferentiableAt ℝ (F-g) (q.1,q.2.1))
    (hσ : DifferentiableAt ℝ σ (q.1,q.2.2.2)) :
    ‖fderiv ℝ (fun q : E × (W × (E × E)) => phaseError F g σ κ q.1 q.2) q‖ ≤
      ‖fderiv ℝ (shiftError F κ) (q.1,q.2.1,q.2.2.1)‖ +
      ‖fderiv ℝ (F-g) (q.1,q.2.1)‖ + ‖fderiv ℝ σ (q.1,q.2.2.2)‖ := by
  let A := fderiv ℝ (shiftError F κ) (q.1,q.2.1,q.2.2.1)
  let B := fderiv ℝ (F-g) (q.1,q.2.1)
  let C := fderiv ℝ σ (q.1,q.2.2.2)
  have hA : ‖A.comp (jointForget (E := E) (W := W))‖ ≤ ‖A‖ :=
    (A.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg A) norm_jointForget_le)
  have hB : ‖B.comp (jointOld (E := E) (W := W))‖ ≤ ‖B‖ :=
    (B.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg B) norm_jointOld_le)
  have hC : ‖C.comp (jointMixed (E := E) (W := W))‖ ≤ ‖C‖ :=
    (C.opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg C) norm_jointMixed_le)
  rw [(hasFDerivAt_jointPhaseError q hshift hR hσ).fderiv]
  calc
    _ ≤ ‖A.comp jointForget + B.comp jointOld‖ +
        ‖C.comp (jointMixed (E := E) (W := W))‖ :=
          norm_add_le (A.comp jointForget + B.comp jointOld) (C.comp jointMixed)
    _ ≤ (‖A.comp jointForget‖ + ‖B.comp jointOld‖) +
        ‖C.comp (jointMixed (E := E) (W := W))‖ := add_le_add
          (norm_add_le (A.comp jointForget) (B.comp jointOld)) le_rfl
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := add_le_add (add_le_add hA hB) hC

namespace StepData
variable (S : StepData (E := E) (W := W))

theorem jointPhaseError_uniform_bounds {g : E × W → ℝ}
    (hζU : tsupport S.ζ ⊆ S.U)
    (hζ : HasCompactSupport S.ζ) (hβ : HasCompactSupport S.β) (hχ : HasCompactSupport S.χ)
    (hσ : HasCompactSupport S.σ)
    (hR : ∀ q : E × W, q.1 ∈ S.U → DifferentiableAt ℝ (S.F-g) q)
    (bR₀ : ∃ M : ℝ, ∀ q : E × W, q.1 ∈ S.U → ‖S.F q-g q‖ ≤ M)
    (bR₁ : ∃ M : ℝ, ∀ q : E × W, q.1 ∈ S.U → ‖fderiv ℝ (S.F-g) q‖ ≤ M) :
    ∃ M₀ M₁ : ℝ, (∀ q : E × (W × (E × E)), q.1 ∈ S.U →
      ‖phaseError S.F g S.σ S.κ q.1 q.2‖ ≤ M₀) ∧
      (∀ q : E × (W × (E × E)), q.1 ∈ S.U →
       ‖fderiv ℝ (fun q => phaseError S.F g S.σ S.κ q.1 q.2) q‖ ≤ M₁) := by
  obtain ⟨A₀,A₁,hA₀,hA₁⟩ := S.shiftError_uniform_bounds hζU hζ hβ hχ
  obtain ⟨B₀,hB₀⟩ := bR₀
  obtain ⟨B₁,hB₁⟩ := bR₁
  obtain ⟨C₀,C₁,hC₀,hC₁⟩ := compactSmooth_uniform_jet_bounds hσ S.smooth_σ
  refine ⟨A₀+B₀+C₀,A₁+B₁+C₁,?_,?_⟩
  · intro q hq
    rw [phaseError_eq]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hA₀ _) (hB₀ (q.1,q.2.1) hq))) (hC₀ _))
  · intro q hq
    exact (norm_jointPhaseError_fderiv_le q
      ((S.contDiff_shiftError hζU).differentiable (by simp) _)
      (hR _ hq) (S.smooth_σ.differentiable (by simp) _)).trans
      (add_le_add (add_le_add (hA₁ _) (hB₁ _ hq)) (hC₁ _))

end StepData
end NearbyLagrangian.Transport

end

end OAI
