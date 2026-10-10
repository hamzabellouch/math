import OAI.MathematicalPhysics.Elasticity.Basic
import OAI.MathematicalPhysics.Elasticity.Extension
import OAI.MathematicalPhysics.Elasticity.BoundaryLayers

namespace OAI

section
/-! Smooth boundary geometry in open partial homeomorphism charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

def SourceSmoothBoundary (Ω : Set X) : Prop :=
  ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph X X,
    x ∈ e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
    e x 0 = 0 ∧
    ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0

def SourceDomain (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ SourceSmoothBoundary Ω

lemma SourceSmoothBoundary.to_inherited {Ω : Set X} (h : SourceSmoothBoundary Ω) :
    SmoothBoundary Ω := by
  intro x hx
  obtain ⟨e, hxs, he, hi, h0, hΩ⟩ := h x hx
  exact ⟨e, hxs, he, hi, h0, hΩ⟩

lemma SourceDomain.to_inherited {Ω : Set X} (h : SourceDomain Ω) : Domain Ω :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.to_inherited⟩

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x ∈ e.source)

include he hi hx

lemma chart_fderiv_left_inverse :
    (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ X := by
  have hd := (he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hx)
  have hd' := (hi.differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hEq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  rw [← fderiv_comp x hd' hd, hEq.fderiv_eq, fderiv_id]

lemma chart_fderiv_right_inverse :
    (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x)) = ContinuousLinearMap.id ℝ X := by
  simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv hx] using
    chart_fderiv_left_inverse e.symm hi he (e.map_source hx)

/-- The derivative of a smooth open boundary chart is continuously invertible. -/
def chartDerivativeEquiv : X ≃L[ℝ] X := {
  toLinearEquiv := {
    toLinearMap := (fderiv ℝ e x).toLinearMap
    invFun := fderiv ℝ e.symm (e x)
    left_inv := fun v => by
      have h := congrArg (fun J : X →L[ℝ] X => J v) (chart_fderiv_left_inverse e he hi hx)
      exact h
    right_inv := fun v => by
      have h := congrArg (fun J : X →L[ℝ] X => J v) (chart_fderiv_right_inverse e he hi hx)
      exact h }
  continuous_toFun := (fderiv ℝ e x).continuous
  continuous_invFun := (fderiv ℝ e.symm (e x)).continuous }

@[simp] lemma chartDerivativeEquiv_apply (v : X) :
    chartDerivativeEquiv e he hi hx v = fderiv ℝ e x v := rfl

end Elasticity

end
end
section
/-! Orthogonal normalization of an honest physical boundary chart. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

/-- Normal covector of a linear boundary-coordinate map, represented in the
fixed Euclidean coordinates by Riesz duality. -/
def coordinateNormal (B : X ≃L[ℝ] X) : X :=
  (InnerProductSpace.toDual ℝ X).symm
    ((EuclideanSpace.proj (0 : Fin 3)).comp B.toContinuousLinearMap)

lemma coordinateNormal_inner (B : X ≃L[ℝ] X) (z : X) :
    inner ℝ (coordinateNormal B) z = B z 0 := by
  exact InnerProductSpace.toDual_symm_apply

lemma coordinateNormal_ne_zero (B : X ≃L[ℝ] X) : coordinateNormal B ≠ 0 := by
  intro h
  have hi := coordinateNormal_inner B (B.symm (EuclideanSpace.single 0 1))
  rw [h, inner_zero_left, B.apply_symm_apply] at hi
  simp at hi

/-- A physical orthogonal frame whose first vector is the inward normal. -/
def coordinateFrame (B : X ≃L[ℝ] X) : X ≃ₗᵢ[ℝ] X :=
  (ℝ ∙ (EuclideanSpace.single 2 1 - ‖coordinateNormal B‖⁻¹ • coordinateNormal B))ᗮ.reflection

lemma coordinateFrame_first (B : X ≃L[ℝ] X) :
    coordinateFrame B (EuclideanSpace.single 2 1) =
      ‖coordinateNormal B‖⁻¹ • coordinateNormal B := by
  apply Submodule.reflection_sub
  rw [PiLp.norm_single, norm_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (coordinateNormal_ne_zero B)

/-- This normalization preserves the physical half-space without changing its
positive side. It also keeps the physical metric Euclidean at the base point. -/
theorem coordinateFrame_normal (B : X ≃L[ℝ] X) (z : X) :
    B (coordinateFrame B z) 0 = ‖coordinateNormal B‖ * z 2 := by
  have hn : ‖coordinateNormal B‖ ≠ 0 := norm_ne_zero_iff.mpr (coordinateNormal_ne_zero B)
  have h : ‖coordinateNormal B‖ • coordinateFrame B (EuclideanSpace.single 2 1) =
      coordinateNormal B := by
    rw [coordinateFrame_first, smul_smul, mul_inv_cancel₀ hn, one_smul]
  calc
    B (coordinateFrame B z) 0 = inner ℝ (coordinateNormal B) (coordinateFrame B z) :=
      (coordinateNormal_inner B _).symm
    _ = inner ℝ (‖coordinateNormal B‖ • coordinateFrame B (EuclideanSpace.single 2 1))
        (coordinateFrame B z) := congrArg (fun v => inner ℝ v (coordinateFrame B z)) h.symm
    _ = ‖coordinateNormal B‖ * z 2 := by
      rw [inner_smul_left, (coordinateFrame B).inner_map_map, EuclideanSpace.inner_single_left]
      simp

lemma coordinateFrame_positive (B : X ≃L[ℝ] X) (z : X) :
    0 < B (coordinateFrame B z) 0 ↔ 0 < z 2 := by
  rw [coordinateFrame_normal]
  exact mul_pos_iff_of_pos_left (norm_pos_iff.mpr (coordinateNormal_ne_zero B))

end Elasticity

end
end
section
/-! Honest boundary coordinates with orthogonal physical derivative at the
base point. The inward normal is coordinate 2, matching the frozen physical
half-space ODE. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x ∈ e.source)

def normalizedLinear : X ≃L[ℝ] X :=
  (coordinateFrame (chartDerivativeEquiv e he hi hx)).toContinuousLinearEquiv.trans
    (chartDerivativeEquiv e he hi hx)

def normalizedAffine : X ≃ₜ X :=
  (normalizedLinear e he hi hx).toHomeomorph.trans (Homeomorph.addRight (e x))

def normalizedParam : OpenPartialHomeomorph X X :=
  (normalizedAffine e he hi hx).toOpenPartialHomeomorph.trans e.symm

@[simp] lemma normalizedAffine_apply (z : X) :
    normalizedAffine e he hi hx z = normalizedLinear e he hi hx z + e x := rfl

@[simp] lemma normalizedParam_apply (z : X) :
    normalizedParam e he hi hx z = e.symm (normalizedLinear e he hi hx z + e x) := rfl

lemma normalizedParam_source :
    (normalizedParam e he hi hx).source =
      {z | normalizedLinear e he hi hx z + e x ∈ e.target} := by
  ext z
  simp [normalizedParam]

@[simp] lemma normalizedParam_target :
    (normalizedParam e he hi hx).target = e.source := by
  ext z
  simp [normalizedParam]

lemma normalizedParam_zero_source : (0 : X) ∈ (normalizedParam e he hi hx).source := by
  rw [normalizedParam_source]
  simpa using e.map_source hx

@[simp] lemma normalizedParam_zero : normalizedParam e he hi hx 0 = x := by
  simp [e.left_inv hx]

lemma normalizedParam_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalizedParam e he hi hx)
      (normalizedParam e he hi hx).source := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z => normalizedLinear e he hi hx z + e x) :=
    (normalizedLinear e he hi hx).contDiff.add contDiff_const
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => e.symm (normalizedLinear e he hi hx z + e x)) _
  apply hi.comp ha.contDiffOn
  intro z hz
  simpa only [normalizedParam_source, Set.mem_ofPred_eq] using hz

lemma normalizedParam_symm_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalizedParam e he hi hx).symm
      (normalizedParam e he hi hx).target := by
  rw [normalizedParam_target]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => e y - e x) e.source :=
    he.sub contDiffOn_const
  exact ((normalizedLinear e he hi hx).symm.contDiff.comp_contDiffOn hs)

lemma normalizedParam_fderiv :
    HasFDerivAt (normalizedParam e he hi hx)
      (coordinateFrame (chartDerivativeEquiv e he hi hx)).toContinuousLinearEquiv.toContinuousLinearMap 0 := by
  let B := chartDerivativeEquiv e he hi hx
  let Q := coordinateFrame B
  have hb : HasFDerivAt e.symm B.symm.toContinuousLinearMap (e x) :=
    ((hi.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))).hasFDerivAt
  have ha := ((normalizedLinear e he hi hx).hasFDerivAt (x := (0 : X))).add_const (e x)
  have hcomp := (by simpa using hb : HasFDerivAt e.symm B.symm.toContinuousLinearMap
    (normalizedLinear e he hi hx 0 + e x)).comp 0 ha
  have hQ : B.symm.toContinuousLinearMap.comp
      (normalizedLinear e he hi hx).toContinuousLinearMap =
      Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    exact B.symm_apply_apply (Q z)
  rw [hQ] at hcomp
  exact hcomp

lemma normalizedParam_halfspace {Ω : Set X} (h0 : e x 0 = 0)
    (hΩ : ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0)
    {z : X} (hz : z ∈ (normalizedParam e he hi hx).source) :
    normalizedParam e he hi hx z ∈ Ω ↔ 0 < z 2 := by
  have ht : normalizedLinear e he hi hx z + e x ∈ e.target :=
    by simpa only [normalizedParam_source, Set.mem_ofPred_eq] using hz
  rw [normalizedParam_apply, hΩ _ (e.map_target ht), e.right_inv ht]
  change 0 < (chartDerivativeEquiv e he hi hx)
    (coordinateFrame (chartDerivativeEquiv e he hi hx) z) 0 + e x 0 ↔ _
  rw [h0, add_zero]
  exact coordinateFrame_positive _ z

/-- Normalized local physical parametrizations exist at every boundary point
of a domain with smooth open boundary charts. No regularity is imposed on the
Lamé moduli here. -/
theorem SourceSmoothBoundary.normalized {Ω : Set X} (h : SourceSmoothBoundary Ω)
    {x : X} (hx : x ∈ frontier Ω) :
    ∃ (φ : OpenPartialHomeomorph X X) (Q : X ≃ₗᵢ[ℝ] X),
      (0 : X) ∈ φ.source ∧ φ 0 = x ∧
      ContDiffOn ℝ (⊤ : ℕ∞) φ φ.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) φ.symm φ.target ∧
      HasFDerivAt φ Q.toContinuousLinearEquiv.toContinuousLinearMap 0 ∧
      ∀ z ∈ φ.source, φ z ∈ Ω ↔ 0 < z 2 := by
  obtain ⟨e, hxs, he, hi, h0, hΩ⟩ := h x hx
  exact ⟨normalizedParam e he hi hxs, coordinateFrame (chartDerivativeEquiv e he hi hxs),
    normalizedParam_zero_source e he hi hxs, normalizedParam_zero e he hi hxs,
    normalizedParam_contDiff e he hi hxs, normalizedParam_symm_contDiff e he hi hxs,
    normalizedParam_fderiv e he hi hxs,
    fun _ hz => normalizedParam_halfspace e he hi hxs h0 hΩ hz⟩

end Elasticity

end
end
section
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def basis (i : I) : X := EuclideanSpace.single i 1

def chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) : SmoothTensor :=
  fun s α r β y => principalPull basis
    (mixedTensor (fun s i => frameMatrix Q i s) (frameMatrix Q) (coeff l m)) ψ s α r β (Φ y)

def chartLower (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) : SmoothLower :=
  fun s r β y => lowerPull basis
    (mixedTensor (fun s i => frameMatrix Q i s) (frameMatrix Q) (coeff l m))
    (mixedLower (fun s i => frameMatrix Q i s) (frameMatrix Q) (lower basis l m)) ψ s r β (Φ y)

lemma smooth_jac {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) := by
  exact contDiff_apply ℝ ℝ α |>.comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma smooth_hess {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v w : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (hess ψ v w α) := by
  exact ((smooth_jac hψ w α).fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s α r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartPrincipal Q Φ ψ l m s α r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.sum; intro k _
  apply ContDiff.sum; intro v _
  apply ContDiff.mul
  · apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis k) α)
  · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

lemma smooth_chartLower (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartLower Q Φ ψ l m s r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.add
  · apply ContDiff.sum; intro k _
    apply ContDiff.sum; intro v _
    apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_hess hψ (basis k) (basis v) β)
  · apply ContDiff.sum; intro v _
    apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold lower
      exact (((smooth_dd hl _).mul contDiff_const).add
        ((smooth_dd hm _).mul contDiff_const)).add ((smooth_dd hm _).mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

lemma chartPrincipal_frozen (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) (hj : ∀ k α, (jac ψ (basis k) α (Φ 0):ℂ)=frameMatrix Q k α)
    (s α r β : I) :
    chartPrincipal Q Φ ψ l m s α r β 0=elasticityTensor (l (Φ 0)) (m (Φ 0)) s α r β := by
  have he : chartPrincipal Q Φ ψ l m s α r β 0=
      rotateTensor (frameMatrix Q) (elasticityTensor (l (Φ 0)) (m (Φ 0))) s α r β := by
    unfold chartPrincipal principalPull mixedTensor coeff rotateTensor
    simp only [hj, Finset.sum_mul]
    calc
      _ = ∑ k, ∑ i, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := by
        apply Finset.sum_congr rfl; intro k _
        exact Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro v _
        ring
  rw [he,rotate_isotropic]

/-- Exact equality with the true physical stress divergence after pullback.
The inverse chart equality is used literally, not replaced by a formal symbol. -/
theorem physical_chart_operator (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) {ψ : X → Y}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (y : Y) (hy : ψ (Φ y)=y) (s : I) :
    (∑ i, frameMatrix Q i s*(∑ k, dd
      (stress basis l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i k) (basis k) (Φ y)))=
      strong (chartPrincipal Q Φ ψ l m) (chartLower Q Φ ψ l m) u s y := by
  have hS (i : I) := stress_divergence basis hl hm
    (mix (frameMatrix Q) (fun j x => u j (ψ x)))
    (smooth_mix _ _ (fun j => (hu j).comp hψ)) i (Φ y)
  simp_rw [hS]
  refine (directional_mix basis (fun s i => frameMatrix Q i s) (frameMatrix Q)
    (coeff l m) (lower basis l m) (fun j => u j ∘ ψ) (fun j => (hu j).comp hψ) s (Φ y)).trans ?_
  refine (directional_comp basis _ _ hψ u hu s (Φ y)).trans ?_
  rw [hy]
  rfl

end ElasticityBoundaryChartOperator

end
end
section
/-! Smooth compact extensions of genuine local maps, in arbitrary finite
 dimensional physical and coordinate spaces. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
lemma contDiff_cutoff_smul {U : Set E} (hU : IsOpen U) (f : E → F) (χ : E → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ⊆U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈U
  · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
  · have hn : x∉tsupport χ := fun hh => hx (hs hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

/-- The output may itself be an actual chart or vector displacement. -/
theorem smooth_vector_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (f : E → F) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => χ x • f x,contDiff_cutoff_smul hU f χ hf hχ hs,?_,?_⟩
  · exact hc.smul_right
  · filter_upwards [h1] with x hx
    simp [hx]

end ElasticityBoundary

end
end
section
/-! Transferring a trial supported in an honest chart produces an actual
 globally smooth compact physical field, without imposing artificial boundary
 data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def chartTransfer (e : OpenPartialHomeomorph E E) (η : E → ℝ) (u : E → F) (x : E) : F :=
  η x • u (e.symm x)

omit [FiniteDimensional ℝ E] in
lemma smooth_chartTransfer (e : OpenPartialHomeomorph E E)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : tsupport η⊆e.target)
    {u : E → F} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (chartTransfer e η u) := by
  apply contDiff_cutoff_smul e.open_target _ η _ hη hs
  exact hu.comp_contDiffOn hi

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_apply (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {y : E} (hy : y∈e.source) :
    chartTransfer e η u (e y)=u y := by
  unfold chartTransfer
  rw [e.left_inv hy]
  by_cases h : u y=0
  · simp [h]
  · rw [hη _ (mem_image_of_mem e (hu h)),one_smul]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_zero (e : OpenPartialHomeomorph E E) {η : E → ℝ}
    (hs : tsupport η⊆e.target) (u : E → F) {x : E} (hx : x∉e.target) :
    chartTransfer e η u x=0 := by
  have hn : x∉tsupport η := fun h => hx (hs h)
  simp [chartTransfer, image_eq_zero_of_notMem_tsupport hn]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma compact_chartTransfer (e : OpenPartialHomeomorph E E) {η : E → ℝ}
    (hc : HasCompactSupport η) (u : E → F) : HasCompactSupport (chartTransfer e η u) := by
  exact hc.smul_right

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_support (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hs : tsupport η⊆e.target)
    {u : E → F} (hu : Function.support u⊆K) :
    Function.support (chartTransfer e η u)⊆e '' K := by
  intro x hx
  have ht : x∈e.target := by
    by_contra hn
    exact hx (chartTransfer_zero e hs u hn)
  have hn : u (e.symm x)≠0 := by
    intro hz
    exact hx (by simp [chartTransfer,hz])
  exact ⟨e.symm x,hu hn,e.right_inv ht⟩

/-- Cutoffs and both globally smooth chart extensions exist from honest source
 hypotheses. The extensions agree near the whole compact supports used in the
 physical change of variables. -/
theorem compact_chart_data (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hs : K⊆e.source) :
    ∃ (η : E → ℝ) (Φ Ψ : E → E),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η⊆e.target ∧
      η =ᶠ[𝓝ˢ (e '' K)] (fun _ => 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ Φ =ᶠ[𝓝ˢ K] e ∧
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ Ψ =ᶠ[𝓝ˢ (tsupport η)] e.symm := by
  have hKe : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hs)
  have hst : e '' K⊆e.target := by
    rintro x ⟨y,hy,rfl⟩
    exact e.map_source (hs hy)
  obtain ⟨η,hη,hc,hηs,hη1,_⟩ := compact_smooth_cutoff hKe e.open_target hst
  obtain ⟨Φ,hΦ,_,hΦe⟩ := smooth_vector_extension hK e.open_source hs e he
  obtain ⟨Ψ,hΨ,_,hΨe⟩ := smooth_vector_extension hc e.open_target hηs e.symm hi
  exact ⟨η,Φ,Ψ,hη,hc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩

end ElasticityBoundary

end
end
section
/-! Locality and true support control for the physical differential operator
and the compact chart transfer. These use germs, not formal coefficients. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryOperatorLocal
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryPhysicalStrong
  ElasticityBoundary
abbrev I := Fin 3
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dd_germ {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v =ᶠ[𝓝 x] dd g v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun A : E →L[ℝ] ℂ => A v) hy

lemma dd_germ_eq {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v x=dd g v x := (dd_germ h v).eq_of_nhds

lemma directional_germ_eq (e : I → E) (a : Tensor E) (b : Lower E)
    {u v : I → E → ℂ} {x : E} (h : ∀ j, u j =ᶠ[𝓝 x] v j) (i : I) :
    directional e a b u i x=directional e a b v i x := by
  unfold directional
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (dd_germ (h j) (e l)) (e k)]
  · apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (h j) (e l)]

lemma directional_zero (e : I → E) (a : Tensor E) (b : Lower E) (i : I) (x : E) :
    directional e a b (fun _ _ => 0) i x=0 := by
  have hz (v : E) : dd (fun _ : E => (0:ℂ)) v=(fun _ => 0) := by
    funext y
    simp [dd]
  simp only [directional,hz,mul_zero,Finset.sum_const_zero,add_zero]

lemma directional_support (e : I → E) (a : Tensor E) (b : Lower E)
    {K : Set E} (hK : IsClosed K) (u : I → E → ℂ)
    (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (directional e a b u i)⊆K := by
  intro x hx
  by_contra hn
  have hg (j : I) : u j =ᶠ[𝓝 x] (fun _ => 0) := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun h => hn (closure_minimal (hu j) hK h)
  have heq := directional_germ_eq e a b hg i
  rw [directional_zero] at heq
  exact hx heq

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
lemma chartTransfer_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (e.symm z)) := by
  filter_upwards [e.open_target.mem_nhds hx] with z hz
  have h := chartTransfer_apply e hη hu (e.map_target hz)
  simpa only [e.right_inv hz] using h

omit [NormedSpace ℝ E] in
lemma chartTransfer_extension_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target)
    {Ψ : E → E} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (Ψ z)) := by
  filter_upwards [chartTransfer_germ e hη hu hx,hΨ] with z hz hΨz
  rw [hz,hΨz]

end ElasticityBoundaryOperatorLocal

end
end

end OAI
