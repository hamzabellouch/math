import OAI.MathematicalPhysics.Elasticity.Variational
import OAI.MathematicalPhysics.Elasticity.BoundaryParametrix

namespace OAI

section
/-! The exact inverse derivative at normalized physical boundary charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryInverseGeometry
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma inverse_derivative (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x) :
    HasFDerivAt e.symm Q.symm.toContinuousLinearEquiv.toContinuousLinearMap (e x) := by
  have hd := (hi.differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hinv := chart_fderiv_left_inverse e he hi hx
  rw [hQ.fderiv] at hinv
  have hf : fderiv ℝ e.symm (e x)=Q.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : X →L[ℝ] X => A (Q.symm v)) hinv
    change fderiv ℝ e.symm (e x) (Q (Q.symm v))=Q.symm v at h
    change fderiv ℝ e.symm (e x) v=Q.symm v
    simpa only [Q.apply_symm_apply] using h
  rw [← hf]
  exact hd.hasFDerivAt

lemma inverse_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (k α : I) :
    Q.symm (EuclideanSpace.single k 1) α=Q (EuclideanSpace.single α 1) k := by
  have h := Q.inner_map_eq_flip (EuclideanSpace.single α 1) (EuclideanSpace.single k 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul, mul_one, starRingEnd_apply, star_trivial] using h.symm

lemma coordinate_inverse_jac (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 (e x)] e.symm) (k α : I) :
    (jac (fun z => (Ψ z).ofLp) (EuclideanSpace.single k 1) α (e x):ℂ)=frameMatrix Q k α := by
  have hder := (inverse_derivative e he hi hx Q hQ).congr_of_eventuallyEq hΨ
  have hcoords := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).hasFDerivAt.comp (e x) hder
  change ((fderiv ℝ (fun z => (Ψ z).ofLp) (e x) (EuclideanSpace.single k 1)) α:ℂ)=_
  change HasFDerivAt (fun z => (Ψ z).ofLp) _ (e x) at hcoords
  rw [hcoords.fderiv]
  change (Q.symm (EuclideanSpace.single k 1) α:ℂ)=_
  rw [inverse_frame_entry]
  rfl

end ElasticityBoundaryInverseGeometry

end
end
section
/-! Exact inversion of the fixed physical orthogonal frame, including
quantitative component control needed for the genuine residual norm. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameInverse
open ElasticityBoundaryRotation ElasticityBoundaryInverseGeometry ElasticityBoundaryFrameOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

lemma frameMatrix_symm (Q : X ≃ₗᵢ[ℝ] X) (i j : I) :
    frameMatrix Q.symm i j=frameMatrix Q j i := by
  exact congrArg Complex.ofReal (inverse_frame_entry Q j i)

lemma frameMatrix_rows (Q : X ≃ₗᵢ[ℝ] X) (i j : I) :
    (∑ s, frameMatrix Q i s*frameMatrix Q j s)=if i=j then 1 else 0 := by
  simpa only [frameMatrix_symm] using frameMatrix_orthogonal Q.symm i j

lemma frame_inverse (Q : X ≃ₗᵢ[ℝ] X) (v : I → ℂ) (i : I) :
    (∑ s, frameMatrix Q i s*(∑ j, frameMatrix Q j s*v j))=v i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,frameMatrix_rows]
  simp

lemma norm_sq_sum_three (v : I → ℂ) : ‖∑ i, v i‖^2 ≤ 3*∑ i, ‖v i‖^2 := by
  have h := norm_sum_le Finset.univ v
  have h0 : 0≤∑ i, ‖v i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs : (∑ i, ‖v i‖)^2≤3*∑ i, ‖v i‖^2 := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),sq_nonneg (‖v 1‖-‖v 2‖)]
  exact (sq_le_sq₀ (norm_nonneg _) h0 |>.mpr h).trans hs

lemma norm_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (i j : I) : ‖frameMatrix Q i j‖≤1 := by
  have h := PiLp.norm_apply_le (p := (2:ENNReal)) (Q (EuclideanSpace.single j 1)) i
  simpa only [frameMatrix,Complex.norm_real,Q.norm_map,EuclideanSpace.single,PiLp.norm_single,Real.norm_eq_abs,abs_one] using h

lemma physical_component_bound (Q : X ≃ₗᵢ[ℝ] X) (v : I → ℂ) (i : I) :
    ‖v i‖^2≤3*∑ s, ‖∑ j, frameMatrix Q j s*v j‖^2 := by
  conv_lhs => rw [← frame_inverse Q v i]
  apply (norm_sq_sum_three _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro s _
  rw [norm_mul,mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_frame_entry Q i s))

end ElasticityBoundaryFrameInverse

end
end
section
/-! Support-complete physical force identification. The coordinate expression
is valid on the entire chart source, including all zero regions, and the
physical force is supported in the genuine compact image. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryForceSupport
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal
  ElasticityBoundaryLocalParametrix ElasticityBoundaryStrongLayer
  ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryFrameInverse ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma compact_image (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) : IsCompact (e '' K) :=
  hK.image_of_continuousOn (e.continuousOn.mono hs)

lemma force_support (l m : X → ℂ) (u : I → X → ℂ) {K : Set X}
    (hK : IsClosed K) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (force l m u i)⊆K :=
  directional_support basis _ _ hK u hu i

lemma transferred_force_support (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hη : tsupport η⊆e.target)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (l m : X → ℂ) (i : I) :
    Function.support (force l m (transferred e η Q u) i)⊆e '' K :=
  force_support l m _ (compact_image e hK hs).isClosed (support_transferred e hη Q u hu) i

lemma strong_support_lifted (a : ElasticityBoundarySmoothOperator.SmoothTensor)
    (b : ElasticityBoundarySmoothOperator.SmoothLower) {K : Set X} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (fun z : X => strong a b u i z.ofLp)⊆K := by
  intro x hx
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} := hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hh : ∀ j, Function.support (u j)⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro j y hy
    exact hu j hy
  exact strong_support a b hcl u hh i hx

/-- No operator identity is required outside the actual support: locality
proves both sides vanish there. -/
theorem transferred_force_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (x : X) (hx : x∈e.source) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e x))=
      strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp := by
  by_cases hxK : x∈K
  · exact transferred_force e hs hη Q u hus hu Φ Ψ hΨ hl hm x.ofLp hxK
      (hΦ x hxK) (hΨe _ (mem_image_of_mem e hxK)) s
  · have hn : e x∉e '' K := by
      rintro ⟨y,hy,he⟩
      exact hxK (e.injOn (hs hy) hx he ▸ hy)
    have hz (i : I) : force l m (transferred e η Q u) i (e x)=0 :=
      Function.notMem_support.mp (fun h => hn (transferred_force_support e hK hs hηs Q u hus l m i h))
    have hr : strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s x.ofLp=0 :=
      Function.notMem_support.mp (fun h => hxK (strong_support_lifted _ _ hK.isClosed u hus s h))
    simp only [hz,mul_zero,Finset.sum_const_zero,hr]

end ElasticityBoundaryForceSupport

end
end
section
/-! Honest physical boundary change of variables. The Jacobian is not
normalized away: it is retained exactly and bounded only on the actual
compact trial support. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ElasticityBoundaryChartIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A compactly supported physical integrand pulls back with its exact
Jacobian, including the domain's half-space indicator. -/
theorem compact_chart_integral (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set E} (hs : K⊆e.source) (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : E → E} (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (f g : E → ℝ) (hf : Function.support f⊆e '' K) (hg : Function.support g⊆K)
    (hfg : ∀ y∈e.source, f (e y)=g y) :
    (∫ x in Ω, f x ∂μ)=(∫ y in H, |(fderiv ℝ Φ y).det| *g y ∂μ) := by
  have hd (y : E) (hy : y∈e.source) : HasFDerivAt e (fderiv ℝ e y) y :=
    ((he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hy)).hasFDerivAt
  rw [← integral_indicator hΩ]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) (f := Ω.indicator f)
    (fun x hx => by
      have hh : f x=0 := by
        by_contra hn
        obtain ⟨y,hy,rfl⟩ := hf hn
        exact hx (e.map_source (hs hy))
      simp only [indicator,hh,ite_self])]
  rw [integral_target_eq_integral_abs_det_fderiv_smul μ hd]
  have heq : (∫ y in e.source, |(fderiv ℝ e y).det| • Ω.indicator f (e y) ∂μ)=
      ∫ y in e.source, H.indicator (fun z => |(fderiv ℝ Φ z).det| *g z) y ∂μ := by
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro y hy
    dsimp only
    by_cases hyK : y∈K
    · rw [← (hΦ y hyK).fderiv_eq]
      by_cases hyH : y∈H
      · rw [indicator_of_mem ((hhalf y hy).mpr hyH),indicator_of_mem hyH,hfg y hy]
        rfl
      · rw [indicator_of_notMem (fun h => hyH ((hhalf y hy).mp h)),indicator_of_notMem hyH,smul_zero]
    · have hz : g y=0 := Function.notMem_support.mp (fun h => hyK (hg h))
      simp only [indicator, hfg y hy]
      simp only [hz,mul_zero,smul_eq_mul,ite_self]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_indicator hH
  · intro y hy
    have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs (hg h)))
    simp only [indicator,hz,mul_zero,ite_self]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_abs_det_bound {K : Set E} (hK : IsCompact K) {Φ : E → E}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ y∈K, |(fderiv ℝ Φ y).det|≤C := by
  have hc : Continuous (fun y => |(fderiv ℝ Φ y).det|) := by
    exact (ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv (by simp))).abs
  obtain ⟨C,hC⟩ := (hK.image hc).bddAbove
  exact ⟨max C 0,le_max_right _ _,fun y hy => (hC (mem_image_of_mem _ hy)).trans (le_max_left _ _)⟩

omit [FiniteDimensional ℝ E] in
/-- The physical mass bound used for actual localized stress residuals. -/
theorem compact_jacobian_mass_bound {K H : Set E} (hK : IsCompact K)
    {Φ : E → E} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ g : E → ℝ, Continuous g → HasCompactSupport g →
      Function.support g⊆K → (∀ y, 0≤g y) →
      (∫ y in H, |(fderiv ℝ Φ y).det| *g y ∂μ)≤C*(∫ y in H, g y ∂μ) := by
  obtain ⟨C,hC,hb⟩ := compact_abs_det_bound hK hΦ
  refine ⟨C,hC,fun g hg hc hs hn => ?_⟩
  have hdet : Continuous (fun y => |(fderiv ℝ Φ y).det|) :=
    (ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv (by simp))).abs
  have hInt : Integrable (fun y => |(fderiv ℝ Φ y).det| *g y) μ :=
    (hdet.mul hg).integrable_of_hasCompactSupport hc.mul_left
  rw [← integral_const_mul]
  apply integral_mono hInt.integrableOn ((hg.integrable_of_hasCompactSupport hc).const_mul C).integrableOn
  intro y
  by_cases hy : y∈K
  · exact mul_le_mul_of_nonneg_right (hb y hy) (hn y)
  · have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs h))
    simp only [hz,mul_zero,le_refl]

end ElasticityBoundaryChartIntegral

end
end
section
/-! A quantitative physical L2 transfer through an honest boundary chart.
The constants are independent of trial fields and concentration parameters. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryChartMass
open ElasticityBoundaryChartIntegral ElasticityBoundaryFrameInverse
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def inverseMix (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) (i : I) (y : X) : ℂ :=
  ∑ j, frameMatrix Q i j*g j y

lemma inverseMix_support (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) {K : Set X}
    (hg : ∀ j, Function.support (g j)⊆K) (i : I) :
    Function.support (inverseMix Q g i)⊆K := by
  intro y hy
  by_contra hn
  apply hy
  apply Finset.sum_eq_zero
  intro j _
  have hz : g j y=0 := Function.notMem_support.mp (fun h => hn (hg j h))
  rw [hz,mul_zero]

lemma inverseMix_bound (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) (i : I) (y : X) :
    ‖inverseMix Q g i y‖^2≤3*∑ j, ‖g j y‖^2 := by
  apply (norm_sq_sum_three _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_frame_entry Q i j))

lemma norm_sq_integrableOn {g : X → ℂ} {K : Set X} (hK : IsCompact K)
    (hg : Continuous g) (hs : Function.support g⊆K) (H : Set X) :
    IntegrableOn (fun y => ‖g y‖^2) H := by
  have hc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs hK.isClosed)
  have hc' : HasCompactSupport (fun y => ‖g y‖^2) :=
    hc.norm.comp_left (g := fun r : ℝ => r^2) (by norm_num)
  exact ((hg.norm.pow 2).integrable_of_hasCompactSupport hc').integrableOn

/-- Uniform transfer of the exact strong residual. There is no assumed
physical/augmented DN equality and no suppressed determinant. -/
theorem chart_frame_mass_bound (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : X → X} (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (Q : X ≃ₗᵢ[ℝ] X) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f g : I → X → ℂ),
      (∀ i, Function.support (f i)⊆e '' K) →
      (∀ j, Continuous (g j)) → (∀ j, Function.support (g j)⊆K) →
      (∀ y∈e.source, ∀ s, (∑ i, frameMatrix Q i s*f i (e y))=g s y) →
      ∀ i, (∫ x in Ω, ‖f i x‖^2)≤C*∑ s, (∫ y in H, ‖g s y‖^2) := by
  obtain ⟨C,hC,hb⟩ := compact_jacobian_mass_bound (volume : Measure X) (H := H) hK hΦs
  refine ⟨C*3,mul_nonneg hC (by norm_num),fun f g hfs hgc hgs hfg i => ?_⟩
  have hscale : ∀ y∈e.source, f i (e y)=inverseMix Q g i y := by
    intro y hy
    rw [← frame_inverse Q (fun j => f j (e y)) i]
    simp only [inverseMix, hfg y hy]
  have hcont : Continuous (inverseMix Q g i) :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (hgc j))
  have hsup : Function.support (fun y => ‖inverseMix Q g i y‖^2)⊆K := by
    intro y hy
    apply inverseMix_support Q g hgs i
    intro hz
    exact hy (by simp [hz])
  have hcc : HasCompactSupport (fun y => ‖inverseMix Q g i y‖^2) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsup hK.isClosed)
  have hfsq : Function.support (fun x => ‖f i x‖^2)⊆e '' K := by
    intro x hx
    apply hfs i
    intro hz
    exact hx (by simp [hz])
  rw [compact_chart_integral (volume : Measure X) e he hs hΩ hH hhalf hΦ
    (fun x => ‖f i x‖^2) (fun y => ‖inverseMix Q g i y‖^2) hfsq hsup
    (fun y hy => congrArg (fun z : ℂ => ‖z‖^2) (hscale y hy))]
  apply (hb _ (hcont.norm.pow 2) hcc hsup (fun _ => sq_nonneg _)).trans
  have hgi (j : I) : IntegrableOn (fun y => ‖g j y‖^2) H :=
    norm_sq_integrableOn hK (hgc j) (hgs j) H
  have hsum : (∫ y in H, ‖inverseMix Q g i y‖^2)≤3*∑ j, (∫ y in H, ‖g j y‖^2) := by
    rw [← integral_finsetSum _ (fun j _ => hgi j),← integral_const_mul]
    exact integral_mono ((hcont.norm.pow 2).integrable_of_hasCompactSupport hcc).integrableOn
      ((integrable_finsetSum _ (fun j _ => hgi j)).const_mul 3) (inverseMix_bound Q g i)
  calc
    _ ≤ C*(3*∑ j, (∫ y in H, ‖g j y‖^2)) := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring

/-- The coordinate product measure is the actual Euclidean volume, not a
normalization chosen during the argument. -/
lemma integral_ofLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Y → F) (H : Set Y) :
    (∫ x : X in (WithLp.ofLp ⁻¹' H), g x.ofLp)=(∫ y in H, g y) :=
  (PiLp.volume_preserving_ofLp I).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 Y).symm.measurableEmbedding g H

end ElasticityBoundaryChartMass

end
end
section
/-! The honest physical strong residual has the same quantitative L2 scale as
its fully curved coordinate expression. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalMass
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryRotation
  ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer ElasticityBoundaryCutoffLayer
  ElasticityBoundaryFrameOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma smooth_strong (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (strong a b u i) := by
  exact (ContDiff.sum (fun α _ => ContDiff.sum (fun j _ => ContDiff.sum (fun β _ =>
    (ha i α j β).mul (smooth_dpart (smooth_dpart (hu j) β) α))))).add
    (ContDiff.sum (fun j _ => ContDiff.sum (fun β _ => (hb i j β).mul (smooth_dpart (hu j) β))))

def principal (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ) : SmoothTensor :=
  chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m

def lower (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ) : SmoothLower :=
  chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m

/-- The multiplicative constant depends only on the fixed chart, not on the
field, its frequency, or the chosen finite parametrix order. -/
theorem transferred_mass_bound (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    :
    ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
      (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
      ∀ i, (∫ x in Ω, ‖force l m (transferred e η Q u) i x‖^2)≤
        C*∑ s, (∫ y in H, ‖strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp‖^2) := by
  have ha := smooth_chartPrincipal Q (hΦs.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp hΨs) hl hm
  have hb := smooth_chartLower Q (hΦs.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp hΨs) hl hm
  obtain ⟨C,hC,hbound⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  refine ⟨C,hC,fun u hu hus i => ?_⟩
  apply hbound (force l m (transferred e η Q u))
    (fun s y => strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp)
  · exact transferred_force_support e hK hs hηs Q u hus l m
  · exact fun s => ((smooth_strong _ _ ha hb u hu s).comp PiLp.contDiff_ofLp).continuous
  · exact strong_support_lifted _ _ hK.isClosed u hus
  · intro y hy s
    exact transferred_force_all e hK hs hηs hη Q u hus hu Φ Ψ hΨs
      (fun x hx => (hΦ x hx).eq_of_nhds) hΨ hl hm y hy s

end ElasticityBoundaryPhysicalMass

end
end
section
/-! Uniform compactly supported matrix-multiplier mass estimates, for the
true coordinate Jacobian acting on first derivatives of boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryCompactMatrix
open ElasticityBoundaryChartMass ElasticityBoundaryFrameInverse
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

lemma compact_array_bound {K : Set X} (hK : IsCompact K) (a : I → I → X → ℂ)
    (ha : ∀ r j, Continuous (a r j)) :
    ∃ B : ℝ, 0≤B ∧ ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B := by
  have hc : Continuous (fun y => ∑ r, ∑ j, ‖a r j y‖^2) :=
    continuous_finsetSum _ (fun r _ => continuous_finsetSum _ (fun j _ => (ha r j).norm.pow 2))
  obtain ⟨B,hB⟩ := (hK.image hc).bddAbove
  refine ⟨max B 0,le_max_right _ _,fun y hy r j => ?_⟩
  have h1 : ‖a r j y‖^2≤∑ k, ‖a r k y‖^2 :=
    Finset.single_le_sum (f := fun k => ‖a r k y‖^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ k, ‖a r k y‖^2)≤∑ s, ∑ k, ‖a s k y‖^2 :=
    Finset.single_le_sum (f := fun s => ∑ k, ‖a s k y‖^2) (fun s _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ r)
  exact h1.trans (h2.trans ((hB (mem_image_of_mem _ hy)).trans (le_max_left _ _)))

def row (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) (y : X) : ℂ := ∑ j, a r j y*v j y

lemma row_support (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) {K : Set X}
    (hv : ∀ j, Function.support (v j)⊆K) : Function.support (row a r v)⊆K := by
  intro y hy
  by_contra hn
  apply hy
  apply Finset.sum_eq_zero
  intro j _
  have hz : v j y=0 := Function.notMem_support.mp (fun h => hn (hv j h))
  rw [hz,mul_zero]

lemma continuous_row (a : I → I → X → ℂ) (ha : ∀ r j, Continuous (a r j))
    (r : I) (v : I → X → ℂ) (hv : ∀ j, Continuous (v j)) : Continuous (row a r v) :=
  continuous_finsetSum _ (fun j _ => (ha r j).mul (hv j))

lemma row_bound (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) {K : Set X}
    (hv : ∀ j, Function.support (v j)⊆K) {B : ℝ}
    (hb : ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B) (y : X) :
    ‖row a r v y‖^2≤3*B*∑ j, ‖v j y‖^2 := by
  by_cases hy : y∈K
  · apply (norm_sq_sum_three _).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (hb y hy r j) (sq_nonneg _)
  · have hz (j : I) : v j y=0 := Function.notMem_support.mp (fun h => hy (hv j h))
    simp only [row,hz,mul_zero,Finset.sum_const_zero,norm_zero,zero_pow (by omega : 2≠0),le_refl]

lemma row_mass_bound {K H : Set X} (hK : IsCompact K) (a : I → I → X → ℂ)
    (ha : ∀ r j, Continuous (a r j)) {B : ℝ}
    (hb : ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B)
    (r : I) (v : I → X → ℂ) (hvc : ∀ j, Continuous (v j))
    (hvs : ∀ j, Function.support (v j)⊆K) :
    (∫ y in H, ‖row a r v y‖^2)≤3*B*∑ j, (∫ y in H, ‖v j y‖^2) := by
  have hi (j : I) := norm_sq_integrableOn hK (hvc j) (hvs j) H
  rw [← integral_finsetSum _ (fun j _ => hi j),← integral_const_mul]
  exact integral_mono (norm_sq_integrableOn hK (continuous_row a ha r v hvc) (row_support a r v hvs) H)
    ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _) (row_bound a r v hvs hb)

end ElasticityBoundaryCompactMatrix

end
end
section
/-! Literal first derivatives of the compact physical trial and their exact
rotated chart expression. No trace reconstruction is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientTransfer
open ElasticityBoundaryPhysicalMass ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryRotation ElasticityBoundaryFrameInverse ElasticityBoundaryOperatorLocal
  ElasticityBoundaryChainRule ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma frame_forward (Q : X ≃ₗᵢ[ℝ] X) (v : I → ℂ) (s : I) :
    (∑ i, frameMatrix Q i s*(∑ j, frameMatrix Q i j*v j))=v s := by
  simpa only [frameMatrix_symm] using frame_inverse Q.symm v s

lemma dd_support {f : X → ℂ} {K : Set X} (hK : IsClosed K)
    (hf : Function.support f⊆K) (v : X) : Function.support (dd f v)⊆K := by
  intro x hx
  apply closure_minimal hf hK
  exact tsupport_fderiv_apply_subset ℝ v (subset_tsupport _ hx)

lemma dpart_support_lifted {f : Y → ℂ} {K : Set X} (hK : IsClosed K)
    (hf : Function.support (fun z : X => f z.ofLp)⊆K) (α : I) :
    Function.support (fun z : X => dpart f α z.ofLp)⊆K := by
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} :=
    hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hs : Function.support f⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro y hy
    exact hf hy
  intro x hx
  exact closure_minimal hs hcl (tsupport_fderiv_apply_subset ℝ (Pi.single α 1) (subset_tsupport _ hx))

def jacobian (Φ Ψ : X → X) (d α : I) (y : X) : ℂ :=
  (jac (fun z => (Ψ z).ofLp) (basis d) α (Φ y):ℂ)

lemma smooth_jacobian {Φ Ψ : X → X} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (d α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jacobian Φ Ψ d α) :=
  Complex.ofRealCLM.contDiff.comp ((ElasticityBoundaryChainRule.smooth_jac
    (PiLp.contDiff_ofLp.comp hΨ) (basis d) α).comp hΦ)

lemma gradient_at_support (e : OpenPartialHomeomorph X X) {K : Set X} (hs : K⊆e.source)
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {y : X} (hy : y∈K) (hΦy : Φ y=e y) (hΨy : Ψ =ᶠ[𝓝 (e y)] e.symm) (s d : I) :
    (∑ i, frameMatrix Q i s*dd (transferred e η Q u i) (basis d) (e y))=
      row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y := by
  have he (i : I) : dd (transferred e η Q u i) (basis d) (e y)=
      ∑ j, frameMatrix Q i j*row (jacobian Φ Ψ) d (fun α z => dpart (u j) α z.ofLp) y := by
    rw [dd_germ_eq (transferred_germ e hη Q u hus (e.map_source (hs hy)) hΨy i)]
    have hum (j : I) : ContDiff ℝ (⊤ : ℕ∞) (fun z => u j (Ψ z).ofLp) :=
      (hu j).comp (PiLp.contDiff_ofLp.comp hΨ)
    rw [dd_mix (frameMatrix Q) _ hum]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun z => frameMatrix Q i j*z)
    have hps : Differentiable ℝ (fun z => (Ψ z).ofLp) :=
      (PiLp.contDiff_ofLp.comp hΨ).differentiable (by simp)
    rw [dd_comp ((hu j).differentiable (by simp)) hps]
    have hid : (Ψ (e y)).ofLp=y.ofLp := by rw [hΨy.eq_of_nhds,e.left_inv (hs hy)]
    simp only [hid,row,jacobian,hΦy]
    rfl
  simp only [he,frame_forward]

lemma gradient_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {y : X} (hy : y∈e.source) (s d : I) :
    (∑ i, frameMatrix Q i s*dd (transferred e η Q u i) (basis d) (e y))=
      row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y := by
  by_cases hyK : y∈K
  · exact gradient_at_support e hs hη Q u hu hus Φ Ψ hΨ hyK (hΦ y hyK)
      (hΨe _ (mem_image_of_mem e hyK)) s d
  · have hn : e y∉e '' K := by
      rintro ⟨z,hz,he⟩
      exact hyK (e.injOn (hs hz) hy he ▸ hz)
    have hz (i : I) : dd (transferred e η Q u i) (basis d) (e y)=0 :=
      Function.notMem_support.mp (fun h => hn (dd_support (compact_image e hK hs).isClosed
        (support_transferred e hηs Q u hus i) (basis d) h))
    have hr : row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y=0 :=
      Function.notMem_support.mp (fun h => hyK (row_support _ _ _
        (fun α => dpart_support_lifted hK.isClosed (hus s) α) h))
    simp only [hz,mul_zero,Finset.sum_const_zero,hr]

end ElasticityBoundaryGradientTransfer

end
end
section
/-! Uniform physical H1 control through the honest chart. Both the coordinate
Jacobian and the orthogonal output frame are accounted for. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientMass
open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartMass ElasticityBoundaryCompactMatrix ElasticityBoundaryForceSupport
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation ElasticityBoundaryChainRule
  ElasticityBoundaryStrongLayer ElasticityBoundaryChartOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma transferred_value (e : OpenPartialHomeomorph X X) {K : Set X}
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    {y : X} (hy : y∈e.source) (s : I) :
    (∑ i, frameMatrix Q i s*transferred e η Q u i (e y))=u s y.ofLp := by
  have he (i : I) := (transferred_germ e hη Q u hus (e.map_source hy)
    (Filter.EventuallyEq.refl (𝓝 (e y)) e.symm) i).eq_of_nhds
  simp only [ElasticityBoundaryFrameOperator.mix,e.left_inv hy] at he
  simp only [he,frame_forward]

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)

include he hK hs hΩ hH hhalf hηs hη hΦs hΦ in
lemma transferred_value_mass : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
    (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
    ∀ i, (∫ x in Ω, ‖transferred e η Q u i x‖^2)≤
      C*∑ s, (∫ y in H, ‖u s y.ofLp‖^2) := by
  obtain ⟨C,hC,hb⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  refine ⟨C,hC,fun u hu hus i => hb (transferred e η Q u) (fun s y => u s y.ofLp)
    (support_transferred e hηs Q u hus)
    (fun s => ((hu s).comp PiLp.contDiff_ofLp).continuous) hus ?_ i⟩
  exact fun y hy s => transferred_value e hη Q u hus hy s

include he hK hs hΩ hH hhalf hηs hη hΦs hΨs hΦ hΨ in
lemma transferred_gradient_mass : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
    (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
    ∀ i d, (∫ x in Ω, ‖dd (transferred e η Q u i) (basis d) x‖^2)≤
      C*∑ s, ∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2) := by
  obtain ⟨C,hC,hb⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  have hJ (d α : I) := (smooth_jacobian hΦs hΨs d α).continuous
  obtain ⟨B,hB,hbB⟩ := compact_array_bound hK (jacobian Φ Ψ) hJ
  refine ⟨C*(3*B),mul_nonneg hC (mul_nonneg (by norm_num) hB),fun u hu hus i d => ?_⟩
  have hds (s α : I) := dpart_support_lifted hK.isClosed (hus s) α
  have hdc (s α : I) : Continuous (fun y : X => dpart (u s) α y.ofLp) :=
    ((ElasticityBoundaryCutoffLayer.smooth_dpart (hu s) α).comp PiLp.contDiff_ofLp).continuous
  have h1 := hb (fun i => dd (transferred e η Q u i) (basis d))
    (fun s => row (jacobian Φ Ψ) d (fun α y => dpart (u s) α y.ofLp))
    (fun i => dd_support (compact_image e hK hs).isClosed (support_transferred e hηs Q u hus i) _)
    (fun s => continuous_row _ hJ _ _ (hdc s)) (fun s => row_support _ _ _ (hds s))
    (fun y hy s => gradient_all e hK hs hηs hη Q u hu hus Φ Ψ hΨs
      (fun y hy => (hΦ y hy).eq_of_nhds) hΨ hy s d) i
  apply h1.trans
  calc
    _ ≤ C*∑ s, (3*B*∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ =>
        row_mass_bound hK _ hJ hbB d _ (hdc s) (hds s))) hC
    _ = _ := by rw [← Finset.mul_sum]; ring

end ElasticityBoundaryGradientMass

end
end
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
  ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryLayerOperator ElasticityBoundaryPhysicalTransfer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

structure Setup (Ω : Set X) (x : X) where
  e : OpenPartialHomeomorph X X
  Q : X ≃ₗᵢ[ℝ] X
  at_zero : (0:X)∈e.source
  center : e 0=x
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) e e.source
  inverse_smooth : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target
  deriv : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap 0
  inside : ∀ y∈e.source, e y∈Ω ↔ 0<y 2
  K : Set X
  compact : IsCompact K
  source : K⊆e.source
  cutoff : Y → ℂ
  cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_one : cutoff =ᶠ[𝓝 (0:Y)] fun _ => 1
  cutoff_support : Function.support (fun z : X => cutoff z.ofLp)⊆K
  η : X → ℝ
  η_smooth : ContDiff ℝ (⊤ : ℕ∞) η
  η_compact : HasCompactSupport η
  η_support : tsupport η⊆e.target
  η_one : ∀ z∈e '' K, η z=1
  Φ : X → X
  Ψ : X → X
  Φ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ
  Ψ_smooth : ContDiff ℝ (⊤ : ℕ∞) Ψ
  Φ_germ : ∀ y∈K, Φ =ᶠ[𝓝 y] e
  Ψ_germ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm

lemma setup_exists {Ω : Set X} (h : SourceSmoothBoundary Ω) {x : X} (hx : x∈frontier Ω) :
    Nonempty (Setup Ω x) := by
  obtain ⟨e,Q,he0,hec,he,hi,hQ,hhalf⟩ := h.normalized hx
  obtain ⟨χ,hχ,hχc,hχs,hχ0,_⟩ := compact_smooth_cutoff (isCompact_singleton (x := (0:X)))
    e.open_source (singleton_subset_iff.mpr he0)
  let K := tsupport χ
  obtain ⟨η,Φ,Ψ,hη,hηc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩ := compact_chart_data e he hi hχc hχs
  have hηK : ∀ z∈e '' K, η z=1 := fun z hz => hη1.self_of_nhdsSet hz
  have hKη : e '' K⊆tsupport η := by
    intro z hz
    exact subset_tsupport η (show η z≠0 from by rw [hηK z hz]; exact one_ne_zero)
  let χc : Y → ℂ := fun y => (χ (WithLp.toLp 2 y):ℂ)
  have hχcs : ContDiff ℝ (⊤ : ℕ∞) χc :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp PiLp.contDiff_toLp)
  have hχcc : HasCompactSupport χc :=
    (hχc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hχc0 : χc =ᶠ[𝓝 (0:Y)] fun _ => 1 := by
    have hh : χ =ᶠ[𝓝 (0:X)] fun _ => 1 := by
      change ∀ᶠ z in 𝓝 (0:X), χ z=1
      simpa only [nhdsSet_singleton] using hχ0
    have ht : Tendsto (WithLp.toLp 2 : Y → X) (𝓝 (0:Y)) (𝓝 (0:X)) :=
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt
    filter_upwards [hh.comp_tendsto ht] with y hy
    change χ (WithLp.toLp 2 y)=1 at hy
    simp only [χc,hy,Complex.ofReal_one]
  refine ⟨{
    e := e, Q := Q, at_zero := he0, center := hec, smooth := he,
    inverse_smooth := hi, deriv := hQ, inside := hhalf, K := K, compact := hχc,
    source := hχs, cutoff := χc, cutoff_smooth := hχcs, cutoff_compact := hχcc,
    cutoff_one := hχc0, cutoff_support := ?_, η := η, η_smooth := hη,
    η_compact := hηc, η_support := hηs, η_one := hηK, Φ := Φ, Ψ := Ψ,
    Φ_smooth := hΦ, Ψ_smooth := hΨ, Φ_germ := ?_, Ψ_germ := ?_ }⟩
  · intro z hz
    apply subset_tsupport χ
    intro hc
    exact hz (by simp [χc,hc])
  · intro y hy
    exact hΦe.filter_mono (nhds_le_nhdsSet hy)
  · intro z hz
    exact hΨe.filter_mono (nhds_le_nhdsSet (hKη hz))

lemma Setup.zero_mem {Ω : Set X} {x : X} (s : Setup Ω x) : (0:X)∈s.K := by
  apply s.cutoff_support
  change s.cutoff 0≠0
  rw [s.cutoff_one.eq_of_nhds]
  exact one_ne_zero

lemma Setup.Φ_zero {Ω : Set X} {x : X} (s : Setup Ω x) : s.Φ 0=x :=
  (s.Φ_germ 0 s.zero_mem).eq_of_nhds.trans s.center

lemma Setup.frozen {Ω : Set X} {x : X} (s : Setup Ω x) (l m : X → ℂ)
    (i α j β : I) : principal s.Q s.Φ s.Ψ l m i α j β 0=elasticityTensor (l x) (m x) i α j β := by
  unfold ElasticityBoundaryPhysicalMass.principal
  rw [chartPrincipal_frozen]
  · simp only [WithLp.toLp_zero,s.Φ_zero]
  · intro k a
    simp only [WithLp.toLp_zero]
    rw [(s.Φ_germ 0 s.zero_mem).eq_of_nhds]
    exact coordinate_inverse_jac s.e s.smooth s.inverse_smooth s.at_zero s.Q s.deriv
      (s.Ψ_germ _ (mem_image_of_mem s.e s.zero_mem)) k a

end ElasticityBoundaryPacket

end
end
section
/-! Value mass and the exact identification of Euclidean and product Lebesgue
measure used by the physical boundary packets. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryPacketMass
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryParameterBounds
  ElasticityBoundaryOrderBound ElasticityBoundaryCutoffBound ElasticityBoundaryScaling
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryMVCalculus
  ElasticityBoundaryTensorSeries ElasticityBoundaryProfileBounds ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
abbrev I := Fin 3
abbrev Y := I → ℝ
abbrev X := EuclideanSpace ℝ I

def H : Set X := {y | 0<y 2}
lemma measurable_H : MeasurableSet H :=
  (isOpen_lt (continuous_const : Continuous (fun _ : X => (0:ℝ)))
    (EuclideanSpace.proj 2).continuous).measurableSet

lemma integral_ofLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Y → F) : (∫ x in H, f x.ofLp)=∫ y in halfspace, f y := by
  rw [← integral_indicator measurable_H,← integral_indicator measurable_halfspace]
  have hh (x : X) : H.indicator (fun x => f x.ofLp) x=halfspace.indicator f x.ofLp := rfl
  simp_rw [hh]
  exact (PiLp.volume_preserving_ofLp I).integral_comp
    (PiLp.homeomorph 2 (fun _ : I => ℝ)).measurableEmbedding _

/-- The lower-order value term even decays as delta^4. -/
lemma cutoff_value_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j : I) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      MemLp (cutoffLayer χ q δ j) 2 (volume.restrict halfspace) ∧
      (∫ z in halfspace, ‖cutoffLayer χ q δ j z‖^2)≤C*δ^4 := by
  have hb : OrderBound (fun δ y => χ (scale δ y)*value (atParameter (unpack j q) δ) y) 0 := by
    simpa only [Nat.zero_add] using (compact_scaled hχ.continuous hc).mul (parameter_bound (unpack j q))
  have hcont (δ : ℝ) : Continuous (fun y => χ (scale δ y)*value (atParameter (unpack j q) δ) y) :=
    (hχ.continuous.comp (scale δ).continuous).mul (smooth_value _).continuous
  obtain ⟨C,hC,hI⟩ := hb.square_mass hcont (by norm_num : (0:ℝ)<2)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hB⟩ := hI δ hδ hδ1
  have hid (y : Y) : cutoffLayer χ q δ j (scale δ y)=
      (1:ℝ) • (envelope δ y*(χ (scale δ y)*value (atParameter (unpack j q) δ) y)) := by
    simp only [cutoffLayer,layer,physicalProfile_scale hδ.ne',profile,one_smul]
    ring
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (smooth_cutoffLayer hχ q δ j).continuous.aestronglyMeasurable).mpr
      (scaled_envelope_integrable hδ.ne' _ _ _ hid hInt), ?_⟩
  rw [scaled_envelope_mass hδ.ne' _ _ _ hid]
  simp only [one_pow,mul_one,Nat.mul_zero,pow_zero] at hB ⊢
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hB (pow_nonneg hδ.le 4)

end ElasticityBoundaryPacketMass

end
end
section
/-!
Exact physical-DN remainder identity needed for boundary high-frequency tests.
All objects below use the physical energy and full trace quotient.
There are no additional main hypotheses; the estimates hold for any trial field.
-/
noncomputable section
open Set MeasureTheory
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

/-- The variational residual, acting on all zero-trace test fields. -/
def physicalResidual (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1Hilbert Ω) : H10Hilbert Ω →L[ℝ] ℝ :=
  (jetEnergy hl hm u.val).comp (H10Hilbert Ω).subtypeL

/-- The actual physical solution with the same trace as the trial field. -/
def physicalProjection (u : H1Hilbert Ω) : H1Hilbert Ω :=
  (h1Equiv Ω).symm (dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)))

lemma physicalProjection_weak (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) :
    WeakSolution Ω lam mu (h1Equiv Ω (physicalProjection (lam := lam) (mu := mu) u)) := by
  simpa only [physicalProjection, Equiv.apply_symm_apply] using
    (dirichletSolution_spec ha hO hB (trace Ω (h1Equiv Ω u))).2

lemma physicalProjection_trace (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) :
    trace Ω (h1Equiv Ω (physicalProjection (lam := lam) (mu := mu) u)) =
      trace Ω (h1Equiv Ω u) := by
  simpa only [physicalProjection, Equiv.apply_symm_apply] using
    (dirichletSolution_spec ha hO hB (trace Ω (h1Equiv Ω u))).1

/-- The exact zero-trace correction, not an assumed quasimode remainder. -/
def physicalError (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) : H10Hilbert Ω :=
  ⟨u.val - (physicalProjection (lam := lam) (mu := mu) u).val,
    (sameTrace_h1Equiv u _).mp ((trace_eq_iff _ _).mp
      (physicalProjection_trace ha hO hB u).symm)⟩

lemma error_residual (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (v : H10Hilbert Ω) :
    zeroTraceEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
      (physicalError ha hO hB u) v =
      physicalResidual (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB) u v := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  have hw := (weakSolution_h1Equiv hl hm _).mp (physicalProjection_weak ha hO hB u) v
  change jetEnergy hl hm (u.val - (physicalProjection (lam := lam) (mu := mu) u).val)
    v.val = jetEnergy hl hm u.val v.val
  rw [map_sub, sub_apply, hw, sub_zero]

/-- Coercivity gives a uniform correction bound in the honest Hilbert norm. -/
theorem physicalError_bound (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : H1Hilbert Ω,
      ‖physicalError ha hO hB u‖ ≤
      ‖physicalResidual (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB) u‖ / c := by
  obtain ⟨c, hc, hco⟩ := physical_coercive ha hO hB
  refine ⟨c, hc, ?_⟩
  intro u
  let e := physicalError ha hO hB u
  let r := physicalResidual (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) u
  have h1 : c * ‖e‖ * ‖e‖ ≤ r e := by
    simpa only [e, r, error_residual] using hco e
  have h2 : r e ≤ ‖r‖ * ‖e‖ := (le_abs_self _).trans (r.le_opNorm e)
  by_cases he : ‖e‖ = 0
  · change ‖e‖ ≤ ‖r‖ / c
    rw [he]
    positivity
  · have he' : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg e) (Ne.symm he)
    have hh : c * ‖e‖ ≤ ‖r‖ := (mul_le_mul_iff_left₀ he').mp (h1.trans h2)
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)

/-- Exact error identity for the bilinear full physical DN pairing. -/
theorem DN_quasimode_identity (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) -
      DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      zeroTraceEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
        (physicalError ha hO hB u) (physicalError ha hO hB v) := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let U := physicalProjection (lam := lam) (mu := mu) u
  let V := physicalProjection (lam := lam) (mu := mu) v
  have hw := (weakSolution_h1Equiv hl hm V).mp (physicalProjection_weak ha hO hB v)
    (physicalError ha hO hB u)
  have he : jetEnergy hl hm (u.val - U.val) V.val = 0 := by
    rw [jetEnergy_symm]
    exact hw
  rw [DN_eq_energy ha hO hB]
  have hU : dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)) = h1Equiv Ω U :=
    (Equiv.apply_symm_apply _ _).symm
  rw [hU, ← jetEnergy_eq_energy hl hm u v, ← jetEnergy_eq_energy hl hm U v]
  change jetEnergy hl hm u.val v.val - jetEnergy hl hm U.val v.val =
    jetEnergy hl hm (u.val - U.val) (v.val - V.val)
  have hsub : jetEnergy hl hm (u.val - U.val) v.val =
      jetEnergy hl hm u.val v.val - jetEnergy hl hm U.val v.val := by
    exact congrArg (fun f : JetH Ω →L[ℝ] ℝ => f v.val)
      ((jetEnergy hl hm).map_sub u.val U.val)
  rw [map_sub (jetEnergy hl hm (u.val - U.val)) v.val V.val, he, sub_zero]
  exact hsub.symm

/-- The DN error is quadratic in the dual residual, uniformly over all trials.
This bound loses no derivative and uses no pointwise boundary assumptions. -/
theorem DN_quasimode_bound (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : H1Hilbert Ω,
      |energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) -
        DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v))| ≤
      C * ‖physicalResidual (ha.1.boundedCoefficient hO hB)
        (ha.2.1.boundedCoefficient hO hB) u‖ *
        ‖physicalResidual (ha.1.boundedCoefficient hO hB)
        (ha.2.1.boundedCoefficient hO hB) v‖ := by
  obtain ⟨c, hc, hbound⟩ := physicalError_bound ha hO hB
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro u v
  rw [DN_quasimode_identity ha hO hB, error_residual]
  let r := physicalResidual (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) u
  let s := physicalResidual (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) v
  change |r (physicalError ha hO hB v)| ≤ c⁻¹ * ‖r‖ * ‖s‖
  calc
    |r (physicalError ha hO hB v)| ≤ ‖r‖ * ‖physicalError ha hO hB v‖ :=
      r.le_opNorm _
    _ ≤ ‖r‖ * (‖s‖ / c) := mul_le_mul_of_nonneg_left (hbound v) (norm_nonneg r)
    _ = c⁻¹ * ‖r‖ * ‖s‖ := by ring

/-- An exact quantitative comparison for two actual equal physical DN maps.
The trials may differ, provided their traces agree; the errors are calculated
separately in the two genuine physical systems. -/
theorem equal_DN_quasimode_bound {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁ = DN Ω l₂ m₂) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ u₁ v₁ u₂ v₂ : H1Hilbert Ω,
      trace Ω (h1Equiv Ω u₁) = trace Ω (h1Equiv Ω u₂) →
      trace Ω (h1Equiv Ω v₁) = trace Ω (h1Equiv Ω v₂) →
      |energy Ω l₁ m₁ (h1Equiv Ω u₁) (h1Equiv Ω v₁) -
        energy Ω l₂ m₂ (h1Equiv Ω u₂) (h1Equiv Ω v₂)| ≤
      C₁ * ‖physicalResidual (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) u₁‖ *
        ‖physicalResidual (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) v₁‖ +
      C₂ * ‖physicalResidual (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) u₂‖ *
        ‖physicalResidual (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) v₂‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := DN_quasimode_bound ha₁ hO hB
  obtain ⟨C₂, hC₂, h₂⟩ := DN_quasimode_bound ha₂ hO hB
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro u₁ v₁ u₂ v₂ hu hv
  have he : DN Ω l₁ m₁ (trace Ω (h1Equiv Ω u₁)) (trace Ω (h1Equiv Ω v₁)) =
      DN Ω l₂ m₂ (trace Ω (h1Equiv Ω u₂)) (trace Ω (h1Equiv Ω v₂)) := by
    rw [hDN, hu, hv]
  have hi := abs_sub_le
    (energy Ω l₁ m₁ (h1Equiv Ω u₁) (h1Equiv Ω v₁))
    (DN Ω l₁ m₁ (trace Ω (h1Equiv Ω u₁)) (trace Ω (h1Equiv Ω v₁)))
    (energy Ω l₂ m₂ (h1Equiv Ω u₂) (h1Equiv Ω v₂))
  have hb₂ := h₂ u₂ v₂
  rw [← he, abs_sub_comm] at hb₂
  exact hi.trans (add_le_add (h₁ u₁ v₁) hb₂)

end Elasticity

end
end

end OAI
