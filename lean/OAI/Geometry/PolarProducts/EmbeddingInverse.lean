import OAI.Geometry.PolarProducts.HamiltonianGrowth

namespace OAI

universe u121 u122

section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 def localEquiv {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : OpenPartialHomeomorph E E :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U) hf.continuousOn
    (LocalEmbedding.isOpenEmbedding hU hf hi hD).isOpenMap hU

@[simp] theorem localEquiv_apply {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) (x : E) :
    localEquiv hU f hf hi hD x = f x := rfl

@[simp] theorem localEquiv_source {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    (localEquiv hU f hf hi hD).source = U := rfl

@[simp] theorem localEquiv_target {U : Set E} (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    (localEquiv hU f hf hi hD).target = f '' U := rfl

 theorem contDiffAt_inverse (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {y : E} (hy : y ∈ e.target) : ContDiffAt ℝ ∞ e.symm y := by
  have hs := he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))
  obtain ⟨D,hD⟩ := hD _ (e.map_target hy)
  apply e.contDiffAt_symm hy (f₀' := D) _ hs
  rw [hD]
  exact (hs.differentiableAt (by simp)).hasFDerivAt

 def extendFunction (e : OpenPartialHomeomorph E E) (f : E → ℝ) (y : E) : ℝ := by
  classical
  exact if y ∈ e.target then f (e.symm y) else 0

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_apply (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    {x : E} (hx : x ∈ e.source) : extendFunction e f (e x) = f x := by
  simp only [extendFunction, ite_eq_left (e.map_source hx), e.left_inv hx]

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_zero (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    (S : Set E) (hz : ∀ x ∉ S, f x = 0) {y : E} (hy : y ∉ e '' S) :
    extendFunction e f y = 0 := by
  unfold extendFunction
  split_ifs with hyt
  · apply hz
    intro hin
    exact hy ⟨e.symm y,hin,e.right_inv hyt⟩
  · rfl

 theorem contDiff_extendFunction (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {S : Set E} (hS : IsCompact S)
    (hSU : S ⊆ e.source) (hz : ∀ x ∉ S, f x = 0) :
    ContDiff ℝ ∞ (extendFunction e f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · apply (hf.contDiffAt.comp y (contDiffAt_inverse e he hD hy)).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    simp only [extendFunction, hz, ite_true, Function.comp_apply]
  · have hT : IsClosed (e '' S) := (hS.image_of_continuousOn (e.continuousOn.mono hSU)).isClosed
    have hyt : y ∈ (e '' S)ᶜ := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hSU hx))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hT.isOpen_compl.mem_nhds hyt] with z hz'
    exact extendFunction_zero e f S hz hz'

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_mem_range (e : OpenPartialHomeomorph E E) (f : E → ℝ) (y : E) :
    extendFunction e f y = 0 ∨ ∃ x ∈ e.source, extendFunction e f y = f x := by
  by_cases hy : y ∈ e.target
  · exact Or.inr ⟨e.symm y,e.map_target hy, by simp only [extendFunction,hy,ite_true]⟩
  · exact Or.inl (by simp only [extendFunction,hy,ite_false])

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem eventually_of_comp (e : OpenPartialHomeomorph E E) {x : E} (hx : x ∈ e.source)
    {P : E → Prop} (hP : ∀ᶠ z in 𝓝 x, P (e z)) : ∀ᶠ y in 𝓝 (e x), P y := by
   rw [← e.map_nhds_eq hx]
   exact hP

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE
variable {κ : Type u122} [Fintype κ]

 def form (v w : Vector κ) : ℝ := inner (𝕜 := ℝ) (Complex.I • v) w
 def Preserves (A : Vector κ →L[ℝ] Vector κ) : Prop := ∀ v w, form (A v) (A w) = form v w

 theorem form_ext {v w : Vector κ} (h : ∀ z, form v z = form w z) : v = w := by
   exact smul_right_injective _ Complex.I_ne_zero (ext_inner_right ℝ h)

 theorem form_I (v w : Vector κ) : form (Complex.I • v) w = -inner (𝕜 := ℝ) v w := by
   simp [form, smul_smul]

 theorem injective {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : Function.Injective A := by
   intro v w hvw
   apply form_ext
   intro z
   calc
     form v z = form (A v) (A z) := (hA v z).symm
     _ = form (A w) (A z) := by rw [hvw]
     _ = form w z := hA w z

 theorem invertible {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : A.IsInvertible := by
   have hi := injective hA
   exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
     (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hi)), rfl⟩

 theorem push_gradient {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) (a b : Vector κ)
    (hh : ∀ v, inner (𝕜 := ℝ) b (A v) = inner (𝕜 := ℝ) a v) :
    A (Complex.I • a) = Complex.I • b := by
   apply form_ext
   intro w
   obtain ⟨v,rfl⟩ := (LinearMap.surjective_of_injective (injective hA)) w
   change form (A (Complex.I • a)) (A v) = form (Complex.I • b) (A v)
   rw [hA, form_I, form_I, hh]

 theorem push_hamiltonian (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x) {x : Vector κ} (hx : x ∈ e.source) :
    fderiv ℝ e x (Complex.I • gradient G x) = Complex.I • gradient H (e x) := by
   apply push_gradient (hω x hx)
   intro v
   have hed := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
   have hhd := ((hH.differentiable (by simp) (e x)).hasGradientAt.hasFDerivAt).comp x hed
   have hgd := ((hG.differentiable (by simp) x).hasGradientAt.hasFDerivAt)
   have heq : H ∘ e =ᶠ[𝓝 x] G := by
     filter_upwards [e.open_source.mem_nhds hx] with z hz
     exact hcomp z hz
   have hh := hhd.unique (hgd.congr_of_eventuallyEq heq)
   exact congrArg (fun D : Vector κ →L[ℝ] ℝ => D v) hh

 theorem inverse_curve (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x)
    {x : ℝ → Vector κ} (hxt : ∀ t, x t ∈ e.target)
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (t : ℝ) :
    HasDerivAt (fun s => e.symm (x s)) (Complex.I • gradient G (e.symm (x t))) t := by
   let y := e.symm (x t)
   have hy : y ∈ e.source := e.map_target (hxt t)
   obtain ⟨D,hD⟩ := invertible (hω y hy)
   have hed : HasFDerivAt e D.toContinuousLinearMap y := by
     rw [hD]
     exact ((he.contDiffAt (e.open_source.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
   have hcd := (e.hasFDerivAt_symm (hxt t) hed).comp_hasDerivAt t (hx t)
   apply hcd.congr_deriv
   apply D.injective
   simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
   have hh := push_hamiltonian e he hω hH hG hcomp hy
   rw [e.right_inv (hxt t)] at hh
   change Complex.I • gradient H (x t) = D.toContinuousLinearMap (Complex.I • gradient G y)
   rw [hD]
   exact hh.symm

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
