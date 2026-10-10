import Mathlib
import OAI.Geometry.BallPacking.RelativeJets.EmbeddingAdaptedNeighborhood

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem differential_intertwine {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (heq : ∀ s b, e (B.slice s b) = A.slice s (e b)) (s : ℝ) (b : N) :
    (A.differential s (e b)).comp (manifoldMapDifferential (E := E) (F := F) e b) =
      (manifoldMapDifferential (E := E) (F := F) e (B.slice s b)).comp (B.differential s b) := by
  have heq' : A.slice s ∘ e = e ∘ B.slice s := funext (fun b => (heq s b).symm)
  have h₀ := (((A.slice_smooth s).mdifferentiable (by simp) (e b)).hasMFDerivAt.comp b
    (he.mdifferentiable (by simp) b).hasMFDerivAt).mfderiv
  have h₁ := ((he.mdifferentiable (by simp) (B.slice s b)).hasMFDerivAt.comp b
    ((B.slice_smooth s).mdifferentiable (by simp) b).hasMFDerivAt).mfderiv
  rw [heq'] at h₀
  exact h₀.symm.trans h₁

variable [FiniteDimensional ℝ E]

omit [IsManifold 𝓘(ℝ,F) ∞ N] [FiniteDimensional ℝ E] in
theorem averageOneForm_apply {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (x : M) (v : E) :
    A.averageOneForm α t x v = ∫ s in (0:ℝ)..1,
      parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x v := by
  exact ContinuousLinearMap.intervalIntegral_apply (μ := volume)
    ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1) v

omit [IsManifold 𝓘(ℝ,F) ∞ N] [FiniteDimensional ℝ E] in

theorem averageOneForm_normal_annihilation
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (heq : ∀ s b, e (B.slice s b) = A.slice s (e b))
    (hΩ : ∀ s t x u v, Ω t (A.slice s x) (A.differential s x u) (A.differential s x v) = Ω t x u v)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) {t : ℝ}
    (hi : ∀ b, (manifoldPullbackTwoForm (F := F) Ω e t b).IsInvertible)
    (ha : ∀ b v, α t (e b) v = α t (e b)
      (manifoldMapDifferential (E := E) (F := F) e b
        (symplecticProjection (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) v)))
    (b : N) (v : E) :
    A.averageOneForm α t (e b) v = A.averageOneForm α t (e b)
      (manifoldMapDifferential (E := E) (F := F) e b
        (symplecticProjection (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) v)) := by
  rw [A.averageOneForm_apply hα,A.averageOneForm_apply hα]
  apply intervalIntegral.integral_congr
  intro s _
  have hL : ∀ u w, Ω t (e (B.slice s b)) (A.differential s (e b) u)
      (A.differential s (e b) w) = Ω t (e b) u w := by
    intro u w
    rw [heq]
    exact hΩ s t (e b) u w
  have hI : ∀ u, A.differential s (e b) (manifoldMapDifferential (E := E) (F := F) e b u) =
      manifoldMapDifferential (E := E) (F := F) e (B.slice s b) (B.differential s b u) :=
    fun u => congrArg (fun L : F →L[ℝ] E => L u) (A.differential_intertwine B he heq s b)
  have hh := normal_annihilation_pullback (hi b) (hi (B.slice s b))
    (B.differential_invertible s b).surjective hL hI (ha (B.slice s b)) v
  rw [heq] at hh
  exact hh

end SmoothCircleAction

end
section

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem symplecticHorizontalLift_unique {Ω : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] F}
    (h : (horizontalSystem Ω A).IsInvertible)
    (hV : ∀ v, A v = 0 → (∀ w, A w = 0 → Ω v w = 0) → v = 0)
    (b : F) (v : E) (hv : A v = b) (ho : ∀ w, A w = 0 → Ω v w = 0) :
    v = symplecticHorizontalLift Ω A b := by
  apply sub_eq_zero.mp
  apply hV
  · rw [map_sub,hv,symplecticHorizontalLift_projects h,sub_self]
  · intro w hw
    rw [map_sub,sub_apply,ho w hw,symplecticHorizontalLift_orthogonal h b hw,sub_self]

theorem horizontalSystem_contDiffAt {Ω : P → E →L[ℝ] E →L[ℝ] ℝ}
    {A : P → E →L[ℝ] F} {p : P} (hΩ : ContDiffAt ℝ ∞ Ω p)
    (hA : ContDiffAt ℝ ∞ A p) :
    ContDiffAt ℝ ∞ (fun q => horizontalSystem (Ω q) (A q)) p := by
  unfold horizontalSystem
  have hdual : ContDiffAt ℝ ∞ (fun q => (ContinuousLinearMap.compL ℝ E F ℝ).flip (A q)) p :=
    (ContinuousLinearMap.contDiff _).contDiffAt.comp p hA
  have hp : ContDiff ℝ ∞ (fun L :
      ((E × (F →L[ℝ] ℝ)) →L[ℝ] E →L[ℝ] ℝ) × ((E × (F →L[ℝ] ℝ)) →L[ℝ] F) =>
      L.1.prod L.2) := by
    exact LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞)
      (E := ((E × (F →L[ℝ] ℝ)) →L[ℝ] E →L[ℝ] ℝ) × ((E × (F →L[ℝ] ℝ)) →L[ℝ] F))
      (F := (E × (F →L[ℝ] ℝ)) →L[ℝ] ((E →L[ℝ] ℝ) × F))
      (ContinuousLinearMap.prodₗᵢ ℝ)
  exact hp.contDiffAt.comp p
    (((hΩ.clm_comp (contDiffAt_const (c := ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ)))).sub
      (hdual.clm_comp (contDiffAt_const (c := ContinuousLinearMap.snd ℝ E (F →L[ℝ] ℝ))))).prodMk
      (hA.clm_comp (contDiffAt_const (c := ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ)))))

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace F] in

theorem symplecticHorizontalLift_contDiffAt {Ω : P → E →L[ℝ] E →L[ℝ] ℝ}
    {A : P → E →L[ℝ] F} {p : P} (hΩ : ContDiffAt ℝ ∞ Ω p)
    (hA : ContDiffAt ℝ ∞ A p) (hi : (horizontalSystem (Ω p) (A p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => symplecticHorizontalLift (Ω q) (A q)) p := by
  unfold symplecticHorizontalLift
  have hInv : ContDiffAt ℝ ∞ (fun L :
      (E × (F →L[ℝ] ℝ)) →L[ℝ] ((E →L[ℝ] ℝ) × F) => L.inverse)
      (horizontalSystem (Ω p) (A p)) := hi.contDiffAt_map_inverse
  have hI : ContDiffAt ℝ ∞ (fun q => (horizontalSystem (Ω q) (A q)).inverse) p :=
    by convert! hInv.comp p (horizontalSystem_contDiffAt hΩ hA) using 1
  have hR : ContDiffAt ℝ ∞ (fun q => (horizontalSystem (Ω q) (A q)).inverse.comp
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] ℝ) F)) p :=
    hI.clm_comp (contDiffAt_const (c := ContinuousLinearMap.inr ℝ (E →L[ℝ] ℝ) F))
  exact (contDiffAt_const (c := ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ))).clm_comp hR

omit [CompleteSpace E] [CompleteSpace F] in

theorem vertical_nondegenerate_change {Ω : E →L[ℝ] E →L[ℝ] ℝ}
    {A : E →L[ℝ] F} {C : E →L[ℝ] E} (hC : C.IsInvertible)
    (hV : ∀ v, A v = 0 → (∀ w, A w = 0 → Ω v w = 0) → v = 0) :
    ∀ v, (A.comp C.inverse) v = 0 →
      (∀ w, (A.comp C.inverse) w = 0 → (Ω.bilinearComp C.inverse C.inverse) v w = 0) →
      v = 0 := by
  intro v hv ho
  have he : C.inverse v = 0 := by
    apply hV _ hv
    intro w hw
    have hh := ho (C w) (by simpa only [ContinuousLinearMap.comp_apply,hC.inverse_apply_self] using hw)
    change Ω (C.inverse v) (C.inverse (C w)) = 0 at hh
    rw [hC.inverse_apply_self] at hh
    convert! hh using 1
  exact hC.inverse.injective (by simpa only [map_zero] using he)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] [CompleteSpace F] in

theorem symplecticHorizontalLift_change {Ω : E →L[ℝ] E →L[ℝ] ℝ}
    {A : E →L[ℝ] F} {C : E →L[ℝ] E} (hC : C.IsInvertible)
    (hA : Surjective A)
    (hV : ∀ v, A v = 0 → (∀ w, A w = 0 → Ω v w = 0) → v = 0) (b : F) :
    C (symplecticHorizontalLift Ω A b) =
      symplecticHorizontalLift (Ω.bilinearComp C.inverse C.inverse) (A.comp C.inverse) b := by
  have hAi : Surjective (A.comp C.inverse) := hA.comp hC.inverse.surjective
  have hVi := vertical_nondegenerate_change hC hV
  apply symplecticHorizontalLift_unique (horizontalSystem_isInvertible hAi hVi) hVi
  · simpa only [ContinuousLinearMap.comp_apply,hC.inverse_apply_self] using
      symplecticHorizontalLift_projects (horizontalSystem_isInvertible hA hV) b
  · intro w hw
    change Ω (C.inverse (C (symplecticHorizontalLift Ω A b))) (C.inverse w) = 0
    rw [hC.inverse_apply_self]
    convert! symplecticHorizontalLift_orthogonal (horizontalSystem_isInvertible hA hV) b hw using 1

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldBaseDifferential (g : M → F) (x : M) : E →L[ℝ] F :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x

def manifoldBaseChart (g : M → F) (c : M) (y : E) : F :=
  g ((extChartAt 𝓘(ℝ,E) c).symm y)

theorem manifoldBaseChart_contDiffAt {g : M → F}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (manifoldBaseChart g c) y := by
  exact (hg.contMDiffAt.comp y
    ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy))).contDiffAt

private theorem chart_fderiv_of_hasFDerivAt {f : E → F} {A : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt f A x) : fderiv ℝ f x = A := h.fderiv

theorem manifoldBaseChart_fderiv {g : M → F}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    fderiv ℝ (manifoldBaseChart g c) y =
      (manifoldBaseDifferential (E := E) g ((extChartAt 𝓘(ℝ,E) c).symm y)).comp
        (chartDifferential c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  rw [chartDifferential_inverse hy]
  apply chart_fderiv_of_hasFDerivAt
  exact hasMFDerivAt_iff_hasFDerivAt.mp
    (((hg.mdifferentiable (by simp) _).hasMFDerivAt).comp y
      (hi.mdifferentiableAt (by simp)).hasMFDerivAt)

def manifoldHorizontalField (Ω : ManifoldTwoForm E M) (g : M → F) (b : F)
    (x : M) : TangentSpace 𝓘(ℝ,E) x :=
  symplecticHorizontalLift (Ω x) (manifoldBaseDifferential (E := E) g x) b

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem chart_horizontalField
    {Ω : ManifoldTwoForm E M} {g : M → F}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (hA : ∀ x, Surjective (manifoldBaseDifferential (E := E) g x))
    (hV : ∀ x v, manifoldBaseDifferential (E := E) g x v = 0 →
      (∀ w, manifoldBaseDifferential (E := E) g x w = 0 → Ω x v w = 0) → v = 0)
    (b : F) {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    timeChartField (fun q => manifoldHorizontalField Ω g b q.2) c p =
      symplecticHorizontalLift (chartTwoForm Ω c p.2) (fderiv ℝ (manifoldBaseChart g c) p.2) b := by
  let x := (extChartAt 𝓘(ℝ,E) c).symm p.2
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      ((extChartAt 𝓘(ℝ,E) c).map_target hp) using 1
  rw [manifoldBaseChart_fderiv hg hp]
  exact symplecticHorizontalLift_change hC (hA x) (hV x) b

theorem manifoldHorizontalField_smooth
    {Ω : ManifoldTwoForm E M} {g : M → F}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (chartTwoForm Ω c) (extChartAt 𝓘(ℝ,E) c).target)
    (hA : ∀ x, Surjective (manifoldBaseDifferential (E := E) g x))
    (hV : ∀ x v, manifoldBaseDifferential (E := E) g x v = 0 →
      (∀ w, manifoldBaseDifferential (E := E) g x w = 0 → Ω x v w = 0) → v = 0) (b : F) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,manifoldHorizontalField Ω g b x⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  have hs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p : ℝ × M => (⟨p.2,manifoldHorizontalField Ω g b p.2⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
    apply timeField_smooth_of_coordinates
    intro p
    let y := extChartAt 𝓘(ℝ,E) p.2 p.2
    have hy : y ∈ (extChartAt 𝓘(ℝ,E) p.2).target := mem_extChartAt_target p.2
    have hC : (chartDifferential (E := E) p.2 ((extChartAt 𝓘(ℝ,E) p.2).symm y)).IsInvertible := by
      convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
        ((extChartAt 𝓘(ℝ,E) p.2).map_target hy) using 1
    have hA' : Surjective (fderiv ℝ (manifoldBaseChart g p.2) y) := by
      rw [manifoldBaseChart_fderiv hg hy]
      exact (hA _).comp hC.inverse.surjective
    have hV' : ∀ v, fderiv ℝ (manifoldBaseChart g p.2) y v = 0 →
        (∀ w, fderiv ℝ (manifoldBaseChart g p.2) y w = 0 → chartTwoForm Ω p.2 y v w = 0) → v = 0 := by
      rw [manifoldBaseChart_fderiv hg hy]
      exact vertical_nondegenerate_change hC (hV _)
    have hS := symplecticHorizontalLift_contDiffAt
      ((hΩ p.2).contDiffAt ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p.2).mem_nhds hy))
      ((manifoldBaseChart_contDiffAt hg hy).fderiv_right (m := ∞) (by simp))
      (horizontalSystem_isInvertible hA' hV')
    have hS' := (hS.clm_apply (contDiffAt_const (c := b))).comp (p.1,y) contDiffAt_snd
    apply hS'.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p.2).mem_nhds hy)] with q hq
    exact chart_horizontalField hg hA hV b hq
  exact hs.comp ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_id)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifold_isLocallyConstant_of_differential_zero {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hdf : ∀ x, manifoldBaseDifferential (E := E) f x = 0) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).2
  intro x
  let a := extChartAt 𝓘(ℝ,E) x
  have hy : a x ∈ a.target := mem_extChartAt_target x
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x) (a x) hy
  have hconst (z : E) (hz : z ∈ Metric.ball (a x) r) :
      manifoldBaseChart f x z = manifoldBaseChart f x (a x) := by
    apply (convex_ball (a x) r).is_const_of_fderivWithin_eq_zero
      (fun y hy => ((manifoldBaseChart_contDiffAt hf (hball hy)).differentiableAt
        (by simp)).differentiableWithinAt) _ hz (Metric.mem_ball_self hr)
    intro y hy
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hy,manifoldBaseChart_fderiv hf (hball hy),hdf]
    simp
  have hnear := (continuousAt_extChartAt (I := 𝓘(ℝ,E)) x).preimage_mem_nhds
    (Metric.ball_mem_nhds (a x) hr)
  filter_upwards [hnear, (isOpen_extChartAt_source (I := 𝓘(ℝ,E)) x).mem_nhds
    (mem_extChartAt_source x)] with z hz hzs
  have hc := hconst (a z) hz
  change f (a.symm (a z)) = f (a.symm (a x)) at hc
  simpa only [a.left_inv hzs,a.left_inv (mem_extChartAt_source x)] using hc

theorem manifold_difference_constant {f g : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (hd : ∀ x, manifoldBaseDifferential (E := E) f x = manifoldBaseDifferential (E := E) g x)
    {S : Set M} (hS : IsPreconnected S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    f x - g x = f y - g y := by
  have hzero (z : M) : manifoldBaseDifferential (E := E) (fun w => f w - g w) z = 0 := by
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f - g) z = 0
    rw [mfderiv_sub (hf.mdifferentiable (by simp) z) (hg.mdifferentiable (by simp) z)]
    change manifoldBaseDifferential (E := E) f z - manifoldBaseDifferential (E := E) g z = 0
    rw [hd z,sub_self]
  exact (manifold_isLocallyConstant_of_differential_zero (hf.sub hg) hzero).apply_eq_of_isPreconnected hS hx hy

end
section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

namespace SmoothCircleAction

def generator (A : SmoothCircleAction E M) (x : M) : E :=
  manifoldMapDifferential (F := ℝ) (fun s : ℝ => A.slice s x) (0 : ℝ) (1 : ℝ)

theorem generator_natural (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)
    {f : M → N} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (heq : ∀ s x, f (A.slice s x) = B.slice s (f x)) (x : M) :
    manifoldMapDifferential f x (A.generator x) = B.generator (f x) := by
  have hpath : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun s : ℝ => A.slice s x) :=
    A.smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have he : (f ∘ fun s : ℝ => A.slice s x) = (fun s : ℝ => B.slice s (f x)) :=
    funext (fun s => heq s x)
  have hc : manifoldMapDifferential (f ∘ fun s : ℝ => A.slice s x) 0 =
      (manifoldMapDifferential f (A.slice 0 x)).comp
        (manifoldMapDifferential (fun s : ℝ => A.slice s x) 0) :=
    mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hpath.mdifferentiable (by simp) 0)
  have hz : A.slice 0 x = x := A.zero x
  rw [he,hz] at hc
  exact (congrArg (fun L : ℝ →L[ℝ] F => L 1) hc).symm
end SmoothCircleAction

variable [IsManifold 𝓘(ℝ,E) ∞ M]

theorem equivariant_moment_difference_constant
    (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)
    {Ω₀ : ManifoldTwoForm E M} {Ω₁ : ManifoldTwoForm F N}
    {f : M → N} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (heq : ∀ s x, f (A.slice s x) = B.slice s (f x))
    (hΩ : ∀ x u v, Ω₁ (f x) (manifoldMapDifferential f x u)
      (manifoldMapDifferential f x v) = Ω₀ x u v)
    {μ₀ : M → ℝ} {μ₁ : N → ℝ}
    (hμ₀ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ μ₀)
    (hμ₁ : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ μ₁)
    (hm₀ : ∀ x v, manifoldBaseDifferential (E := E) μ₀ x v = -(Ω₀ x (A.generator x) v))
    (hm₁ : ∀ x v, manifoldBaseDifferential (E := F) μ₁ x v = -(Ω₁ x (B.generator x) v))
    {S : Set M} (hS : IsPreconnected S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    μ₁ (f x) - μ₀ x = μ₁ (f y) - μ₀ y := by
  apply manifold_difference_constant (hμ₁.comp hf) hμ₀ _ hS hx hy
  intro z
  have hc : manifoldBaseDifferential (E := E) (μ₁ ∘ f) z =
      (manifoldBaseDifferential (E := F) μ₁ (f z)).comp (manifoldMapDifferential f z) :=
    mfderiv_comp z (hμ₁.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) z)
  ext v
  rw [hc]
  change manifoldBaseDifferential (E := F) μ₁ (f z) (manifoldMapDifferential f z v) = _
  rw [hm₁,hm₀,←A.generator_natural B hf heq z,hΩ]

theorem equivariant_moment_normalized
    (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)
    {Ω₀ : ManifoldTwoForm E M} {Ω₁ : ManifoldTwoForm F N}
    {f : M → N} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (heq : ∀ s x, f (A.slice s x) = B.slice s (f x))
    (hΩ : ∀ x u v, Ω₁ (f x) (manifoldMapDifferential f x u)
      (manifoldMapDifferential f x v) = Ω₀ x u v)
    {μ₀ : M → ℝ} {μ₁ : N → ℝ}
    (hμ₀ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ μ₀)
    (hμ₁ : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ μ₁)
    (hm₀ : ∀ x v, manifoldBaseDifferential (E := E) μ₀ x v = -(Ω₀ x (A.generator x) v))
    (hm₁ : ∀ x v, manifoldBaseDifferential (E := F) μ₁ x v = -(Ω₁ x (B.generator x) v))
    {S : Set M} (hS : IsPreconnected S) {x₀ : M} (hx₀ : x₀ ∈ S)
    (hnorm : μ₁ (f x₀) = μ₀ x₀) : ∀ x ∈ S, μ₁ (f x) = μ₀ x := by
  intro x hx
  have he := equivariant_moment_difference_constant A B hf heq hΩ hμ₀ hμ₁ hm₀ hm₁ hS hx hx₀
  rw [hnorm,sub_self] at he
  exact sub_eq_zero.mp he

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace SmoothCircleAction

 omit [FiniteDimensional ℝ E] in
 theorem vector_smooth (A : SmoothCircleAction E E) : ContDiff ℝ ∞ A.toFun := by
  have h := A.smooth
  rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact contMDiff_iff_contDiff.mp h

 theorem averageOneForm_spatialDifferential (A : SmoothCircleAction E E)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x =
      fderiv ℝ (fun y => A.average f (t,y)) x := by
  have hg : ContDiff ℝ ∞ (fun p : ℝ × E => f (t,A.slice p.1 p.2)) :=
    hf.comp (contDiff_const.prodMk A.vector_smooth)
  have hd := (hasFDerivAt_fixed_integral hg x).fderiv
  change A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x =
    fderiv ℝ (fun y => ∫ s in (0:ℝ)..1,f (t,A.slice s y)) x
  rw [hd]
  apply intervalIntegral.integral_congr
  intro s _
  have hs : ContDiff ℝ ∞ (A.slice s) := contMDiff_iff_contDiff.mp (A.slice_smooth s)
  have hft : ContDiff ℝ ∞ (fun y => f (t,y)) := hf.comp (contDiff_const.prodMk contDiff_id)
  change (manifoldSpatialDifferential f t (A.slice s x)).comp (A.differential s x) = _
  simp only [manifoldSpatialDifferential,differential,manifoldMapDifferential,mfderiv_eq_fderiv]
  exact (fderiv_comp x (hft.differentiable (by simp) _) (hs.differentiable (by simp) x)).symm

 theorem averaged_spatial_differential_generator_zero (A : SmoothCircleAction E E)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x (A.generator x)=0 := by
  rw [A.averageOneForm_spatialDifferential hf]
  let G : E → ℝ := fun y => A.average f (t,y)
  have hG : ContDiff ℝ ∞ G := contDiff_fixed_integral
    (hf.comp (contDiff_const.prodMk A.vector_smooth))
  have hpath : ContDiff ℝ ∞ (fun s : ℝ => A.slice s x) :=
    A.vector_smooth.comp (contDiff_id.prodMk contDiff_const)
  have he : (G ∘ fun s : ℝ => A.slice s x)=(fun _ : ℝ => G x) :=
    funext fun s => A.average_invariant f t s x
  have hc := fderiv_comp (0:ℝ) (hG.differentiable (by simp) _)
    (hpath.differentiable (by simp) 0)
  rw [he] at hc
  simp only [fderiv_const_apply] at hc
  have hz : A.slice 0 x=x := A.zero x
  rw [hz] at hc
  have hh := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hc
  simpa only [generator,manifoldMapDifferential,mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply,zero_apply] using hh.symm

 omit [FiniteDimensional ℝ E] in
 theorem differential_generator (A : SmoothCircleAction E E) (s : ℝ) (x : E) :
    A.differential s x (A.generator x)=A.generator (A.slice s x) := by
  apply A.generator_natural A (A.slice_smooth s)
  intro r y
  change A.toFun (s,A.toFun (r,y))=A.toFun (r,A.toFun (s,y))
  rw [←A.add,←A.add,add_comm]

 omit [FiniteDimensional ℝ E] in
 theorem averageOneForm_generator_zero (A : SmoothCircleAction E E)
    {α : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α)
    (ha : ∀ t x,α t x (A.generator x)=0) (t : ℝ) (x : E) :
    A.averageOneForm α t x (A.generator x)=0 := by
  rw [A.averageOneForm_apply hα]
  have he : (fun s => parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x (A.generator x))=
      (fun _ : ℝ => (0:ℝ)) := by
    funext s
    change α t (A.slice s x) (A.differential s x (A.generator x))=0
    rw [A.differential_generator,ha]
  rw [he]
  simp

 omit [FiniteDimensional ℝ E] in
 theorem averageOneForm_add (A : SmoothCircleAction E E)
    {α β : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α) (hβ : SmoothOneFormFamily β)
    (t : ℝ) (x : E) : A.averageOneForm (fun t x => α t x+β t x) t x=
      A.averageOneForm α t x+A.averageOneForm β t x := by
  change (∫ s in (0:ℝ)..1,(α t (A.slice s x)+β t (A.slice s x)).comp (A.differential s x))=_
  simp only [ContinuousLinearMap.add_comp]
  exact intervalIntegral.integral_add
    ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1)
    ((A.pullbackOneForm_continuous hβ t x).intervalIntegrable 0 1)

 theorem averaged_corrected_generator_zero (A : SmoothCircleAction E E)
    {α : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α)
    (ha : ∀ t x,α t x (A.generator x)=0)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (correctedOneForm (E := E) α f) t x (A.generator x)=0 := by
  have hdf : SmoothOneFormFamily (manifoldSpatialDifferential (E := E) f) := by
    have hD : ContDiff ℝ ∞ (fun p : ℝ × E => manifoldSpatialDifferential (E := E) f p.1 p.2) := by
      have hh := (hf.fderiv_right (m := ∞) (by simp)).clm_comp
        (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ E))
      convert! hh using 1
      funext p
      simp only [manifoldSpatialDifferential,mfderiv_eq_fderiv]
      have hi : HasFDerivAt (fun y : E => (p.1,y)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
        convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
      exact ((hf.differentiable (by simp) p).hasFDerivAt.comp p.2 hi).fderiv
    intro z
    simpa only [vector_chartOneForm] using hD.contDiffOn
  change A.averageOneForm (fun t x => α t x+manifoldSpatialDifferential (E := E) f t x) t x (A.generator x)=0
  rw [A.averageOneForm_add hα hdf]
  simp only [add_apply,A.averageOneForm_generator_zero hα ha,
    A.averaged_spatial_differential_generator_zero hf,add_zero]

end SmoothCircleAction

end PackingSufficiencySupport.Hamiltonian
end

end OAI
