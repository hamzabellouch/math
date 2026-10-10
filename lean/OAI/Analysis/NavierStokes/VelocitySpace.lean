import Mathlib

namespace OAI

/-! Solenoidal equivariant velocity spaces and preliminary discretely self-similar Navier-Stokes estimates. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology ContDiff

namespace DSS

instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev V3 (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 3)
abbrev Velocity := R3 → ℝ → R3

def basisVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

def gradient {𝕜 : Type*} [RCLike 𝕜] (φ : R3 → 𝕜) (x : R3) : V3 𝕜 :=
  WithLp.toLp 2 (fun i => fderiv ℝ φ x (basisVector i))

theorem continuous_gradient {𝕜 : Type*} [RCLike 𝕜] {φ : R3 → 𝕜}
    (hφ : ContDiff ℝ ∞ φ) : Continuous (gradient φ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => 𝕜)).comp
  exact continuous_pi fun i => (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem compactSupport_gradient {𝕜 : Type*} [RCLike 𝕜] {φ : R3 → 𝕜}
    (hφ : HasCompactSupport φ) : HasCompactSupport (gradient φ) := by
  exact (hφ.fderiv ℝ).comp_left (g := fun d : R3 →L[ℝ] 𝕜 =>
    WithLp.toLp 2 (fun i => d (basisVector i))) (by rfl)

structure ScalarTest (𝕜 : Type*) [RCLike 𝕜] where
  val : R3 → 𝕜
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val

def ScalarTest.gradientLp {𝕜 : Type*} [RCLike 𝕜] (φ : ScalarTest 𝕜) :
    Lp (V3 𝕜) 2 (volume : Measure R3) :=
  ((continuous_gradient φ.smooth).memLp_of_hasCompactSupport
    (compactSupport_gradient φ.compact)).toLp (gradient φ.val)

abbrev HorizontalOrthogonal := {Q : R3 ≃ₗᵢ[ℝ] R3 // Q (basisVector 2) = basisVector 2}

def horizontalValueMap (𝕜 : Type*) [RCLike 𝕜] (Q : HorizontalOrthogonal) :
    V3 𝕜 →L[𝕜] V3 𝕜 :=
  (Matrix.toEuclideanLin (fun i j : Fin 3 =>
    (RCLike.ofReal ((Q.val (basisVector j)) i) : 𝕜))).toContinuousLinearMap

theorem horizontalValueMap_real (Q : HorizontalOrthogonal) (x : R3) :
    horizontalValueMap ℝ Q x = Q.val x := by
  have hm : (fun i j : Fin 3 =>
      (RCLike.ofReal ((Q.val (basisVector j)) i) : ℝ)) =
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3))
        Q.val.toLinearMap := by
    ext i j
    simp only [LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr]
    rfl
  change Matrix.toLpLin 2 2 _ x = Q.val x
  rw [Matrix.toLpLin_eq_toLin, hm, Matrix.toLin_toMatrix]
  rfl

abbrev VelocityPair (𝕜 : Type*) [RCLike 𝕜] :=
  WithLp 1 (Lp (V3 𝕜) 2 (volume : Measure R3) × Lp (V3 𝕜) 4 (volume : Measure R3))

def velocitySubmodule (𝕜 : Type*) [RCLike 𝕜] : Submodule 𝕜 (VelocityPair 𝕜) where
  carrier := {a |
    (a.fst : R3 →ₘ[volume] V3 𝕜) = (a.snd : R3 →ₘ[volume] V3 𝕜) ∧
    (∀ φ : ScalarTest 𝕜, inner 𝕜 φ.gradientLp a.fst = 0) ∧
    (∀ Q : HorizontalOrthogonal,
      Lp.compMeasurePreservingₗ 𝕜 Q.val Q.val.measurePreserving a.fst =
        (horizontalValueMap 𝕜 Q).compLpₗ 2 volume a.fst)}
  zero_mem' := by
    refine ⟨rfl, ?_, ?_⟩
    · intro φ
      exact inner_zero_right _
    · intro Q
      exact (map_zero (Lp.compMeasurePreservingₗ 𝕜 Q.val Q.val.measurePreserving)).trans
        (map_zero ((horizontalValueMap 𝕜 Q).compLpₗ 2 volume)).symm
  add_mem' := by
    rintro a b ⟨ha, hda, hsa⟩ ⟨hb, hdb, hsb⟩
    refine ⟨?_, ?_, ?_⟩
    · change (a.fst : R3 →ₘ[volume] V3 𝕜) + (b.fst : R3 →ₘ[volume] V3 𝕜) =
        (a.snd : R3 →ₘ[volume] V3 𝕜) + (b.snd : R3 →ₘ[volume] V3 𝕜)
      rw [ha, hb]
    · intro φ
      simp only [WithLp.add_fst, inner_add_right, hda φ, hdb φ, add_zero]
    · intro Q
      simpa only [WithLp.add_fst, map_add] using congrArg₂ (· + ·) (hsa Q) (hsb Q)
  smul_mem' := by
    rintro c a ⟨ha, hda, hsa⟩
    refine ⟨?_, ?_, ?_⟩
    · change c • (a.fst : R3 →ₘ[volume] V3 𝕜) = c • (a.snd : R3 →ₘ[volume] V3 𝕜)
      rw [ha]
    · intro φ
      simp only [WithLp.smul_fst, inner_smul_right, hda φ, mul_zero]
    · intro Q
      simpa only [WithLp.smul_fst, map_smul] using congrArg (c • ·) (hsa Q)

abbrev X (𝕜 : Type*) [RCLike 𝕜] := ↥(velocitySubmodule 𝕜)

def X.field {𝕜 : Type*} [RCLike 𝕜] (v : X 𝕜) : R3 → V3 𝕜 := v.val.fst

theorem X.norm_eq {𝕜 : Type*} [RCLike 𝕜] (v : X 𝕜) :
    ‖v‖ = ‖v.val.fst‖ + ‖v.val.snd‖ :=
  WithLp.prod_norm_eq_of_L1 v.val

theorem X.memLp {𝕜 : Type*} [RCLike 𝕜] (v : X 𝕜) :
    MemLp v.field 2 (volume : Measure R3) ∧ MemLp v.field 4 volume := by
  refine ⟨Lp.memLp v.val.fst, (Lp.memLp v.val.snd).ae_eq ?_⟩
  change ⇑(v.val.snd : R3 →ₘ[volume] V3 𝕜) =ᵐ[volume]
    ⇑(v.val.fst : R3 →ₘ[volume] V3 𝕜)
  rw [v.property.1]

theorem X.solenoidal {𝕜 : Type*} [RCLike 𝕜] (v : X 𝕜) (φ : ScalarTest 𝕜) :
    (∫ x : R3, inner 𝕜 (gradient φ.val x) (v.field x)) = 0 := by
  have hg : (φ.gradientLp : R3 → V3 𝕜) =ᵐ[volume] gradient φ.val :=
    MemLp.coeFn_toLp _
  calc
    _ = ∫ x : R3, inner 𝕜 (φ.gradientLp x) (v.val.fst x) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
      rfl
    _ = inner 𝕜 φ.gradientLp v.val.fst := (L2.inner_def _ _).symm
    _ = 0 := v.property.2.1 φ

theorem X.equivariant {𝕜 : Type*} [RCLike 𝕜] (v : X 𝕜)
    (Q : HorizontalOrthogonal) :
    (fun x => v.field (Q.val x)) =ᵐ[volume] fun x => horizontalValueMap 𝕜 Q (v.field x) := by
  have h : Lp.compMeasurePreserving Q.val Q.val.measurePreserving v.val.fst =
      (horizontalValueMap 𝕜 Q).compLp v.val.fst := v.property.2.2 Q
  apply (Lp.coeFn_compMeasurePreserving v.val.fst Q.val.measurePreserving).symm.trans
  rw [h]
  exact (horizontalValueMap 𝕜 Q).coeFn_compLp' v.val.fst

theorem X.equivariant_real (v : X ℝ) (Q : HorizontalOrthogonal) :
    (fun x => v.field (Q.val x)) =ᵐ[volume] fun x => Q.val (v.field x) := by
  simpa only [horizontalValueMap_real] using v.equivariant Q

theorem velocitySubmodule_isClosed (𝕜 : Type*) [RCLike 𝕜] :
    IsClosed (velocitySubmodule 𝕜 : Set (VelocityPair 𝕜)) := by
  apply IsSeqClosed.isClosed
  intro a x ha hx
  have h₂ := ((WithLp.continuous_fst 1 _ _).tendsto x).comp hx
  have h₄ := ((WithLp.continuous_snd 1 _ _).tendsto x).comp hx
  refine ⟨?_, ?_, ?_⟩
  · apply AEEqFun.ext
    have heq : ∀ n, (a n).fst =ᵐ[volume] (a n).snd := by
      intro n
      change ⇑((a n).fst : R3 →ₘ[volume] V3 𝕜) =ᵐ[volume]
        ⇑((a n).snd : R3 →ₘ[volume] V3 𝕜)
      rw [(ha n).1]
    exact tendstoInMeasure_ae_unique
      ((tendstoInMeasure_of_tendsto_Lp h₂).congr_left heq)
      (tendstoInMeasure_of_tendsto_Lp h₄)
  · intro φ
    apply tendsto_nhds_unique (((innerSL 𝕜 φ.gradientLp).continuous.tendsto x.fst).comp h₂)
    have heq : (fun n => inner 𝕜 φ.gradientLp (a n).fst) = fun _ => 0 :=
      funext fun n => (ha n).2.1 φ
    change Tendsto (fun n => inner 𝕜 φ.gradientLp (a n).fst) atTop (𝓝 0)
    rw [heq]
    exact tendsto_const_nhds
  · intro Q
    have hleft := ((Lp.compMeasurePreservingₗᵢ 𝕜 Q.val Q.val.measurePreserving).continuous.tendsto
      x.fst).comp h₂
    have hright := (((horizontalValueMap 𝕜 Q).compLpL 2 volume).continuous.tendsto x.fst).comp h₂
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n => ((ha n).2.2 Q).symm))

instance X.completeSpace (𝕜 : Type*) [RCLike 𝕜] : CompleteSpace (X 𝕜) := by
  have : IsClosed (velocitySubmodule 𝕜 : Set (VelocityPair 𝕜)) :=
    velocitySubmodule_isClosed 𝕜
  exact IsClosed.completeSpace_coe

def complexifyVector (v : R3) : V3 ℂ :=
  WithLp.toLp 2 (fun i => (v i : ℂ))

def ComplexDecomposition (v : X ℂ) (a b : X ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure R3),
    v.field x = complexifyVector (a.field x) + Complex.I • complexifyVector (b.field x)

def IsComplexification (T : X ℝ →L[ℝ] X ℝ) (TC : X ℂ →L[ℂ] X ℂ) : Prop :=
  ∀ v : X ℂ, ∃ a b : X ℝ,
    ComplexDecomposition v a b ∧ ComplexDecomposition (TC v) (T a) (T b)

def divergence (f : R3 → R3) (x : R3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ f x (basisVector i)) i

def laplacian (f : R3 → R3) (x : R3) : R3 :=
  ∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ f z (basisVector i)) x (basisVector i)

def SmoothUnforcedNS (U : Velocity) : Prop :=
  ContDiffOn ℝ ∞ (fun z : R3 × ℝ => U z.1 z.2) {z | 0 < z.2} ∧
  ∃ p : R3 → ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun z : R3 × ℝ => p z.1 z.2) {z | 0 < z.2} ∧
    ∀ (x : R3) (t : ℝ), 0 < t →
      divergence (fun z => U z t) x = 0 ∧
      deriv (U x) t + fderiv ℝ (fun z => U z t) x (U x t) +
        gradient (fun z => p z t) x - laplacian (fun z => U z t) x = 0

def AxisymmetricSwirlFree (U : Velocity) : Prop :=
  ∀ (Q : HorizontalOrthogonal) (x : R3) (t : ℝ), 0 < t →
    U (Q.val x) t = Q.val (U x t)

def DiscretelySelfSimilar (L : ℝ) (U : Velocity) : Prop :=
  ∀ (x : R3) (t : ℝ), 0 < t →
    U ((L ^ 2) • x) ((L ^ 4) * t) = (L ^ 2)⁻¹ • U x t

def period (L : ℝ) : ℝ := 4 * Real.log L

def rescaled (U : Velocity) (y : R3) (τ : ℝ) : R3 :=
  Real.sqrt (Real.exp τ) • U (Real.sqrt (Real.exp τ) • y) (Real.exp τ)

def DecayBound (U : Velocity) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x : R3) (t : ℝ), 0 < t →
    ‖U x t‖ ≤ C / (Real.sqrt t + ‖x‖)

def DistributionalInitialTrace (U : Velocity) (U₀ : R3 → R3) : Prop :=
  LocallyIntegrable U₀ (volume : Measure R3) ∧
  ∀ ψ : R3 → R3, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    Tendsto (fun t : ℝ => ∫ x : R3, inner ℝ (U x t) (ψ x))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : R3, inner ℝ (U₀ x) (ψ x)))

def TraceProperties (L : ℝ) (U : Velocity) (U₀ : R3 → R3) : Prop :=
  DistributionalInitialTrace U U₀ ∧
  ContDiffOn ℝ ∞ U₀ ({0}ᶜ : Set R3) ∧
  (∀ x : R3, U₀ ((L ^ 2) • x) = (L ^ 2)⁻¹ • U₀ x) ∧
  ∃ C : ℕ → ℝ, ∀ k : ℕ, 0 < C k ∧
    ∀ x : R3, x ≠ 0 → ‖iteratedFDeriv ℝ k U₀ x‖ ≤ C k / ‖x‖ ^ (k + 1)

structure SolenoidalTest where
  val : R3 → R3
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val
  solenoidal : ∀ x, divergence val x = 0

def rescaledWeakSpatial (V : Velocity) (v : X ℝ) (ψ : SolenoidalTest)
    (τ : ℝ) (y : R3) : ℝ :=
  - inner ℝ (v.field y) (laplacian ψ.val y) +
    (1 / 2 : ℝ) * inner ℝ (v.field y) (fderiv ℝ ψ.val y y) +
    inner ℝ (v.field y) (ψ.val y) -
    inner ℝ (v.field y) (fderiv ℝ ψ.val y (V y τ)) -
    inner ℝ (V y τ) (fderiv ℝ ψ.val y (v.field y))

def WeakLinearizedSolution (V : Velocity) (s : ℝ) (w : ℝ → X ℝ) : Prop :=
  ContinuousOn w (Ici s) ∧
  ∀ ψ : SolenoidalTest,
    (∀ τ ∈ Ici s,
      Integrable (fun y : R3 => inner ℝ ((w τ).field y) (ψ.val y)) ∧
      Integrable (rescaledWeakSpatial V (w τ) ψ τ)) ∧
    ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ Ioi s →
      let F := fun τ : ℝ =>
        - deriv h τ * (∫ y : R3, inner ℝ ((w τ).field y) (ψ.val y)) +
          h τ * (∫ y : R3, rescaledWeakSpatial V (w τ) ψ τ y)
      Integrable F ∧ (∫ τ : ℝ, F τ) = 0

abbrev Evolution := ℝ → ℝ → (X ℝ →L[ℝ] X ℝ)

def ForwardEvolution (V : Velocity) (E : Evolution) : Prop :=
  CompleteSpace (X ℝ) ∧
  (∀ s : ℝ, E s s = ContinuousLinearMap.id ℝ (X ℝ)) ∧
  (∀ (s r t : ℝ), s ≤ r → r ≤ t → E t r ∘L E r s = E t s) ∧
  (∀ v : X ℝ, ContinuousOn (fun z : ℝ × ℝ => E z.1 z.2 v) {z | z.2 ≤ z.1}) ∧
  (∀ (s : ℝ) (v : X ℝ), WeakLinearizedSolution V s (fun τ => E τ s v)) ∧
  ∀ (s : ℝ) (w : ℝ → X ℝ), WeakLinearizedSolution V s w →
    ∀ τ : ℝ, s ≤ τ → w τ = E τ s (w s)

structure SpectralSplitting {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : W →L[ℂ] W) (F : Set ℂ) where
  projection : W →L[ℂ] W
  idempotent : projection * projection = projection
  commutes : Commute projection T
  onRange : LinearMap.range projection.toLinearMap →L[ℂ]
    LinearMap.range projection.toLinearMap
  onKernel : LinearMap.ker projection.toLinearMap →L[ℂ]
    LinearMap.ker projection.toLinearMap
  onRange_eq : ∀ x, (onRange x).val = T x.val
  onKernel_eq : ∀ x, (onKernel x).val = T x.val
  spectrum_range : spectrum ℂ onRange = F
  spectrum_kernel : spectrum ℂ onKernel = spectrum ℂ T \ F

def FiniteAlgebraicEigenvalue {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : W →L[ℂ] W) (z : ℂ) : Prop :=
  (∃ v : W, v ≠ 0 ∧ T v = z • v) ∧
  ∃ D : SpectralSplitting T {z}, FiniteDimensional ℂ (LinearMap.range D.projection.toLinearMap)

def IsolatedSpectralValue {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : W →L[ℂ] W) (z : ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ T, dist w z < ε → w = z

structure RealSpectralSplitting (T : X ℝ →L[ℝ] X ℝ) (TC : X ℂ →L[ℂ] X ℂ)
    (F : Set ℂ) where
  complexSplitting : SpectralSplitting TC F
  realProjection : X ℝ →L[ℝ] X ℝ
  idempotent : realProjection * realProjection = realProjection
  commutes : Commute realProjection T
  complexifies : IsComplexification realProjection complexSplitting.projection
  finite_real : FiniteDimensional ℝ (LinearMap.range realProjection.toLinearMap)
  finite_complex : FiniteDimensional ℂ
    (LinearMap.range complexSplitting.projection.toLinearMap)

def SpectralConclusions (P : ℝ) (T : X ℝ →L[ℝ] X ℝ) (TC : X ℂ →L[ℂ] X ℂ) : Prop :=
  CompleteSpace (X ℂ) ∧ IsComplexification T TC ∧
  (4 : ℝ≥0∞) ≤ spectralRadius ℂ TC ∧
  (∀ z ∈ spectrum ℂ TC, Real.exp (-P / 4) < ‖z‖ →
    IsolatedSpectralValue TC z ∧ FiniteAlgebraicEigenvalue TC z) ∧
  (∀ F : Set ℂ, IsClosed F →
    (∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ F, Real.exp (-P / 4) + ε ≤ ‖z‖) →
    (spectrum ℂ TC ∩ F).Finite) ∧
  (∃ D : RealSpectralSplitting T TC {z | z ∈ spectrum ℂ TC ∧ 1 < ‖z‖},
    D.realProjection ≠ 0 ∧ D.complexSplitting.projection ≠ 0) ∧
  (∀ F : Set ℂ, F.Finite →
    (∀ z ∈ F, z ∈ spectrum ℂ TC ∧ Real.exp (-P / 4) < ‖z‖) →
    (∀ z : ℂ, z ∈ F ↔ star z ∈ F) → Nonempty (RealSpectralSplitting T TC F))

def UnstableDSSFlow : Prop :=
  ∃ (L : ℝ) (U : Velocity) (U₀ : R3 → R3),
    1 < L ∧ SmoothUnforcedNS U ∧ AxisymmetricSwirlFree U ∧
    DiscretelySelfSimilar L U ∧ DecayBound U ∧ TraceProperties L U U₀ ∧
    ∃ E : Evolution, ForwardEvolution (rescaled U) E ∧
      ∃ TC : X ℂ →L[ℂ] X ℂ, SpectralConclusions (period L) (E (period L) 0) TC

theorem period_pos {L : ℝ} (hL : 1 < L) : 0 < period L :=
  mul_pos (by norm_num) (Real.log_pos hL)

theorem exp_period {L : ℝ} (hL : 0 < L) : Real.exp (period L) = L ^ 4 := by
  simpa only [period, Nat.cast_ofNat, Real.exp_log hL] using Real.exp_nat_mul (Real.log L) 4

theorem essential_radius_eq_inv {L : ℝ} (hL : 0 < L) :
    Real.exp (-period L / 4) = L⁻¹ := by
  have h : -period L / 4 = -Real.log L := by unfold period; ring
  rw [h, Real.exp_neg, Real.exp_log hL]

theorem essential_radius_lt_one {L : ℝ} (hL : 1 < L) :
    Real.exp (-period L / 4) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have := period_pos hL
  linarith

theorem rescaled_at_log (U : Velocity) (y : R3) {t : ℝ} (ht : 0 < t) :
    rescaled U y (Real.log t) = Real.sqrt t • U (Real.sqrt t • y) t := by
  simp only [rescaled, Real.exp_log ht]

theorem rescaled_periodic {L : ℝ} {U : Velocity} (hL : 0 < L)
    (hU : DiscretelySelfSimilar L U) (y : R3) :
    Function.Periodic (rescaled U y) (period L) := by
  intro τ
  have he : Real.exp (τ + period L) = L ^ 4 * Real.exp τ := by
    rw [Real.exp_add, exp_period hL, mul_comm]
  have hs : Real.sqrt (L ^ 4 * Real.exp τ) = L ^ 2 * Real.sqrt (Real.exp τ) := by
    rw [Real.sqrt_mul (by positivity)]
    have hp : L ^ 4 = (L ^ 2) ^ 2 := by ring
    rw [hp, Real.sqrt_sq (sq_nonneg L)]
  dsimp [rescaled]
  rw [he, hs, mul_smul (L ^ 2) (Real.sqrt (Real.exp τ)) y,
    hU _ _ (Real.exp_pos τ), smul_smul]
  congr 1
  field_simp

theorem rescaled_decay {U : Velocity} {C : ℝ}
    (hU : ∀ (x : R3) (t : ℝ), 0 < t → ‖U x t‖ ≤ C / (Real.sqrt t + ‖x‖))
    (y : R3) (τ : ℝ) : ‖rescaled U y τ‖ ≤ C / (1 + ‖y‖) := by
  have hs : 0 < Real.sqrt (Real.exp τ) := Real.sqrt_pos.2 (Real.exp_pos τ)
  have hd : 0 < 1 + ‖y‖ := by positivity
  calc
    ‖rescaled U y τ‖ = Real.sqrt (Real.exp τ) *
        ‖U (Real.sqrt (Real.exp τ) • y) (Real.exp τ)‖ := by
      simp only [rescaled, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    _ ≤ Real.sqrt (Real.exp τ) *
        (C / (Real.sqrt (Real.exp τ) + Real.sqrt (Real.exp τ) * ‖y‖)) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hs] using
        hU (Real.sqrt (Real.exp τ) • y) (Real.exp τ) (Real.exp_pos τ)
    _ = C / (1 + ‖y‖) := by
      rw [show Real.sqrt (Real.exp τ) + Real.sqrt (Real.exp τ) * ‖y‖ =
        Real.sqrt (Real.exp τ) * (1 + ‖y‖) by ring]
      field_simp

theorem spectralRadius_ge_of_fixed_orbit_growth
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (T : W →L[ℂ] W) {v : W} (hv : v ≠ 0) {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hgrowth : ∀ n : ℕ, c * a ^ n ≤ ‖(T ^ n) v‖) :
    ENNReal.ofReal a ≤ spectralRadius ℂ T := by
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hC : 0 < c / ‖v‖ := div_pos hc hvnorm
  have hroot : Tendsto (fun n : ℕ => (c / ‖v‖) ^ (1 / (n : ℝ)) * a)
      atTop (𝓝 a) := by
    have ht := (tendsto_const_nhds (x := c / ‖v‖)).rpow
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) (Or.inl hC.ne')
    simpa only [Real.rpow_zero, one_mul] using ht.mul_const a
  refine le_of_tendsto_of_tendsto
    ((ENNReal.continuous_ofReal.tendsto a).comp hroot)
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T) ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  apply ENNReal.ofReal_le_ofReal
  have hop : (c / ‖v‖) * a ^ n ≤ ‖T ^ n‖ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hvnorm]
    exact (hgrowth n).trans ((T ^ n).le_opNorm v)
  have hp := Real.rpow_le_rpow (mul_nonneg hC.le (pow_nonneg ha n)) hop
    (by positivity : 0 ≤ (1 / (n : ℝ)))
  simpa only [Real.mul_rpow hC.le (pow_nonneg ha n), one_div,
    Real.pow_rpow_inv_natCast ha hn] using hp

end DSS

end

end OAI
