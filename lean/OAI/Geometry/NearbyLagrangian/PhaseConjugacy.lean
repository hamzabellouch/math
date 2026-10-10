import Mathlib
import OAI.Geometry.NearbyLagrangian.TimeMesh
import OAI.Geometry.NearbyLagrangian.TameBounds

namespace OAI

/-! Critical-locus conjugacy, transport fibers and tame packages. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

abbrev PhaseCritical (U : Set E) (F : E × W → ℝ) :=
  {q : E × W // q.1 ∈ U ∧ verticalDifferential F q.1 q.2 = 0}

def phaseGenerate (F : E × W → ℝ) (q : E × W) : E × E :=
  (q.1,baseGradient F q.1 q.2)

def MorseOn (U : Set E) (F : E × W → ℝ) : Prop :=
  ∀ x ∈ U, ∀ w, verticalDifferential F x w = 0 →
    Function.Surjective (fderiv ℝ (fun v : E × W => verticalDifferential F v.1 v.2) (x,w))

omit [CompleteSpace E] in
lemma baseDifferential_eq_partial {F : E × W → ℝ} (q : E × W)
    (hF : DifferentiableAt ℝ F q) :
    baseDifferential F q.1 q.2 = fderiv ℝ (fun x => F (x,q.2)) q.1 :=
  (hF.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)).fderiv.symm

namespace StepData
variable (S : StepData (E := E) (W := W))

omit [CompleteSpace E] in
lemma phase_critical_iff {q : E × (W × (E × E))} (hq : q.1 ∈ S.U) :
    verticalDifferential (totalPhase S.F S.σ S.κ) q.1 q.2 = 0 ↔
      IsShiftedCritical S.F S.σ S.κ q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hd := ((S.contDiffAt_totalPhase hq).differentiableAt (by simp)).hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  change ((fderiv ℝ (totalPhase S.F S.σ S.κ) q).comp (inr ℝ E (W × (E × E)))) = 0 ↔ _
  rw [← hd.fderiv]
  rfl

def newPhaseCriticalHomeomorph : S.NewCritical ≃ₜ
    PhaseCritical S.U (totalPhase S.F S.σ S.κ) where
  toFun q := ⟨q.val,q.property.1,(S.phase_critical_iff q.property.1).mpr q.property.2⟩
  invFun q := ⟨q.val,q.property.1,(S.phase_critical_iff q.property.1).mp q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def phaseCriticalHomeomorph : PhaseCritical S.U S.F ≃ₜ
    PhaseCritical S.U (totalPhase S.F S.σ S.κ) :=
  S.criticalHomeomorph.trans S.newPhaseCriticalHomeomorph

theorem phaseGenerate_conjugacy (q : PhaseCritical S.U S.F) :
    phaseGenerate (totalPhase S.F S.σ S.κ) (S.phaseCriticalHomeomorph q).val =
      S.ψ (phaseGenerate S.F q.val) := by
  let r := S.carryCritical q
  have he : S.recover r.val = q.val := congrArg Subtype.val (S.recover_carry q)
  have hx := congrArg Prod.fst he
  have hw := congrArg Prod.snd he
  change S.shiftedBase r.val.1 r.val.2.1 r.val.2.2.1 = q.val.1 at hx
  change r.val.2.1 = q.val.2 at hw
  change (r.val.1,baseGradient (totalPhase S.F S.σ S.κ) r.val.1 r.val.2) =
    S.ψ (q.val.1,baseGradient S.F q.val.1 q.val.2)
  apply Prod.ext
  · rfl
  · apply (innerSL_inj (𝕜 := ℝ)).mp
    rw [innerSL_baseGradient, baseDifferential_eq_partial r.val
      ((S.contDiffAt_totalPhase r.property.1).differentiableAt (by simp))]
    have ho := S.new_output r.property.1 r.property.2
    rw [hx] at ho
    simpa only [hw,totalPhase] using ho

end StepData
end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open scoped ContDiff InnerProductSpace

def TransportFiber (E W : Type) : ℕ → Type
  | 0 => W
  | n+1 => TransportFiber E W n × (E × E)

instance transportFiberNorm (E W : Type) [NormedAddCommGroup E] [NormedAddCommGroup W]
    (n : ℕ) : NormedAddCommGroup (TransportFiber E W n) :=
  match n with
  | 0 => inferInstanceAs (NormedAddCommGroup W)
  | n+1 => letI := transportFiberNorm E W n
           inferInstanceAs (NormedAddCommGroup (TransportFiber E W n × (E × E)))

instance transportFiberSpace (E W : Type) [NormedAddCommGroup E] [NormedAddCommGroup W]
    [NormedSpace ℝ E] [NormedSpace ℝ W] (n : ℕ) : NormedSpace ℝ (TransportFiber E W n) :=
  match n with
  | 0 => inferInstanceAs (NormedSpace ℝ W)
  | n+1 => letI := transportFiberSpace E W n
           inferInstanceAs (NormedSpace ℝ (TransportFiber E W n × (E × E)))

instance transportFiberFinite (E W : Type) [NormedAddCommGroup E] [NormedAddCommGroup W]
    [NormedSpace ℝ E] [NormedSpace ℝ W] [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    (n : ℕ) : FiniteDimensional ℝ (TransportFiber E W n) :=
  match n with
  | 0 => inferInstanceAs (FiniteDimensional ℝ W)
  | n+1 => letI := transportFiberFinite E W n
           inferInstanceAs (FiniteDimensional ℝ (TransportFiber E W n × (E × E)))

variable {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def iterReference (g : E × W → ℝ) : (n : ℕ) → E × TransportFiber E W n → ℝ
  | 0 => g
  | n+1 => fun q => iterReference g n (q.1,q.2.1)-inner ℝ q.2.2.1 q.2.2.2

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

namespace StepData
variable (S : StepData (E := E) (W := W))

omit [FiniteDimensional ℝ W] in

theorem tame_phase_package {g : E × W → ℝ} (T : TameOn S.U S.F g)
    (hM : MorseOn S.U S.F) (hζU : tsupport S.ζ ⊆ S.U)
    (hζ : HasCompactSupport S.ζ) (hβ : HasCompactSupport S.β) (hχ : HasCompactSupport S.χ)
    (hσ : HasCompactSupport S.σ)
    (htwist : ∀ X p, Function.Surjective (ContinuousLinearMap.id ℝ E +
      (fderiv ℝ (mixedDisplacement S.σ) (X,p)).comp (inl ℝ E E))) :
    TameOn S.U (totalPhase S.F S.σ S.κ)
      (fun q => homogeneousReference g q.1 q.2) ∧
    MorseOn S.U (totalPhase S.F S.σ S.κ) ∧
    ∃ e : PhaseCritical S.U S.F ≃ₜ PhaseCritical S.U (totalPhase S.F S.σ S.κ),
      ∀ q, phaseGenerate (totalPhase S.F S.σ S.κ) (e q).val = S.ψ (phaseGenerate S.F q.val) := by
  refine ⟨S.tameOn_transport T hζU hζ hβ hχ hσ,?_,
    S.phaseCriticalHomeomorph,S.phaseGenerate_conjugacy⟩
  intro x hx w hw
  exact S.transported_morse_family hM htwist (x,w) hx hw

end StepData

theorem PreparedMixedStep.tame_step {S : Set (E × E)} {δ : ℝ}
    (P : PreparedMixedStep S δ) (hS : IsCompact S) {U : Set E} (hU : IsOpen U)
    (hSU : ∀ z ∈ S, z.1 ∈ U) (hδ : 0 < δ)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζr : ∀ x, ζ x ∈ Icc (0:ℝ) 1)
    (hζ1 : ∀ x ∈ Prod.fst '' S, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    {F g : E × W → ℝ} (T : TameOn U F g) (hM : MorseOn U F) :
    ∃ F' : E × (W × (E × E)) → ℝ,
      TameOn U F' (fun q => homogeneousReference g q.1 q.2) ∧ MorseOn U F' ∧
      ∃ e : PhaseCritical U F ≃ₜ PhaseCritical U F',
        ∀ q, phaseGenerate F' (e q).val = P.ψ (phaseGenerate F q.val) := by
  obtain ⟨R,c,C,hR,hc,hC,hb,hv⟩ := T.exists_tail_bounds
  obtain ⟨D,hDU,hDF,hDσ,hDψ,hDζ,hDδ,hβ,hχ,hσ,_hψ,htwist⟩ :=
    P.exists_stepData hS hU hSU hδ hζ hζr hζ1 hbuf F hR hc hC T.smooth_F hb hv
  subst U
  subst F
  have hzU : tsupport D.ζ ⊆ D.U := by
    rw [hDζ]
    intro x hx
    have hh := hbuf x hx 0 (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hδ).le)
    simpa only [add_zero] using hh
  have hz : HasCompactSupport D.ζ := by simpa only [hDζ] using hζc
  have hh : ∃ F' : E × (W × (E × E)) → ℝ,
      TameOn D.U F' (fun q => homogeneousReference g q.1 q.2) ∧ MorseOn D.U F' ∧
      ∃ e : PhaseCritical D.U D.F ≃ₜ PhaseCritical D.U F',
        ∀ q, phaseGenerate F' (e q).val = D.ψ (phaseGenerate D.F q.val) :=
    ⟨totalPhase D.F D.σ D.κ,D.tame_phase_package T hM hzU hz hβ hχ hσ htwist⟩
  simpa only [hDψ] using hh

end NearbyLagrangian.Transport

end

end OAI
