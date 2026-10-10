import Mathlib
import OAI.Analysis.Conductivity.Flux.WeakFluxClassicalC1
import OAI.Analysis.Conductivity.Geometry.TorusTraceFiniteEnd
import OAI.Analysis.Conductivity.Geometry.TorusAffineField
import OAI.Analysis.Conductivity.Sobolev.AxialExtension
import OAI.Analysis.Conductivity.Variational.WeakPairOverlap

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def torusEndingCorrection (d e : ℝ) (v f : Coord3 → ℝ) : Coord3 → ℝ :=
  axialZeroExtension (d+e/4) (e/2) (v-f)

def torusEndingFluxCorrection (d e : ℝ) (G F : Coord3 → Coord3) : Coord3 → Coord3 :=
  axialZeroExtension (d+e/4) (e/2) (G-F)

lemma torusEndingCorrection_C2 {d e : ℝ} (he : 0<e) {v f : Coord3 → ℝ}
    (hv : ContDiff ℝ 2 v) (hf : ContDiffOn ℝ 2 f {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x) :
    ContDiff ℝ 2 (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_contDiff (by linarith : 0<e/2)
  · exact (hv.contDiffOn.sub hf).mono (fun x hx => by dsimp at hx ⊢; linarith)
  · intro x hx
    change v x-f x=0
    exact sub_eq_zero.mpr (hz x ⟨by linarith [hx.1],by linarith [hx.2]⟩)

lemma torusEndingFluxCorrection_C1 {d e : ℝ} (he : 0<e) {G F : Coord3 → Coord3}
    (hG : ContDiff ℝ 1 G) (hF : ContDiffOn ℝ 1 F {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x) :
    ContDiff ℝ 1 (torusEndingFluxCorrection d e G F) := by
  apply axialZeroExtension_contDiff (by linarith : 0<e/2)
  · exact (hG.contDiffOn.sub hF).mono (fun x hx => by dsimp at hx ⊢; linarith)
  · intro x hx
    change G x-F x=0
    exact sub_eq_zero.mpr (hz x ⟨by linarith [hx.1],by linarith [hx.2]⟩)

lemma torusEndingCorrection_periodic {T d e : ℝ} {v f : Coord3 → ℝ}
    (hv : AngularPeriodic T v) (hf : AngularPeriodic T f) :
    AngularPeriodic T (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_periodic
  intro n x
  change v (x+angularShift T n)-f (x+angularShift T n)=v x-f x
  rw [hv n x,hf n x]

lemma torusEndingFluxCorrection_periodic {T d e : ℝ} {G F : Coord3 → Coord3}
    (hG : AngularPeriodic T G) (hF : AngularPeriodic T F) :
    AngularPeriodic T (torusEndingFluxCorrection d e G F) := by
  apply axialZeroExtension_periodic
  intro n x
  change G (x+angularShift T n)-F (x+angularShift T n)=G x-F x
  rw [hG n x,hF n x]

lemma torusEndingFluxCorrection_divergence {d e : ℝ} (he : 0<e) {G F : Coord3 → Coord3}
    (hG : ContDiff ℝ 1 G) (hF : ContDiffOn ℝ 1 F {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x)
    (hdG : ∀ x,d<x 0 → coordinateDivergence G x=0)
    (hdF : ∀ x,d<x 0 → coordinateDivergence F x=0) (x : Coord3) :
    coordinateDivergence (torusEndingFluxCorrection d e G F) x=0 := by
  apply axialZeroExtension_divergence (by linarith : 0<e/2) _ _ x
  · intro y hy
    change G y-F y=0
    exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)
  · intro y hy
    have hyd : d<y 0 := by linarith
    change coordinateDivergence (fun x => G x-F x) y=0
    rw [coordinateDivergence_sub_at (hG.differentiable (by norm_num) y)
      ((hF.contDiffAt ((axial_halfspace_open d).mem_nhds hyd)).differentiableAt (by norm_num)),
      hdG y hyd,hdF y hyd,sub_self]

lemma torusEndingFluxCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {G F : Coord3 → Coord3} (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingFluxCorrection d e G F=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change G y-F y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {v f : Coord3 → ℝ} (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change v y-f y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingCorrection_terminal {d e : ℝ} {v f : Coord3 → ℝ}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (v-f) :=
  axialZeroExtension_eventually_self (by linarith)

lemma torusEndingFluxCorrection_terminal {d e : ℝ} {G F : Coord3 → Coord3}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingFluxCorrection d e G F=ᶠ[𝓝 x] (G-F) :=
  axialZeroExtension_eventually_self (by linarith)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

structure TorusEndingData (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) where
  d : ℝ
  e : ℝ
  R : ℝ
  d_pos : 0<d
  e_pos : 0<e
  overlap_lt : d+e<R
  w : WeakFiniteTensorPair {x : Coord3 | d<x 0}
  periodic_v : AngularPeriodic (2*Real.pi) w.v
  periodic_E : AngularPeriodic (2*Real.pi) w.E
  initial_v : ∀ x,x 0∈Icc d (d+e) → w.v x=
    ![x 0+torusRealContinuation s (f 0) x,torusRealContinuation s (f 1) x]
  initial_E : ∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s
  terminal_v : ∀ x,R≤x 0 → w.v x=
    ![x 0+(mFourierCoeff (f 0) 0).re,(mFourierCoeff (f 1) 0).re]
  terminal_E : ∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1

theorem torusEndingData_nonempty {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f : Fin 2 → TorusL2) : Nonempty (TorusEndingData s f) := by
  obtain ⟨d,e,R,hd,he,hR,w,hpv,hpE,hvi,hEi,hvt,hEt⟩ := torus_trace_finite_ending hs hres (f 0) (f 1)
  exact ⟨⟨d,e,R,hd,he,hR,w,hpv,hpE,hvi,hEi,hvt,hEt⟩⟩

def normalizedSlope (j : Fin 2) : ℝ := if j=0 then 1 else 0

def torusInitialPair (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) (x : Coord3) : Fin 2 → ℝ :=
  fun j => torusAffineField s (normalizedSlope j) (f j) x

lemma torusInitialPair_eq (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) (x : Coord3) :
    torusInitialPair s f x=![x 0+torusRealContinuation s (f 0) x,torusRealContinuation s (f 1) x] := by
  ext j
  fin_cases j <;> simp [torusInitialPair,torusAffineField,normalizedSlope]

lemma torusInitialPair_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → TorusL2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusInitialPair s f) {x | 0<x 0} := by
  exact contDiffOn_pi.mpr fun j => torusAffineField_smooth hs _ _

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma initial_field (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    z.w.v x=torusInitialPair s f x := by
  rw [z.initial_v x ⟨hx.1.le,hx.2.le⟩,torusInitialPair_eq]

lemma initial_flux
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    (z.w.G x).col j=flatModeFlux s (torusAffineField s (normalizedSlope j) (f j)) x := by
  apply z.w.flux_on_flat_patch (V:={x : Coord3 | x 0∈Ioo z.d (z.d+z.e)})
    (isOpen_Ioo.preimage (continuous_apply 0)) s
    (fun x hx => z.initial_E x ⟨hx.1.le,hx.2.le⟩) (torusInitialPair s f)
    (((torusInitialPair_smooth hs f).of_le (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono (by
      intro y hy
      exact z.d_pos.trans hy.1)) (fun x hx => z.initial_field x hx) j x hx

def correction (j : Fin 2) : Coord3 → ℝ :=
  torusEndingCorrection z.d z.e (fun x => z.w.v x j)
    (torusAffineField s (normalizedSlope j) (f j))

def fluxCorrection (j : Fin 2) : Coord3 → Coord3 :=
  torusEndingFluxCorrection z.d z.e (fun x => (z.w.G x).col j)
    (flatModeFlux s (torusAffineField s (normalizedSlope j) (f j)))

lemma correction_C2
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 2 (z.correction j) := by
  exact torusEndingCorrection_C2 z.e_pos (contDiff_pi.mp z.w.smooth j)
    (((torusAffineField_smooth hs _ _).of_le (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono (fun x hx => z.d_pos.trans hx))
    (fun x hx => congrFun (z.initial_field x hx) j)

lemma correction_periodic (j : Fin 2) : AngularPeriodic (2*Real.pi) (z.correction j) := by
  exact torusEndingCorrection_periodic (fun n x => congrFun (z.periodic_v n x) j)
    (torusAffineField_periodic _ _ _)

lemma fluxCorrection_C1
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 1 (z.fluxCorrection j) := by
  exact torusEndingFluxCorrection_C1 z.e_pos (z.w.component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono (fun x hx => z.d_pos.trans hx)) (fun x hx => z.initial_flux hs j x hx)

lemma fluxCorrection_periodic (j : Fin 2) : AngularPeriodic (2*Real.pi) (z.fluxCorrection j) := by
  exact torusEndingFluxCorrection_periodic
    (fun n x => congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j)
      (z.w.flux_periodic z.periodic_v z.periodic_E n x))
    (flatModeFlux_periodic (torusAffineField_periodic _ _ _))

lemma fluxCorrection_divergence
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) : coordinateDivergence (z.fluxCorrection j) x=0 := by
  exact torusEndingFluxCorrection_divergence z.e_pos (z.w.component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono (fun x hx => z.d_pos.trans hx))
    (fun x hx => z.initial_flux hs j x hx)
    (fun x hx => z.w.flux_divergence (axial_halfspace_open z.d) j x hx)
    (fun x hx => torusAffineField_flux_divergence hs _ _ (z.d_pos.trans hx)) x

end TorusEndingData
end ScalarConductivity

end
end

end OAI
