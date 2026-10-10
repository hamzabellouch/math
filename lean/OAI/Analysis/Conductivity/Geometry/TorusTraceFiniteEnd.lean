import Mathlib
import OAI.Analysis.Conductivity.Fourier.UndoAngularProperties
import OAI.Analysis.Conductivity.Geometry.TorusLeadingDecomposition
import OAI.Analysis.Conductivity.Variational.RankProjectionFirst

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

theorem torus_trace_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h)
    (f g : TorusL2) :
    ∃ d e R : ℝ,0<d ∧ 0<e ∧ d+e<R ∧
      ∃ w : WeakFiniteTensorPair {x : Coord3 | d<x 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc d (d+e) → w.v x=
          ![x 0+torusRealContinuation s f x,torusRealContinuation s g x]) ∧
        (∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s) ∧
        (∀ x,R≤x 0 → w.v x=![x 0+(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]) ∧
        (∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  classical
  obtain ⟨ga,hga,hra⟩ := torusRate_uniform_positive hs
  have haf (h : Fin 2 → ℤ) (hh : realTorusAmplitude f h≠0) : ga≤torusRate s h := by
    apply hra h
    intro he
    apply hh
    simp [realTorusAmplitude,he]
  by_cases hg : ∃ h : Fin 2 → ℤ,h≠0 ∧ realTorusCoeff g h≠0
  · obtain ⟨h₀,L,B,gb,b,hh₀,hL,hB,hgb,hb,hrb,heq⟩ :=
      torusRealContinuation_leading_decomposition hs hres g hg
    obtain ⟨d,e,R,hd,he,hdR,w,hvp,hEp,hvi,hEi,hvt,hEt⟩ :=
      original_mode_finite_ending (pa:=realTorusPhase f) (pb:=realTorusPhase g)
        hs hh₀ (norm_nonneg f) hB (realTorusAmplitude_bound f) hb hga hgb haf hrb
    let Q := scaleSecondEquiv L hL.ne'
    let c : Fin 2 → ℝ := ![(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]
    let z := w.output Q c
    refine ⟨d,e,R,hd,he,hdR,z,?_,?_,?_,?_,?_,?_⟩
    · intro n x
      simp only [z,WeakFiniteTensorPair.output_v,hvp n x]
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEp
    · intro x hx
      simp only [z,WeakFiniteTensorPair.output_v,hvi x hx]
      rw [torusRealContinuation_mean_free hs f (hd.trans_le hx.1),heq x (hd.trans_le hx.1)]
      ext i
      fin_cases i <;> simp [Q,c] <;> ring
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEi
    · intro x hx
      simp only [z,WeakFiniteTensorPair.output_v,hvt x hx]
      ext i
      fin_cases i <;> simp [Q,c]
    · simpa only [z,WeakFiniteTensorPair.output_E] using hEt
  · have hgc (h : Fin 2 → ℤ) (hh : h≠0) : realTorusCoeff g h=0 := by
      by_contra hn
      exact hg ⟨h,hh,hn⟩
    have hh₀ : (![1,0] : Fin 2 → ℤ)≠0 := by
      intro hn
      have := congrFun hn 0
      norm_num at this
    obtain ⟨d,e,R,hd,he,hdR,w,hvp,hEp,hvi,hEi,hvt,hEt⟩ :=
      original_mode_finite_ending (pa:=realTorusPhase f) (pb:=fun _ => 0)
        (a:=realTorusAmplitude f) (b:=fun _ => 0) (B:=0) (gb:=1)
        hs hh₀ (norm_nonneg f) le_rfl (realTorusAmplitude_bound f) (by simp)
          hga (by norm_num) haf (by simp)
    let c : Fin 2 → ℝ := ![(mFourierCoeff f 0).re,(mFourierCoeff g 0).re]
    let z := w.projectFirst.output (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ)) c
    have hzv (x : Coord3) : z.v x=![w.v x 0,0]+c := by
      rw [show z.v x= _ from WeakFiniteTensorPair.output_v _ _ _ x]
      rfl
    have hzE : z.E=w.E := by
      rw [show z.E= _ from WeakFiniteTensorPair.output_E _ _ _]
      rfl
    refine ⟨d,e,R,hd,he,hdR,z,?_,?_,?_,?_,?_,?_⟩
    · intro n x
      rw [hzv,hzv,hvp n x]
    · simpa only [hzE] using hEp
    · intro x hx
      rw [hzv,hvi x hx,torusRealContinuation_mean_free hs f (hd.trans_le hx.1),
        torusRealContinuation_constant_of_no_modes hs g hgc (hd.trans_le hx.1)]
      ext i
      fin_cases i <;> simp [c]
      ring
    · simpa only [hzE] using hEi
    · intro x hx
      rw [hzv,hvt x hx]
      ext i
      fin_cases i <;> simp [c]
    · simpa only [hzE] using hEt

end ScalarConductivity

end
end

end OAI
