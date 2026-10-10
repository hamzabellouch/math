import OAI.NumberTheory.DirichletL.Detector.GaussianLogWindow

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0<R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0<R)
    (hactive : (∏i,W i (y i))≠0→V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i y≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤T := Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact FourierBridge.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end SevenEighths.ProbePhysical
end

end OAI
