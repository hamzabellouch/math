import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ConcreteFluxH1Scalarization
import OAI.Analysis.Conductivity.Fourier.AngularPhaseTranslation

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

local instance generalModeEndingScalarizationMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance generalModeEndingScalarizationBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma flatFourier_div_coefficients (s : Fin 3 → ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (d : ℝ) (x : Coord3) :
    flatFourier s (fun h => a h/d) phase x=flatFourier s a phase x/d := by
  unfold flatFourier
  simp_rw [div_mul_eq_mul_div]
  exact tsum_div_const

lemma normalizedFourierCoefficients_div (s : Fin 3 → ℝ) (lam T d : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) :
    normalizedFourierCoefficients s lam T (fun h => a h/d)=
      fun h => normalizedFourierCoefficients s lam T a h/d := by
  funext h
  unfold normalizedFourierCoefficients
  ring

lemma normalized_flatFourier_angular_conjugacy (s : Fin 3 → ℝ)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (a phase : (Fin 2 → ℤ) → ℝ) (lam T : ℝ) (θ : Fin 2 → ℝ) (x : Coord3) :
    flatFourier (normalizedAngularTensor s A)
      (normalizedFourierCoefficients (normalizedAngularTensor s A)
        (Real.sqrt (angularNormalization A)*lam) T
        (a ∘ (angularFrequencyEquiv A hA).symm))
      (angularShiftPhase (phase ∘ (angularFrequencyEquiv A hA).symm) θ) x=
    flatFourier s (normalizedFourierCoefficients s lam
      (Real.sqrt (angularNormalization A)*T) a) phase
      (angularNormalizedLift A (angularRealTranslation θ x)) := by
  rw [flatFourier_angular_conjugacy s hA,flatFourier_angular_translation]
  congr 1
  funext h
  obtain ⟨g,rfl⟩ := (angularFrequencyEquiv A hA).surjective h
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using
    normalizedFourierCoefficients_angular_conjugacy s hA a lam T g

theorem general_mode_ending_H1_scalarization {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (k : ℤ),
      Q.det=1 ∧ 0<k ∧ h₀ ᵥ* Q=![0,k] ∧
      ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0<c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3)
        (hsym : ∀ x,(E x).IsSymm),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (Real.sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/Real.sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (Real.sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        ∀ (U : Set Coord3),IsOpen U → Bornology.IsBounded U → U⊆{x : Coord3 | 0<x 0} →
          ∃ (hu : MemLp v 2 (volume.restrict U))
            (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
            (hF : MemLp (voltageFlux v (fun y => ⟨E y,hsym y⟩)) 2 (volume.restrict U))
            (z : voltageH1Jets volume U) (F : Lp FieldVector 2 (volume.restrict U)) (σ : Coord3 → ℝ),
            Measurable σ ∧ MemLp σ ∞ (volume.restrict U) ∧
            z.val-(hu.toLp _,hE.toLp _)∈zeroVoltageJets volume U ∧
            (∀ᵐ x ∂volume.restrict U,σ x∈Icc (laminateLower c C) (laminateUpper C) ∧
              F x=σ x • (z.val.2 x)) ∧
            (∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 (hF.toLp _)) ∧
            (∀ W : zeroVoltageJets volume U,inner ℝ W.val.2 F=0) := by
  obtain ⟨k,Q,hk,hQ,he⟩ := leading_frequency_SL2_alignment hh₀
  let m := Real.sqrt (angularNormalization Q)
  have hm : 0 < m := Real.sqrt_pos.mpr (angularNormalization_pos Q)
  let e := angularFrequencyEquiv Q hQ
  let θ : Fin 2 → ℝ := ![0,-pb h₀/(k:ℝ)]
  let a' : (Fin 2 → ℤ) → ℝ := fun h => a (e.symm h)/m
  let b' : (Fin 2 → ℤ) → ℝ := b ∘ e.symm
  let pa' := angularShiftPhase (pa ∘ e.symm) θ
  let pb' := angularShiftPhase (pb ∘ e.symm) θ
  have hphase : pb' ![0,k]=0 := by
    have he0 : e.symm ![0,k]=h₀ := by
      rw [←he]
      exact e.symm_apply_apply h₀
    dsimp [pb',angularShiftPhase]
    rw [he0]
    exact alignedPhaseTranslation_zero hk (pb h₀)
  have hmode (x : Coord3) :
      flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))=
      flatPhaseMode (normalizedAngularTensor s Q) ![0,k] 0 x := by
    rw [flatPhaseMode_angular_conjugacy s hQ,he,flatPhaseMode_angular_translation]
    rw [show pb h₀+((![0,k] : Fin 2 → ℤ) 0:ℝ)*θ 0+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*θ 1=0 from alignedPhaseTranslation_zero hk (pb h₀)]
  have hab : ∀ h,|a' h|≤A/m := by
    intro h
    dsimp [a']
    rw [abs_div,abs_of_pos hm]
    exact (div_le_div_iff_of_pos_right hm).2 (ha _)
  have hbb : ∀ h,|b' h|≤B := fun h => hb (e.symm h)
  have hgapA := angular_conjugacy_gap s hQ (a:=a) (lam:=0) hga
    (fun h hh => by simpa only [zero_add] using hra h hh)
  have hgapB := angular_conjugacy_gap s hQ hgb hrb
  have hrate : torusRate (normalizedAngularTensor s Q) ![0,k]=m*torusRate s h₀ := by
    rw [←he,torusRate_angular_conjugacy s hQ]
  have hra' : ∀ h,a' h≠0 → m*ga≤torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    have hh' : (a ∘ e.symm) h≠0 := by
      intro hz
      apply hh
      dsimp [a']
      rw [show a (e.symm h)=0 from hz,zero_div]
    simpa only [mul_zero,zero_add] using hgapA.2 h hh'
  have hrb' : ∀ h,b' h≠0 → torusRate (normalizedAngularTensor s Q) ![0,k]+m*gb≤
      torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    rw [hrate]
    exact hgapB.2 h hh
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,hscalar⟩ :=
    aligned_fourier_ending_H1_scalarization (pa:=pa')
      (normalizedAngularTensor_lower hs hQ) hk (div_nonneg hA hm.le) hB hab hbb
      (mul_pos hm hga) (mul_pos hm hgb) hra' hrb' hphase hδ
  refine ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,?_,hEin,hterm,hscalar⟩
  intro x hx
  rw [hvin x hx,hmode]
  congr 1
  · congr 1
    rw [normalizedFourierCoefficients_div,flatFourier_div_coefficients]
    congr 1
    simpa only [pa',e,Function.comp_def,mul_zero] using normalized_flatFourier_angular_conjugacy s hQ a pa 0 (10+1/p) θ x
  · rw [hrate]
    congr 2
    simpa only [b',pb',m,e,Function.comp_apply] using normalized_flatFourier_angular_conjugacy s hQ b pb (torusRate s h₀) (10+1/p) θ x

end ScalarConductivity

end
end

end OAI
