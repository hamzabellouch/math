import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierPairFlux

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def fourierMatchingCutoff (t : ℝ) : ℝ := 1-smoothTransition ((t-2)/2)

lemma fourierMatchingCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) fourierMatchingCutoff :=
  contDiff_const.sub (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const 2))

lemma fourierMatchingCutoff_left {t : ℝ} (ht : t≤2) : fourierMatchingCutoff t=1 := by
  rw [fourierMatchingCutoff,smoothTransition.zero_of_nonpos (by linarith),sub_zero]

lemma fourierMatchingCutoff_right {t : ℝ} (ht : 4≤t) : fourierMatchingCutoff t=0 := by
  rw [fourierMatchingCutoff,smoothTransition.one_of_one_le (by linarith),sub_self]

def fourierMatchingPair (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (z : ℝ×Coord3) : Fin 2 → ℝ :=
  ![z.2 0+fourierMatchingCutoff (z.2 0)*f z,
    flatPhaseMode s ![0,k] 0 z.2+fourierMatchingCutoff (z.2 0)*g z]

lemma fourierMatchingPair_smooth (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fourierMatchingPair s k f g) := by
  have ht : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ×Coord3 => z.2 0) :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact ht.add ((fourierMatchingCutoff_smooth.comp ht).mul hf)
  · exact ((flatPhaseMode_smooth s ![0,k] 0).comp contDiff_snd).add
      ((fourierMatchingCutoff_smooth.comp ht).mul hg)

lemma fourierMatchingPair_periodic (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hg : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) (p : ℝ) :
    AngularPeriodic (2*Real.pi) (fun x => fourierMatchingPair s k f g (p,x)) := by
  intro n x
  dsimp only [fourierMatchingPair]
  have hfe : f (p,x+angularShift (2*Real.pi) n)=f (p,x) := hf p n x
  have hge : g (p,x+angularShift (2*Real.pi) n)=g (p,x) := hg p n x
  rw [hfe,hge,flatPhaseMode_angularPeriodic s ![0,k] 0 n x]
  have he : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  rw [he]

lemma fourierMatchingPair_base (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ x,f (0,x)=0) (hg : ∀ x,g (0,x)=0) (x : Coord3) :
    fourierMatchingPair s k f g (0,x)=
      ![x 0,pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x)] := by
  simp only [fourierMatchingPair,hf,hg,mul_zero,add_zero,pureWallMode_eq_flatPhaseMode]

lemma fourierMatchingPair_left_nhds (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (p : ℝ) {x : Coord3} (hx : x 0<2) :
    (fun y => fourierMatchingPair s k f g (p,y))=ᶠ[𝓝 x]
      (fun y => ![y 0+f (p,y),flatPhaseMode s ![0,k] 0 y+g (p,y)]) := by
  have hn : ∀ᶠ y in 𝓝 x,y 0<2 := (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hx
  filter_upwards [hn] with y hy
  simp only [fourierMatchingPair,fourierMatchingCutoff_left hy.le,one_mul]

lemma fourierMatchingPair_right_nhds (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (p : ℝ) {x : Coord3} (hx : 4<x 0) :
    (fun y => fourierMatchingPair s k f g (p,y))=ᶠ[𝓝 x]
      (fun y => ![y 0,flatPhaseMode s ![0,k] 0 y]) := by
  have hn : ∀ᶠ y in 𝓝 x,4<y 0 := (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx
  filter_upwards [hn] with y hy
  simp only [fourierMatchingPair,fourierMatchingCutoff_right hy.le,zero_mul,add_zero]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def fourierResidualCutoff (t : ℝ) : ℝ := smoothTransition (t-1)*smoothTransition (5-t)
lemma fourierResidualCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) fourierResidualCutoff :=
  (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
lemma fourierResidualCutoff_one {t : ℝ} (ht : t∈Icc 2 4) : fourierResidualCutoff t=1 := by
  rw [fourierResidualCutoff,smoothTransition.one_of_one_le (by linarith [ht.1]),
    smoothTransition.one_of_one_le (by linarith [ht.2]),mul_one]
lemma fourierResidualCutoff_zero_left {t : ℝ} (ht : t≤1) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (by linarith),zero_mul]
lemma fourierResidualCutoff_zero_right {t : ℝ} (ht : 5≤t) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (show 5-t≤0 by linarith),mul_zero]

def fourierMatchingResidual (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (j : Fin 2) (z : ℝ×Coord3) : ℝ :=
  -fourierResidualCutoff (z.2 0)*symmetricSource (fun _ => flatBackgroundTensor s)
    (fun x => fourierMatchingPair s k f g (z.1,x)) j z.2

lemma fourierMatchingResidual_smooth (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) (j : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fourierMatchingResidual s k f g j) := by
  have hr := symmetricSource_parametric_smoothOn (V:=univ) isOpen_univ
    (H:=fun _ : ℝ×Coord3 => flatBackgroundTensor s) contDiffOn_const
    (fourierMatchingPair_smooth s k hf hg).contDiffOn j
  rw [contDiffOn_univ] at hr
  exact ((fourierResidualCutoff_smooth.comp
    ((contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd)).neg).mul hr

lemma fourierMatchingResidual_periodic (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hg : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) (p : ℝ) (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (fun x => fourierMatchingResidual s k f g j (p,x)) := by
  intro n x
  have he := symmetricSource_angular_translate (fourierMatchingPair_periodic s k hf hg p)
    (fun _ => flatBackgroundTensor s) j n x
  dsimp only [fourierMatchingResidual]
  rw [←he]
  simp only [Pi.add_apply,angularShift,Matrix.cons_val_zero,add_zero]

lemma fourierMatchingResidual_support (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (p : ℝ) (j : Fin 2) :
    tsupport (fun x => fourierMatchingResidual s k f g j (p,x))⊆{x | x 0∈Icc 1 5} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 0))
  intro x hx
  constructor
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_left (le_of_not_ge hh),neg_zero,zero_mul])
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_right (le_of_not_ge hh),neg_zero,zero_mul])

lemma flatPurePair_source_zero {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (k : ℤ) (j : Fin 2) (x : Coord3) :
    symmetricSource (fun _ => flatBackgroundTensor s) (fun y => ![y 0,flatPhaseMode s ![0,k] 0 y]) j x=0 := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => ![y 0,flatPhaseMode s ![0,k] 0 y]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact contDiff_apply ℝ ℝ 0
    · exact flatPhaseMode_smooth s ![0,k] 0
  rw [flatBackgroundTensor_source hu]
  fin_cases j
  · change flatTensorLaplacian s (fun y : Coord3 => y 0) x=0
    simpa only [one_mul,add_zero] using flatTensorLaplacian_axial_affine s 1 0 x
  · exact flatPhaseMode_harmonic hs ![0,k] 0 x

lemma fourierMatchingResidual_base {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} (hf : ∀ x,f (0,x)=0) (hg : ∀ x,g (0,x)=0)
    (j : Fin 2) (x : Coord3) : fourierMatchingResidual s k f g j (0,x)=0 := by
  have he : (fun y => fourierMatchingPair s k f g (0,y))=
      (fun y => ![y 0,flatPhaseMode s ![0,k] 0 y]) := by
    funext y
    simp only [fourierMatchingPair,hf,hg,mul_zero,add_zero]
  unfold fourierMatchingResidual
  rw [he,flatPurePair_source_zero hs,mul_zero]

end ScalarConductivity

end

end OAI
