import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! The closed energy space of one Dirichlet cusp mode, constructed from
compactly supported test functions. No differential inverse is assumed. -/
noncomputable section
open MeasureTheory Function
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaRadialTests : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f ∧ ∀ t ≤ 0, f t=0}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero,by simp⟩
  add_mem' := by
    rintro f g ⟨hf,hfc,hfz⟩ ⟨hg,hgc,hgz⟩
    exact ⟨hf.add hg,hfc.add hgc,fun t ht => by simp [hfz t ht,hgz t ht]⟩
  smul_mem' := by
    rintro c f ⟨hf,hfc,hfz⟩
    exact ⟨hf.const_smul c,hfc.smul_left,fun t ht => by simp [hfz t ht]⟩

abbrev CubicThetaRadialJet := EuclideanSpace ℂ (Fin 3)
abbrev CubicThetaRadialAmbient := Lp CubicThetaRadialJet 2 (volume : Measure ℝ)

def cubicThetaRadialJet (A : ℝ) (f : ℝ → ℂ) (t : ℝ) : CubicThetaRadialJet :=
  WithLp.toLp 2 ![f t,deriv f t,(Real.sqrt A*Real.exp t:ℝ) • f t]

lemma cubicThetaRadialJet_continuous (A : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (cubicThetaRadialJet A f) := by
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using hf.continuous
  · simpa using hf.continuous_deriv le_rfl
  · change Continuous (fun t : ℝ => (Real.sqrt A*Real.exp t:ℝ) • f t)
    exact (continuous_const.mul Real.continuous_exp).smul hf.continuous

lemma cubicThetaRadialJet_compact (A : ℝ) {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (cubicThetaRadialJet A f) := by
  apply hc.mono'
  intro t ht
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  have hd := deriv_of_notMem_tsupport hn
  apply ht
  ext i
  fin_cases i <;> simp [cubicThetaRadialJet,hz,hd]

lemma cubicThetaRadialJet_memLp (A : ℝ) (f : cubicThetaRadialTests) :
    MemLp (cubicThetaRadialJet A f) 2 (volume : Measure ℝ) :=
  (cubicThetaRadialJet_continuous A f.property.1).memLp_of_hasCompactSupport
    (cubicThetaRadialJet_compact A f.property.2.1)

def cubicThetaRadialGraph (A : ℝ) : cubicThetaRadialTests →ₗ[ℂ] CubicThetaRadialAmbient where
  toFun f := (cubicThetaRadialJet_memLp A f).toLp (cubicThetaRadialJet A f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cubicThetaRadialJet_memLp A (f+g)).coeFn_toLp,
      (cubicThetaRadialJet_memLp A f).coeFn_toLp,
      (cubicThetaRadialJet_memLp A g).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaRadialJet_memLp A f).toLp _) ((cubicThetaRadialJet_memLp A g).toLp _)]
      with t hfg hf hg hs
    simp only [Pi.add_apply] at hs
    rw [hfg,hs,hf,hg]
    ext i
    fin_cases i
    · rfl
    · exact deriv_add (f.property.1.differentiable (by norm_num) t)
        (g.property.1.differentiable (by norm_num) t)
    · simp [cubicThetaRadialJet,smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cubicThetaRadialJet_memLp A (c • f)).coeFn_toLp,
      (cubicThetaRadialJet_memLp A f).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaRadialJet_memLp A f).toLp _)] with t hcf hf hs
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hs
    rw [hcf,hs,hf]
    ext i
    fin_cases i
    · rfl
    · change deriv (fun t => c*(f:ℝ → ℂ) t) t=c*deriv (f:ℝ → ℂ) t
      exact deriv_const_mul_field _
    · simp [cubicThetaRadialJet]
      ring

def cubicThetaRadialEnergySpace (A : ℝ) : Submodule ℂ CubicThetaRadialAmbient :=
  (cubicThetaRadialGraph A).range.topologicalClosure

instance cubicThetaRadialEnergy_complete (A : ℝ) :
    CompleteSpace (cubicThetaRadialEnergySpace A) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaRadialEnergyTest (A : ℝ) (f : cubicThetaRadialTests) :
    cubicThetaRadialEnergySpace A :=
  ⟨cubicThetaRadialGraph A f,Submodule.le_topologicalClosure _ ⟨f,rfl⟩⟩

end CubicFirstMoment

end

end OAI
