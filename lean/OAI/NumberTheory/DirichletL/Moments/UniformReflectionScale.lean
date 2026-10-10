import OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile
import OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentUniformReflectionScale
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy CenteredMomentUniformReflectionProfile
open CenteredMomentReflectedNormalization

theorem actual_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0<s i) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=actual_inverse_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound G χ (fun i=>polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=>Real.exp (lx i)) hspos (fun i=>Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert hh using 1

end SevenEighths.CenteredMomentUniformReflectionScale

end

end OAI
