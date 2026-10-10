import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
import OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

lemma annular_inverse_frequency_norm (χ : Character) (X v : ℝ) (hX : 0<X) :
    ‖polynomial χ.inverse false
      (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
      X 0 (2*Real.pi*v)‖=
    ‖polynomial χ false (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v)‖ := by
  rw [actual_log_window]
  have hh := HeckeInverseAmplification.polynomial_inverse_norm χ false
    (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v) hX
  simpa only [Complex.conj_ofReal,neg_mul,neg_neg] using hh

theorem actual_one_rowwise_scales (a b : ℝ) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)
      (s t lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Icc lo hi) → (∀i,ly i∈Icc low high) →
      (∀i,0<s i) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Icc lo hi,∀y∈Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong A n (s i) (t i))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionEnergy.actual_one_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) a b hlog hwindow ha A J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hbound⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P s t lx ly omega Wshort c d lo hi low high E hd hshort hshortsmooth
    hlh hlw hlx hly hspos hE henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i).inverse false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by
      rw [←pow_mul,Nat.mul_comm J 2]
    calc
      _ = ∑i,‖polynomial (χ i) false (fun z : ℝ=>(annulus z:ℂ))
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul,annular_inverse_frequency_norm (χ i) _ v (Real.exp_pos _)]
      _ ≤ (1+2*(hi-lo))*((1+2*(high-low))*(E*(1+‖v‖)^(2*J))) := hh
      _ = _ := by rw [hp];ring
  have hh := hbound (fun i=>(χ i).inverse) χ P s t (fun i=>Real.exp (lx i))
    (fun i=>Real.exp (ly i)) omega Wshort hspos (fun i=>Real.exp_pos _)
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) (mul_nonneg hdx (mul_nonneg hdy hE)) hfixed
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI
