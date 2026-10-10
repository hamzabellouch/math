import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpinJoinEquiv
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

namespace CoulombAtom

lemma IsWeakDerivative.translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] {v : E} {f g : E → ℂ}
    (hw : IsWeakDerivative v f g) (a : E) :
    IsWeakDerivative v (fun x => f (x+a)) (fun x => g (x+a)) := by
  intro φ hφ hcφ
  let φ' : E → ℝ := fun x => φ (x-a)
  have hφ' : ContDiff ℝ ∞ φ' := hφ.comp (contDiff_id.sub contDiff_const)
  have hcφ' : HasCompactSupport φ' := by
    simpa [φ',Function.comp_def,sub_eq_add_neg] using hcφ.comp_homeomorph (Homeomorph.addRight (-a))
  have hd (x : E) : lineDeriv ℝ φ' (x+a) v = lineDeriv ℝ φ x v := by
    rw [(hφ'.differentiable (by simp) (x+a)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (x+a-a)).hasFDerivAt.comp (x+a)
      ((hasFDerivAt_id (x+a)).sub_const a)
    have hh' := congrArg (fun T : E →L[ℝ] ℝ => T v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,add_sub_cancel_right,φ',Function.comp_def,id_eq] using hh'
  have h1 : (∫ x, f (x+a)*Complex.ofReal (lineDeriv ℝ φ' (x+a) v)) =
      ∫ x, f x*Complex.ofReal (lineDeriv ℝ φ' x v) :=
    (measurePreserving_add_right (volume : Measure E) a).integral_comp
      (Homeomorph.addRight a).measurableEmbedding
      (fun x => f x*Complex.ofReal (lineDeriv ℝ φ' x v))
  have h2 : (∫ x, g (x+a)*(φ' (x+a) : ℂ)) = ∫ x, g x*(φ' x : ℂ) :=
    (measurePreserving_add_right (volume : Measure E) a).integral_comp
      (Homeomorph.addRight a).measurableEmbedding (fun x => g x*(φ' x : ℂ))
  have hh := hw φ' hφ' hcφ'
  rw [←h1,←h2] at hh
  simpa only [hd,φ',add_sub_cancel_right] using hh

lemma shifted_nuclear_integrable {N : ℕ} (i : Fin N) (y : Space)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hw : ∀ a, IsWeakDerivative (direction i a) f (g a)) :
    Integrable (fun x => ‖f x‖^2/‖x i-y‖) := by
  let a : Configuration N := fun _ => y
  have hp := measurePreserving_add_right (volume : Measure (Configuration N)) a
  have hi := nuclear_integrable i (hf.comp_measurePreserving hp)
    (fun b => (hg b).comp_measurePreserving hp) (fun b => (hw b).translate a)
  have hh := ((measurePreserving_add_right (volume : Measure (Configuration N)) (-a)).integrable_comp
    hi.aestronglyMeasurable).2 hi
  simpa only [Function.comp_def,neg_add_cancel_right,Pi.add_apply,Pi.neg_apply,a,sub_eq_add_neg] using hh

lemma SobolevVector.shifted_nuclear_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) (y : Space) :
    Integrable (fun x => ‖ψ.value s x‖^2/‖x i-y‖) :=
  CoulombAtom.shifted_nuclear_integrable i y (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

lemma coreSlice_mass_shifted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (i : Fin M) (y : Space) :
    Integrable (fun u : Configuration M => formMass (coreSlice ψ s u)/‖u i-y‖) := by
  have he (u : Configuration M) : formMass (coreSlice ψ s u)/‖u i-y‖ =
      ∑ t : Spins N, ∫ v : Configuration N,
        ‖ψ.value (joinLists t s) (joinLists v u)‖^2/‖u i-y‖ := by
    simp only [formMass,Finset.sum_div,integral_div,coreSlice]
  simp_rw [he]
  apply integrable_finsetSum
  intro t _
  have hh := (integrable_join (N := N) (M := M)
    (hψ.shifted_nuclear_integrable (joinLists t s) (finSumFinEquiv (Sum.inr i)) y)).integral_prod_right
  simpa only [joinLists_right] using hh

end CoulombAtom

end

end OAI
