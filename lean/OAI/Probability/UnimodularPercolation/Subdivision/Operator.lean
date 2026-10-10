import Mathlib
import OAI.Probability.UnimodularPercolation.Subdivision.Coupling

namespace OAI

/-! Operator bounds transferred through graph subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal

private theorem sum_inl_extend_le (f : Hilbert V) (s : Finset (V ⊕ E)) :
    ∑ z ∈ s, ‖Sum.elim (fun x => f x) (fun _ : E => (0:ℂ)) z‖ ^ (2:ℝ≥0∞).toReal ≤
      ‖f‖ ^ (2:ℝ≥0∞).toReal := by
  classical
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  simp only [Sum.elim_inl,Sum.elim_inr,norm_zero,ENNReal.toReal_ofNat,Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0),
    Finset.sum_const_zero,add_zero]
  exact lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) f s.toLeft

noncomputable def hilbertInlValue (f : Hilbert V) : Hilbert (V ⊕ E) :=
  ⟨Sum.elim (fun x => f x) (fun _ => 0),memℓp_gen' (sum_inl_extend_le f)⟩

theorem norm_hilbertInlValue_le (f : Hilbert V) : ‖hilbertInlValue (E:=E) f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg f) (sum_inl_extend_le f)

noncomputable def hilbertInl : Hilbert V →L[ℂ] Hilbert (V ⊕ E) :=
  LinearMap.mkContinuous
    { toFun := hilbertInlValue
      map_add' := by
        intro f g
        apply lp.ext
        funext z
        cases z with
        | inl x => rfl
        | inr e => change (0:ℂ) = 0+0; simp
      map_smul' := by
        intro c f
        apply lp.ext
        funext z
        cases z with
        | inl x => rfl
        | inr e => change (0:ℂ) = c • 0; simp }
    1 (fun f => by simpa using norm_hilbertInlValue_le (E:=E) f)

@[simp] theorem hilbertInl_apply_inl (f : Hilbert V) (x : V) :
    hilbertInl (E:=E) f (.inl x) = f x := rfl
@[simp] theorem hilbertInl_apply_inr (f : Hilbert V) (e : E) :
    hilbertInl (E:=E) f (.inr e) = 0 := rfl

private theorem sum_inl_restrict_le (f : Hilbert (V ⊕ E)) (s : Finset V) :
    ∑ x ∈ s, ‖f (.inl x)‖ ^ (2:ℝ≥0∞).toReal ≤ ‖f‖ ^ (2:ℝ≥0∞).toReal := by
  classical
  rw [←Finset.sum_image (f := fun z => ‖f z‖ ^ (2:ℝ≥0∞).toReal) Sum.inl_injective.injOn]
  exact lp.sum_rpow_le_norm_rpow (by norm_num) f _

noncomputable def hilbertRestrictInlValue (f : Hilbert (V ⊕ E)) : Hilbert V :=
  ⟨fun x => f (.inl x),memℓp_gen' (sum_inl_restrict_le f)⟩

theorem norm_hilbertRestrictInlValue_le (f : Hilbert (V ⊕ E)) :
    ‖hilbertRestrictInlValue f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg f) (sum_inl_restrict_le f)

noncomputable def hilbertRestrictInl : Hilbert (V ⊕ E) →L[ℂ] Hilbert V :=
  LinearMap.mkContinuous
    { toFun := hilbertRestrictInlValue
      map_add' := by intro f g; apply lp.ext; rfl
      map_smul' := by intro c f; apply lp.ext; rfl }
    1 (fun f => by simpa using norm_hilbertRestrictInlValue_le f)

@[simp] theorem hilbertRestrictInl_apply (f : Hilbert (V ⊕ E)) (x : V) :
    hilbertRestrictInl f x = f (.inl x) := rfl

@[simp] theorem hilbertInl_single [DecidableEq V] [DecidableEq E] (x : V) (c : ℂ) :
    hilbertInl (E:=E) (lp.single 2 x c) = lp.single 2 (.inl x) c := by
  apply lp.ext
  funext z
  cases z <;> simp [lp.single_apply,Pi.single_apply]

 
theorem operatorBounded_of_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval) (h : OperatorBounded (subdivision G) q) :
    OperatorBounded G (q^2) := by
  classical
  obtain ⟨A,hA⟩ := h
  refine ⟨hilbertRestrictInl ∘L A ∘L hilbertInl,?_⟩
  intro x y
  simp only [ContinuousLinearMap.comp_apply,hilbertInl_single,hilbertRestrictInl_apply]
  convert (hA (.inl x) (.inl y)).trans (congrArg (fun r : ℝ => (r:ℂ))
    (twoPoint_subdivision G q x y)) using 1
  apply congrArg (fun f : Hilbert (V ⊕ E) => A f (.inl x))
  apply lp.ext
  funext z
  simp [lp.single_apply,Pi.single_apply]

 

theorem critical_bounded_of_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    (h : OperatorBounded (subdivision G) (pc (subdivision G))) :
    OperatorBounded G (pc G) := by
  simpa only [pc_subdivision_sq G hloc] using
    operatorBounded_of_subdivision G (pc (subdivision G)) h

end Percolation

end OAI
