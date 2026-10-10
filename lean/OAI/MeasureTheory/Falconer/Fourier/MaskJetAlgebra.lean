import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace OAI

/-! # Finite algebra of individual ambient mask jets

A term contains each original mask exactly once, evaluated at one smooth
angular chart point, with a fixed finite jet on each occurrence. The
coefficient contains only the fixed chart geometry. Differentiation can
therefore distribute to one mask without deleting any other occurrence.
-/

namespace Falconer
open Set
open scoped ContDiff

structure MaskJetIndex (d : ℕ) where
  order : ℕ
  vectors : Fin order → Space d
  norm_vectors : ∀ i, ‖vectors i‖ ≤ 1

namespace MaskJetIndex

noncomputable def zero (d : ℕ) : MaskJetIndex d :=
  ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩

noncomputable def prepend {d : ℕ} (j : MaskJetIndex d) (v : Space d) (hv : ‖v‖ ≤ 1) :
    MaskJetIndex d :=
  ⟨j.order+1,Fin.cons v j.vectors,by intro i; refine Fin.cases hv (fun i => ?_) i; exact j.norm_vectors i⟩

noncomputable def value {d : ℕ} (j : MaskJetIndex d) (B : Space d → ℂ) (z : Space d) : ℂ :=
  iteratedFDeriv ℝ j.order B z j.vectors

@[simp] theorem zero_value (d : ℕ) (B : Space d → ℂ) (z : Space d) :
    (zero d).value B z = B z := rfl

theorem value_contDiff {d : ℕ} (j : MaskJetIndex d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (j.value B) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j.order => Space d) ℂ j.vectors).contDiff.comp
    (hB.iteratedFDeriv_right (by simp))

theorem fderiv_value {d : ℕ} (j : MaskJetIndex d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) (z v : Space d) (hv : ‖v‖ ≤ 1) :
    fderiv ℝ (j.value B) z v = (j.prepend v hv).value B z := by
  have hd := (hB.iteratedFDeriv_right (by simp : (∞ : ℕ∞ω)+j.order ≤ ∞)).differentiable
    (by simp)
  change fderiv ℝ (fun y => iteratedFDeriv ℝ j.order B y j.vectors) z v = _
  rw [fderiv_continuousMultilinear_apply_const_apply (hd z)]
  rfl

end MaskJetIndex

theorem complex_clm_coordinate_expansion {d : ℕ} (L : Space d →L[ℝ] ℂ) (z : Space d) :
    L z = ∑ i : Fin d, (z i : ℂ)*L ((EuclideanSpace.basisFun (Fin d) ℝ) i) := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr z)
  simpa only [map_sum,map_smul,OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr,smul_eq_mul,
    Complex.real_smul] using h.symm

theorem MaskJetIndex.fderiv_comp {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : MaskJetIndex d) {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B)
    {g : E → Space d} (hg : ContDiff ℝ ∞ g) (z v : E) :
    fderiv ℝ (fun u => j.value B (g u)) z v =
      ∑ i : Fin d, ((fderiv ℝ g z v) i : ℂ)*
        (j.prepend ((EuclideanSpace.basisFun (Fin d) ℝ) i)
          (by simp)).value B (g z) := by
  change fderiv ℝ (j.value B ∘ g) z v = _
  rw [_root_.fderiv_comp z ((j.value_contDiff hB).differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  change fderiv ℝ (j.value B) (g z) (fderiv ℝ g z v) = _
  rw [complex_clm_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [j.fderiv_value hB (g z) _ (by simp)]

structure MaskJetTerm (ι : Type*) (d : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  coefficient : E → ℂ
  point : E → Space d
  jet : ι → MaskJetIndex d
  coefficient_smooth : ContDiff ℝ ∞ coefficient
  point_smooth : ContDiff ℝ ∞ point

namespace MaskJetTerm
variable {ι X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def value (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ)
    (x : X) (z : E) : ℂ :=
  T.coefficient z * ∏ i, (T.jet i).value (B i x) (T.point z)

def order (T : MaskJetTerm ι d E) : ℕ := ∑ i, (T.jet i).order

theorem value_contDiff (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) : ContDiff ℝ ∞ (T.value B x) :=
  T.coefficient_smooth.mul (contDiff_prod (fun i _ =>
    ((T.jet i).value_contDiff (hB i x)).comp T.point_smooth))

noncomputable def mulFixed (T : MaskJetTerm ι d E) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    MaskJetTerm ι d E :=
  ⟨fun z => c z*T.coefficient z,T.point,T.jet,hc.mul T.coefficient_smooth,T.point_smooth⟩

@[simp] theorem mulFixed_value (T : MaskJetTerm ι d E) (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (T.mulFixed c hc).value B x z = c z*T.value B x z := by
  simp only [value,mulFixed,mul_assoc]

noncomputable def pullback (T : MaskJetTerm ι d E) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    MaskJetTerm ι d H :=
  ⟨T.coefficient ∘ g,T.point ∘ g,T.jet,T.coefficient_smooth.comp hg,T.point_smooth.comp hg⟩

@[simp] theorem pullback_value (T : MaskJetTerm ι d E) (g : H → E) (hg : ContDiff ℝ ∞ g)
    (B : ι → X → Space d → ℂ) (x : X) (z : H) :
    (T.pullback g hg).value B x z = T.value B x (g z) := rfl

noncomputable def derivativeTerm [DecidableEq ι] (T : MaskJetTerm ι d E)
    (v : E) : Unit ⊕ (ι × Fin d) → MaskJetTerm ι d E
  | .inl _ =>
    ⟨fun z => fderiv ℝ T.coefficient z v,T.point,T.jet,
      (T.coefficient_smooth.fderiv_right (by simp)).clm_apply contDiff_const,T.point_smooth⟩
  | .inr (i,j) =>
    ⟨fun z => T.coefficient z*((fderiv ℝ T.point z v) j : ℂ),T.point,
      Function.update T.jet i ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j)
        (by simp)),
      T.coefficient_smooth.mul (Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj 2 (fun _ : Fin d => ℝ) j).contDiff.comp
          ((T.point_smooth.fderiv_right (by simp)).clm_apply contDiff_const))),T.point_smooth⟩

theorem derivativeTerm_order [DecidableEq ι] (T : MaskJetTerm ι d E) (v : E)
    (a : Unit ⊕ (ι × Fin d)) : (T.derivativeTerm v a).order ≤ T.order+1 := by
  rcases a with a | ⟨i,j⟩
  · exact Nat.le_succ _
  · have he : (fun l => ((Function.update T.jet i
        ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp))) l).order) =
        Function.update (fun l => (T.jet l).order) i ((T.jet i).order+1) := by
      funext l
      by_cases hl : l = i
      · subst l; simp [MaskJetIndex.prepend]
      · simp [Function.update_of_ne hl]
    change (∑ l, ((Function.update T.jet i _ l)).order) ≤ (∑ l, (T.jet l).order)+1
    rw [he,Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
    have hs := Finset.add_sum_erase Finset.univ (fun l => (T.jet l).order) (Finset.mem_univ i)
    omega

private theorem fderiv_product [DecidableEq ι] (f : ι → E → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (z v : E) :
    fderiv ℝ (fun z => ∏ i, f i z) z v =
      ∑ i, (∏ j ∈ Finset.univ.erase i, f j z)*fderiv ℝ (f i) z v := by
  have he := congrArg (fun L : E →L[ℝ] ℂ => L v)
    (fderiv_finsetProd (u := Finset.univ) (x := z)
      (fun i _ => ((hf i).differentiable (by simp)).differentiableAt))
  simpa only [sum_apply,smul_apply,smul_eq_mul] using he

private theorem derivativeTerm_value_right [DecidableEq ι]
    (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ) (v : E)
    (i : ι) (j : Fin d) (x : X) (z : E) :
    (T.derivativeTerm v (.inr (i,j))).value B x z =
      T.coefficient z*((fderiv ℝ T.point z v) j : ℂ)*
      ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp)).value
        (B i x) (T.point z)*
      ∏ l ∈ Finset.univ.erase i, (T.jet l).value (B l x) (T.point z) := by
  have he : (fun l => ((Function.update T.jet i
      ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp))) l).value
        (B l x) (T.point z)) =
      Function.update (fun l => (T.jet l).value (B l x) (T.point z)) i
        (((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j) (by simp)).value
          (B i x) (T.point z)) := by
    funext l
    by_cases hl : l = i
    · subst l; simp
    · simp [Function.update_of_ne hl]
  dsimp only [derivativeTerm]
  change (T.coefficient z*((fderiv ℝ T.point z v) j : ℂ))*_ = _
  rw [he,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
  ring

theorem derivative_value [DecidableEq ι] (T : MaskJetTerm ι d E)
    (B : ι → X → Space d → ℂ) (hB : ∀ i x, ContDiff ℝ ∞ (B i x))
    (v : E) (x : X) (z : E) :
    ∑ a : Unit ⊕ (ι × Fin d), (T.derivativeTerm v a).value B x z =
      fderiv ℝ (T.value B x) z v := by
  let f : ι → E → ℂ := fun i z => (T.jet i).value (B i x) (T.point z)
  have hf (i : ι) : ContDiff ℝ ∞ (f i) :=
    ((T.jet i).value_contDiff (hB i x)).comp T.point_smooth
  have hprod : ContDiff ℝ ∞ (fun z => ∏ i, f i z) := contDiff_prod (fun i _ => hf i)
  change _ = fderiv ℝ (fun z => T.coefficient z*∏ i, f i z) z v
  rw [fderiv_fun_mul (T.coefficient_smooth.differentiable (by simp)).differentiableAt
    (hprod.differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul,Fintype.sum_sum_type,Fintype.sum_unique,
    Fintype.sum_prod_type]
  rw [fderiv_product f hf z v]
  change (fderiv ℝ T.coefficient z v)*(∏ i, f i z)+_ = _
  have hsum : (∑ i : ι, ∑ j : Fin d,
      (T.derivativeTerm v (.inr (i,j))).value B x z) =
      T.coefficient z*∑ i, (∏ l ∈ Finset.univ.erase i, f l z)*fderiv ℝ (f i) z v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MaskJetIndex.fderiv_comp (T.jet i) (hB i x) T.point_smooth z v]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [derivativeTerm_value_right]
    dsimp only [f]
    ring
  rw [hsum]
  ring

end MaskJetTerm
end Falconer

end OAI
