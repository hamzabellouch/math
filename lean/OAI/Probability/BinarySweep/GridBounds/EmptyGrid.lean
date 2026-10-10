import Mathlib
import OAI.Probability.BinarySweep.Analytic.ComplexGrid
import OAI.Probability.BinarySweep.Conditional.MomentOperatorBound
import OAI.Probability.BinarySweep.Conditional.MainMomentInterface

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {b : ℕ} (bits : Fin b → ℕ)

def emptyPaths : PathFamily bits 0 where
  position _ k := k.elim0
  disjoint _ := fun k => k.elim0
  changes_only_stage _ k := k.elim0

lemma emptyPaths_event (g : GridChoices bits) : pathEvent (emptyPaths bits) g := by
  intro j k; exact k.elim0

def emptyFree (t : Fin (b+1)) : FreeSlot (emptyPaths bits) t ≃ GridSlot bits where
  toFun := Subtype.val
  invFun x := ⟨x,by rintro ⟨k,_⟩; exact k.elim0⟩
  left_inv _ := rfl
  right_inv _ := rfl

def emptyFrame : Equiv.Perm (GridSlot bits) :=
  (emptyFree bits (Fin.last b)).symm.trans
    ((freeIdentification (emptyPaths bits)).symm.trans (emptyFree bits 0))

lemma emptyPerm (g : GridChoices bits) (hg : pathEvent (emptyPaths bits) g) :
    (emptyFree bits 0).permCongr (remainingPerm (emptyPaths bits) g hg)=
      emptyFrame bits * gridSweep bits g := by
  ext x
  rfl

lemma empty_normalizer (z : ℝ) : conditionalNormalizer (emptyPaths bits) z=1 := by
  simp only [conditionalNormalizer,emptyPaths_event,ite_true,gridWeight_sum]

lemma empty_cost : pathCost (emptyPaths bits)=0 := by
  have hh (j : Fin b) (y : GridOutside bits j) : lineHoles (emptyPaths bits) j y=0 := by
    unfold lineHoles
    exact Fintype.card_eq_zero
  simp [pathCost,hh]

lemma empty_operator {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D))
    (z : ℝ) (x : RepSpace D) :
    conditionalOperator (emptyPaths bits) z
      (ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom) x=
    ρ (emptyFrame bits) (complexGridAverage bits ρ (z:ℂ) x) := by
  rw [conditionalOperator_apply,empty_normalizer]
  simp only [Complex.ofReal_one,inv_one,one_smul,dite_true,emptyPaths_event]
  simp only [complexGridAverage,sum_apply,smul_apply,
    complexGridWeight_real,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ ((emptyFree bits 0).permCongr (remainingPerm _ g _)) x= _
  rw [emptyPerm,map_mul]
  rfl

lemma empty_operator_norm {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D))
    (hρ : IsUnitaryRep ρ) (z : ℝ) :
    ‖conditionalOperator (emptyPaths bits) z
      (ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom)‖=
    ‖complexGridAverage bits ρ (z:ℂ)‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro x
  rw [empty_operator,hρ]

theorem real_grid_bound : ∃ r : ℕ, 0 < r ∧ ∃ q : ℕ, 0 < q ∧
    ∃ a : ℝ, 0 < a ∧ ∀b : ℕ, 1 ≤ b → ∀bits : Fin b → ℕ,
    (∀j, r ≤ bits j ∧ bits j ≤ 2*r) → ∀D : ℕ,
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D),
    ρ.IsIrreducible → IsUnitaryRep ρ → ∀z : ℝ, 0 ≤ z → z ≤ a →
    ‖complexGridAverage bits ρ (z:ℂ)‖ ≤ (D:ℝ)^(-c0/(2*q)) := by
  obtain ⟨r,hr,q,hq,a,ha,h⟩ := conditional_moment_main
  refine ⟨r,hr,q,hq,a,ha,?_⟩
  intro b hb bits hd D ρ hi hρ z hz hza
  let := hi
  let σ : Representation ℂ (Equiv.Perm (FreeSlot (emptyPaths bits) 0)) (RepSpace D) := ρ.comp (emptyFree bits 0).permCongrHom.toMonoidHom
  have hiσ : σ.IsIrreducible := Irrep.irreducible_comp_equiv _ ρ
  have huσ : IsUnitaryRep σ := fun g x => hρ _ x
  have hlog := h b hb bits hd 0 (emptyPaths bits) z hz hza D σ hiσ huσ
  simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero,empty_cost,sub_zero] at hlog
  have hop := opNorm_of_logMoment hq _ hlog
  rw [empty_operator_norm bits ρ hρ z] at hop
  have hD : 0 < D := by
    simpa only [RepSpace,finrank_euclideanSpace,Fintype.card_fin] using
      Signed.irreducible_finrank_pos ρ
  have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
  have hc : c0  ≤  cExponent (gridSize bits) := by
    unfold cExponent
    exact le_add_of_nonneg_right (by positivity)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hqe : 0 < (2:ℝ)*q := by positivity
  have hh : (-cExponent (gridSize bits)*Real.log D)/(2*q) ≤
      (-c0/(2*q))*Real.log D := by
    apply (div_le_iff₀ hqe).mpr
    have := mul_le_mul_of_nonneg_right hc hlogD
    field_simp
    nlinarith
  apply hop.trans
  rw [Real.rpow_def_of_pos hD']
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hh

end BinaryCoordinateSweeps

end

end OAI
