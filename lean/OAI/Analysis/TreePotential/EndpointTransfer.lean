import OAI.Analysis.TreePotential.RealModuli

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
section RealEndpointTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma averagedModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ averagedModulus E t) : a≤ averagedModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [averagedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]

lemma maximumModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ maximumModulus E t) : a≤ maximumModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [maximumModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]

lemma oneSidedModulusReal_zero (h : ¬IsAUC E) {t : ℝ}
    (ht : oneSidedModulus E t=0) : oneSidedModulusReal E t=0 := by
  apply EReal.coe_eq_coe_iff.mp
  rw [oneSidedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h),ht]
  rfl
end RealEndpointTransfer

namespace TreeCalculus

theorem four_averaged_modulus_real (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    Real.sqrt (1+t^2/4)-1≤ averagedModulusReal (TestCompletion (treeTestFamily r k)) t :=
  averagedModulusReal_lower (four_no_equivalent_AUC r k (.refl ℝ _)) (four_averaged_modulus r k ht ht1)

theorem four_renorming_obstruction_real (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β)
    (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (four_no_equivalent_AUC r k e) (four_renorming_obstruction r k e hα hαβ he)

theorem four_no_equivalent_AUC_real (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (four_no_equivalent_AUC r k e)
end TreeCalculus

namespace FreeRoot

theorem freeRoot_averaged_modulus_real {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    (Real.sqrt (1+t^2/576)-1)/4≤ averagedModulusReal Space t :=
  averagedModulusReal_lower (freeRoot_no_equivalent_AUC (.refl ℝ _)) (freeRoot_averaged_modulus ht ht1)

theorem freeRoot_renorming_obstruction_real {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) {α β : ℝ} (hα : 0<α) (hαβ : α≤β)
    (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(4*β))=0 :=
  oneSidedModulusReal_zero (freeRoot_no_equivalent_AUC e) (freeRoot_renorming_obstruction e hα hαβ he)

theorem freeRoot_no_equivalent_AUC_real {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (freeRoot_no_equivalent_AUC e)
end FreeRoot

section CostRealObstructions
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem linearOuter_renorming_obstruction_real (e : LinearOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖)
    (ht : 0< t) (htb : t≤α/β) : oneSidedModulusReal Y t=0 :=
  oneSidedModulusReal_zero (linearOuter_no_equivalent_AUC e)
    (linearOuter_renorming_obstruction e hα hαβ he ht htb)

theorem quadraticOuter_renorming_obstruction_real (e : QuadraticOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖)
    (ht : 0< t) (htb : t≤α/(Real.sqrt 2*β)) : oneSidedModulusReal Y t=0 :=
  oneSidedModulusReal_zero (quadraticOuter_no_equivalent_AUC e)
    (quadraticOuter_renorming_obstruction e hα hαβ he ht htb)

theorem linearOuter_no_equivalent_AUC_real (e : LinearOuter ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (linearOuter_no_equivalent_AUC e)

theorem quadraticOuter_no_equivalent_AUC_real (e : QuadraticOuter ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (quadraticOuter_no_equivalent_AUC e)
end CostRealObstructions

namespace CostHeads

theorem linear_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal LinearOuter t :=
  averagedModulusReal_lower (linearOuter_no_equivalent_AUC (.refl ℝ _)) (linear_averaged_modulus ht)

theorem quadratic_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal QuadraticOuter t :=
  averagedModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_averaged_modulus ht)

theorem quadratic_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ maximumModulusReal QuadraticOuter t :=
  maximumModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_maximum_modulus ht)

theorem quadratic_maximum_modulus_real_positive {t : ℝ} (ht : 0< t) :
    0< maximumModulusReal QuadraticOuter t := by
  apply EReal.coe_lt_coe_iff.mp
  rw [maximumModulusReal_coe QuadraticOuter
    (infiniteDimensional_of_not_isAUC _ (quadraticOuter_no_equivalent_AUC (.refl ℝ _)))]
  exact quadratic_maximum_modulus_positive ht
end CostHeads

namespace Segments

theorem start_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/64)-1≤ maximumModulusReal StartSpace t :=
  maximumModulusReal_lower (start_no_equivalent_AUC (.refl ℝ _)) (start_maximum_modulus ht)

theorem start_unit_sphere_bound_real (x : StartSpace) (hx : ‖x‖=1)
    {t ε : ℝ} (ht : 0< t) (hε : 0<ε) :
    ∃ F : ClosedFiniteCodim StartSpace,
      Real.sqrt (1+t^2/64)-ε≤⨅ y : {y : StartSpace // y ∈ F.space ∧ ‖y‖=1},
        max ‖x+t • y.val‖ ‖x-t • y.val‖ := by
  obtain ⟨F,hF⟩ := start_completed_tail_bound x hx ht hε
  obtain ⟨y,hy,hyn⟩ := F.unit_exists StartSpace
    (infiniteDimensional_of_not_isAUC _ (start_no_equivalent_AUC (.refl ℝ _)))
  have : Nonempty {y : StartSpace // y ∈ F.space ∧ ‖y‖=1} := ⟨⟨y,hy,hyn⟩⟩
  refine ⟨F,le_ciInf fun y => ?_⟩
  have hh := hF y.val y.property.1 y.property.2.ge
  linarith

section RealObstructions
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem start_renorming_obstruction_real (e : StartSpace ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (start_no_equivalent_AUC e) (start_renorming_obstruction e hα hαβ he)

theorem start_no_equivalent_AUC_real (e : StartSpace ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (start_no_equivalent_AUC e)

theorem incomparable_renorming_obstruction_real (e : Dual ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (incomparable_no_equivalent_AUC e)
    (incomparable_renorming_obstruction e hα hαβ he)

theorem incomparable_no_equivalent_AUC_real (e : Dual ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (incomparable_no_equivalent_AUC e)
end RealObstructions
end Segments
end BoundedTreePotentials


end

end OAI
