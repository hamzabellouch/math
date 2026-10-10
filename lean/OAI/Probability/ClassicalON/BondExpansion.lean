import OAI.Probability.ClassicalON.DiscreteReference

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def bondSignProduct (left right : E → V) (t : E → ℝ) (η : E → Bool) (s : V → Bool) : ℝ :=
  ∏ e,if η e then (if s (left e)=s (right e) then t e else 0) else 1

omit [Fintype V] in
theorem bondSignProduct_eq (left right : E → V) (t : E → ℝ) (η : E → Bool) (s : V → Bool) :
    bondSignProduct left right t η s=
      bondProduct t η*(if s∈compatibleSigns left right η then 1 else 0) := by
  by_cases h : s∈compatibleSigns left right η
  · simp only [h,ite_true,mul_one,bondSignProduct,bondProduct]
    apply Finset.prod_congr rfl
    intro e _
    cases he : η e
    · simp
    · simp [h e he]
  · simp only [h,ite_false,mul_zero]
    obtain ⟨e,he,hs⟩ : ∃ e,η e=true ∧ s (left e)≠s (right e) := by
      change ¬(∀ e,η e=true → s (left e)=s (right e)) at h
      push Not at h
      exact h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he,hs]

omit [Fintype V] in
theorem ising_expansion (left right : E → V) (K : E → ℝ) (s : V → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K s)=
      Real.exp (-∑ e,K e)*∑ η : E → Bool,bondSignProduct left right
        (fun e => Real.exp (2*K e)-1) η s := by
  have hedge (k : ℝ) (a b : Bool) :
      Real.exp (k*(signValue a*signValue b))=
        Real.exp (-k)*(∑ η : Bool,if η then (if a=b then Real.exp (2*k)-1 else 0) else 1) := by
    cases a <;> cases b <;> simp [signValue]
    all_goals ring_nf
    all_goals rw [← Real.exp_add]
    all_goals (congr 1; ring)
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum]
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib,Fintype.prod_sum]
  rfl

omit [Fintype V] in
theorem signValue_fieldSign (s : Bool) : signValue s=fieldSign (signFieldEquiv s) := by
  cases s <;> rfl

omit [Fintype E] in
theorem compatible_sign_correlation_sum (left right : E → V) (η : E → Bool) (x y : V) :
    (∑ s : V → Bool,(if s∈compatibleSigns left right η then (1:ℝ) else 0)*
      (signValue (s x)*signValue (s y)))=
      if bondConnected left right η x y then clusterWeight left right η else 0 := by
  have he := Equiv.sum_comp (compatibleSignsEquiv left right η)
    (fun s : bondSubspace left right η => fieldSign (s.val x)*fieldSign (s.val y))
  have hh : (∑ s : compatibleSigns left right η,signValue (s.val x)*signValue (s.val y))=
      ∑ s : bondSubspace left right η,fieldSign (s.val x)*fieldSign (s.val y) := by
    convert he using 1
    congr 1
    ext s
    simp only [signValue_fieldSign]
    rfl
  rw [← bond_sign_correlation left right η x y,← hh]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun s : V → Bool => s∈compatibleSigns left right η))
    (by simp) (fun s => signValue (s x)*signValue (s y)),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem ising_partition_bond_sum (left right : E → V) (K : E → ℝ) :
    (∫ s,Real.exp (edgeHamiltonian (isingEnergy left right) K s) ∂isingReference)=
      (2 : ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,K e)*
        ∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η := by
  rw [integral_isingReference]
  simp_rw [ising_expansion,bondSignProduct_eq]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,compatibleSigns_sum]
  unfold bondWeight
  simp only [mul_comm (bondProduct _ _) (clusterWeight _ _ _)]
  ring

end ClassicalON

end

end OAI
