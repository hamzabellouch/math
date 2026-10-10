import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.SequentialChunkCoupling

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma expectation_centered_sum_square (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (f : B → A → ℝ) (hmean : ∀ b,∑ a,w b a*f b a=0) :
    finiteExpectation (productWeights w) (fun D => (∑ b,f b (D b))^2)=
      ∑ b,∑ a,w b a*(f b a)^2 := by
  have he (D : B → A) : (∑ b,f b (D b))^2=∑ b,∑ c,f b (D b)*f c (D c) := by
    rw [sq,Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [he]
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteExpectation_sum]
  calc
    _=finiteExpectation (productWeights w) (fun D => f b (D b)*f b (D b)) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rw [expectation_distinct_coordinates w hw b c (Ne.symm hcb),hmean,zero_mul]
      · simp
    _=∑ a,w b a*(f b a)^2 := by
      rw [expectation_coordinate w hw b (fun a => f b a*f b a)]
      simp only [pow_two]

lemma finiteExpectation_exists_le {E : Type*} [Fintype E] [Nonempty E]
    (v : E → ℝ) (hv : ∀ x,0≤v x) (hs : ∑ x,v x=1) (F : E → ℝ) :
    ∃ x,F x≤finiteExpectation v F := by
  classical
  obtain ⟨x,_,hx⟩ := Finset.exists_min_image (Finset.univ : Finset E) F Finset.univ_nonempty
  refine ⟨x,?_⟩
  calc
    F x=finiteExpectation v (fun _ => F x) := by rw [finiteExpectation_const,hs,one_mul]
    _≤finiteExpectation v F := finiteExpectation_mono v hv _ _ (fun y => hx y (Finset.mem_univ y))

lemma probability_weight_le_one (w : A → ℝ) (hw : ∀ a,0≤w a) (hs : ∑ a,w a=1) (a : A) :
    w a≤1 := by
  rw [←hs]
  exact Finset.single_le_sum (fun b _ => hw b) (Finset.mem_univ a)

lemma categorical_variance [DecidableEq A] (w : A → ℝ) (_hw : ∀ a,0≤w a)
    (hs : ∑ a,w a=1) (a : A) (q : ℝ) :
    (∑ z,w z*(q*((if z=a then 1 else 0)-w a))^2)≤q^2*w a := by
  have h1 : (∑ z,w z*(if z=a then 1 else 0))=w a := by simp
  have h2 : (∑ z,w z*(if z=a then 1 else 0)^2)=w a := by simp
  have he (z : A) : w z*(q*((if z=a then 1 else 0)-w a))^2=
      q^2*(w z*(if z=a then 1 else 0)^2)-
      (2*q^2*w a)*(w z*(if z=a then 1 else 0))+(q^2*(w a)^2)*w z := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    ←Finset.mul_sum,h1,h2,hs]
  nlinarith [sq_nonneg (q*w a)]

lemma categorical_mean_zero [DecidableEq A] (w : A → ℝ) (hs : ∑ a,w a=1) (a : A) (q : ℝ) :
    (∑ z,w z*(q*((if z=a then 1 else 0)-w a)))=0 := by
  have he (z : A) : w z*(q*((if z=a then 1 else 0)-w a))=
    q*(w z*(if z=a then 1 else 0))-(q*w a)*w z := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hs]
  simp

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

noncomputable def assignedMass (q : B → ℝ) (D : B → A) (a : A) : ℝ :=
  ∑ b,q b*(if D b=a then 1 else 0)
noncomputable def fractionalMass (q : B → ℝ) (w : B → A → ℝ) (a : A) : ℝ :=
  ∑ b,q b*w b a
noncomputable def assignmentError (q : B → ℝ) (w : B → A → ℝ) (D : B → A) : ℝ :=
  ∑ a,|assignedMass q D a-fractionalMass q w a|

omit [Nonempty A] in
lemma expected_row_error_square (q : B → ℝ) (w : B → A → ℝ)
    (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1) (a : A) :
    finiteExpectation (productWeights w)
      (fun D => (assignedMass q D a-fractionalMass q w a)^2)≤∑ b,(q b)^2*w b a := by
  let f : B → A → ℝ := fun b z => q b*((if z=a then 1 else 0)-w b a)
  have he (D : B → A) : assignedMass q D a-fractionalMass q w a=∑ b,f b (D b) := by
    simp only [assignedMass,fractionalMass,f,mul_sub,Finset.sum_sub_distrib]
  simp_rw [he]
  rw [expectation_centered_sum_square w hs f (fun b => categorical_mean_zero (w b) (hs b) a (q b))]
  exact Finset.sum_le_sum (fun b _ => categorical_variance (w b) (hw b) (hs b) a (q b))

omit [Nonempty A] in
lemma expected_assignment_error_square (q : B → ℝ) (hq : ∀ b,0≤q b) (hqsum : ∑ b,q b=1)
    (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1)
    {M : ℝ} (hM : ∀ b,q b≤M) :
    finiteExpectation (productWeights w) (fun D => assignmentError q w D^2)≤
      (Fintype.card A : ℝ)*M := by
  have hpt (D : B → A) : assignmentError q w D^2≤
      (Fintype.card A : ℝ)*∑ a,(assignedMass q D a-fractionalMass q w a)^2 := by
    simpa only [assignmentError,Finset.card_univ,sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
        (f:=fun a => |assignedMass q D a-fractionalMass q w a|))
  have hW := productWeights_nonneg w hw
  calc
    _≤finiteExpectation (productWeights w)
        (fun D => (Fintype.card A : ℝ)*∑ a,(assignedMass q D a-fractionalMass q w a)^2) :=
      finiteExpectation_mono _ hW _ _ hpt
    _=(Fintype.card A : ℝ)*∑ a,finiteExpectation (productWeights w)
        (fun D => (assignedMass q D a-fractionalMass q w a)^2) := by
      rw [finiteExpectation_smul,finiteExpectation_sum]
    _≤(Fintype.card A : ℝ)*∑ a,∑ b,(q b)^2*w b a := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun a _ => expected_row_error_square q w hw hs a)
    _=(Fintype.card A : ℝ)*∑ b,(q b)^2 := by
      rw [Finset.sum_comm]
      simp only [←Finset.mul_sum,hs,mul_one]
    _≤(Fintype.card A : ℝ)*M := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        (∑ b,(q b)^2)≤∑ b,M*q b :=
          Finset.sum_le_sum (fun b _ => by nlinarith [mul_le_mul_of_nonneg_right (hM b) (hq b)])
        _=M := by rw [←Finset.mul_sum,hqsum,mul_one]

omit [DecidableEq A] [Nonempty A] in
lemma expected_assignment_cost (q : B → ℝ) (w : B → A → ℝ)
    (hs : ∀ b,∑ a,w b a=1) (c : A → B → ℝ) :
    finiteExpectation (productWeights w) (fun D => ∑ b,q b*c (D b) b)=
      ∑ b,∑ a,q b*w b a*c a b := by
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteExpectation_smul,expectation_coordinate w hs b (fun a => c a b),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exists_deterministic_assignment (q : B → ℝ) (hq : ∀ b,0≤q b) (hqsum : ∑ b,q b=1)
    (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (hs : ∀ b,∑ a,w b a=1)
    (c : A → B → ℝ) {M : ℝ} (hM : ∀ b,q b≤M) :
    ∃ D : B → A,assignmentError q w D^2+(∑ b,q b*c (D b) b)≤
      (Fintype.card A : ℝ)*M+∑ b,∑ a,q b*w b a*c a b := by
  obtain ⟨D,hD⟩ := finiteExpectation_exists_le (productWeights w) (productWeights_nonneg w hw)
    (productWeights_sum w hs)
    (fun D => assignmentError q w D^2+∑ b,q b*c (D b) b)
  refine ⟨D,hD.trans ?_⟩
  rw [finiteExpectation_add,expected_assignment_cost q w hs c]
  have h := expected_assignment_error_square q hq hqsum w hw hs hM
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

noncomputable def conditionalAssignment (r : MatrixCoupling p q) (b : B) (a : A) : ℝ :=
  if q b=0 then (if a=Classical.choice (inferInstance : Nonempty A) then 1 else 0)
  else r.weight a b/q b

omit [DecidableEq B] in
lemma conditionalAssignment_nonneg (r : MatrixCoupling p q) (b : B) (a : A) :
    0≤r.conditionalAssignment b a := by
  unfold conditionalAssignment
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (r.nonneg a b) (r.right_nonneg b)

omit [DecidableEq B] in
lemma conditionalAssignment_sum (r : MatrixCoupling p q) (b : B) :
    ∑ a,r.conditionalAssignment b a=1 := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · simp [hq]
  · simp only [hq,ite_false,←Finset.sum_div,r.col,div_self hq]

omit [DecidableEq B] in
lemma mul_conditionalAssignment (r : MatrixCoupling p q) (a : A) (b : B) :
    q b*r.conditionalAssignment b a=r.weight a b := by
  unfold conditionalAssignment
  by_cases hq : q b=0
  · have hr : r.weight a b=0 := le_antisymm (by simpa only [hq] using r.le_right a b) (r.nonneg a b)
    simp [hq,hr]
  · simp only [hq,ite_false]
    exact mul_div_cancel₀ _ hq

omit [DecidableEq B] in
lemma fractionalMass_conditionalAssignment (r : MatrixCoupling p q) (a : A) :
    fractionalMass q r.conditionalAssignment a=p a := by
  simp only [fractionalMass,r.mul_conditionalAssignment,r.row]

theorem exists_rounded_decoder (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (c : A → B → ℝ) {M : ℝ} (hM : ∀ b,q b≤M) :
    ∃ D : B → A,(∑ a,|assignedMass q D a-p a|)^2+(∑ b,q b*c (D b) b)≤
      (Fintype.card A : ℝ)*M+r.cost c := by
  obtain ⟨D,hD⟩ := exists_deterministic_assignment q r.right_nonneg hq r.conditionalAssignment
    r.conditionalAssignment_nonneg r.conditionalAssignment_sum c hM
  refine ⟨D,?_⟩
  simp only [assignmentError,r.fractionalMass_conditionalAssignment,r.mul_conditionalAssignment] at hD
  rw [Finset.sum_comm] at hD
  exact hD

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

omit [Fintype A] [DecidableEq B] [Nonempty A] in
lemma assignedMass_nonneg (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) (a : A) :
    0≤assignedMass q D a := Finset.sum_nonneg (fun b _ => mul_nonneg (hq b) (by split_ifs <;> norm_num))
omit [DecidableEq B] [Nonempty A] in
lemma assignedMass_sum (q : B → ℝ) (D : B → A) : ∑ a,assignedMass q D a=∑ b,q b := by
  unfold assignedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def assignment (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) :
    MatrixCoupling (assignedMass q D) q where
  weight a b := q b*(if D b=a then 1 else 0)
  nonneg a b := mul_nonneg (hq b) (by split_ifs <;> norm_num)
  row a := rfl
  col b := by simp

omit [DecidableEq B] [Nonempty A] in
lemma assignment_cost (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) (c : A → B → ℝ) :
    (assignment q hq D).cost c=∑ b,q b*c (D b) b := by
  unfold cost assignment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp

omit [DecidableEq B] [Nonempty A] in
theorem repair_assignment (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (D : B → A) (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1) :
    ∃ R : MatrixCoupling p q,
      R.cost (fun a b => symbolCost a (D b))≤∑ a,|assignedMass q D a-p a| ∧
      R.cost c≤(∑ b,q b*c (D b) b)+∑ a,|assignedMass q D a-p a| := by
  have hp : ∑ a,p a=1 := by
    simp only [←r.row]
    rw [Finset.sum_comm]
    simp only [r.col,hq]
  obtain ⟨w,hw,hrow,hcol,hwcost⟩ := finite_maximal_coupling p (assignedMass q D) r.left_nonneg
    (assignedMass_nonneg q r.right_nonneg D) hp (by rw [assignedMass_sum,hq])
  let S : MatrixCoupling p (assignedMass q D) := ⟨w,hw,hrow,hcol⟩
  let U := assignment q r.right_nonneg D
  have hScost : S.cost symbolCost=(∑ a,∑ b,w a b*(if a=b then 0 else 1)) := by
    unfold cost
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a=b <;> simp [S,symbolCost,h]
  have hS : S.cost symbolCost≤∑ a,|assignedMass q D a-p a| := by
    rw [hScost]
    apply hwcost.le.trans
    apply Finset.sum_le_sum
    intro a _
    have h : max (p a-assignedMass q D a) 0≤|p a-assignedMass q D a| :=
      max_le (le_abs_self _) (abs_nonneg _)
    simpa only [abs_sub_comm] using h
  have hU : U.cost (fun a b => symbolCost a (D b))=0 := by
    rw [assignment_cost]
    simp only [symbolCost_self,mul_zero,Finset.sum_const_zero]
  refine ⟨S.comp U,?_,?_⟩
  · have h := comp_cost_le S U symbolCost (fun a b => symbolCost a (D b))
      (fun a b => symbolCost a (D b)) (fun a b v => symbolCost_triangle a b (D v))
    rw [hU,add_zero] at h
    exact h.trans hS
  · have htri (a a' : A) (b : B) : c a b≤ symbolCost a a'+c a' b := by
      by_cases h : a=a'
      · subst a'; simp only [symbolCost_self,zero_add,le_refl]
      · simp only [symbolCost,ite_eq_right h]
        have h0 := hc0 a' b
        have h1 := hc1 a b
        linarith
    have h := comp_cost_le S U symbolCost c c htri
    rw [assignment_cost] at h
    linarith

theorem exists_decodable_coupling (r : MatrixCoupling p q) (hq : ∑ b,q b=1)
    (c : A → B → ℝ) (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    {M : ℝ} (hM : ∀ b,q b≤M) :
    ∃ (D : B → A) (R : MatrixCoupling p q),
      R.cost (fun a b => symbolCost a (D b))≤Real.sqrt ((Fintype.card A : ℝ)*M+r.cost c) ∧
      R.cost c≤(Fintype.card A : ℝ)*M+r.cost c+Real.sqrt ((Fintype.card A : ℝ)*M+r.cost c) := by
  obtain ⟨D,hD⟩ := r.exists_rounded_decoder hq c hM
  have he0 : 0≤∑ a,|assignedMass q D a-p a| := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hcost0 : 0≤∑ b,q b*c (D b) b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (r.right_nonneg b) (hc0 _ _))
  have hE : 0≤(Fintype.card A : ℝ)*M+r.cost c := by nlinarith [sq_nonneg (∑ a,|assignedMass q D a-p a|)]
  have herr : (∑ a,|assignedMass q D a-p a|)≤Real.sqrt ((Fintype.card A : ℝ)*M+r.cost c) := by
    nlinarith [Real.sq_sqrt hE,Real.sqrt_nonneg ((Fintype.card A : ℝ)*M+r.cost c)]
  have hc : (∑ b,q b*c (D b) b)≤(Fintype.card A : ℝ)*M+r.cost c := by
    nlinarith [sq_nonneg (∑ a,|assignedMass q D a-p a|)]
  obtain ⟨R,hdecode,hpaint⟩ := r.repair_assignment hq D c hc0 hc1
  exact ⟨D,R,hdecode.trans herr,by linarith⟩

end MatrixCoupling
end HyperbolicCoding

end
end

end OAI
