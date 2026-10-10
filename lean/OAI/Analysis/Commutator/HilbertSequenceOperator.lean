import Mathlib
import OAI.Analysis.Commutator.HilbertSequence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ)

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma point_action_bound (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) (i : ℕ) :
    ‖T i (x.seq i)‖≤‖T‖*‖x.seq‖ :=
  (T i).le_of_opNorm_le (T.norm_coe_le_norm i) _ |>.trans
    (mul_le_mul_of_nonneg_left (x.seq.norm_coe_le_norm i) (norm_nonneg _))

def actPreLinear (T : ℕ →ᵇ (E →L[ℂ] F)) : Pre ω E →ₗ[ℂ] Pre ω F where
  toFun x := ⟨BoundedContinuousFunction.mkOfDiscrete (fun i => T i (x.seq i))
    (2*(‖T‖*‖x.seq‖)) (by
      intro i j
      exact (dist_le_norm_add_norm _ _).trans (by
        have hi := point_action_bound ω T x i
        have hj := point_action_bound ω T x j
        linarith))⟩
  map_add' x y := by
    apply (equiv ω F).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_add (T i) _ _
  map_smul' r x := by
    apply (equiv ω F).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_smul (T i) r _

@[simp] lemma actPreLinear_seq (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) (i : ℕ) :
    (actPreLinear ω T x).seq i=T i (x.seq i) := rfl

lemma norm_actPreLinear_le (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) :
    ‖actPreLinear ω T x‖≤‖T‖*‖x‖ := by
  apply le_of_tendsto_of_tendsto (tendsto_norm ω F (actPreLinear ω T x))
    (tendsto_const_nhds.mul (tendsto_norm ω E x))
  exact Filter.Eventually.of_forall (fun i => (T i).le_of_opNorm_le (T.norm_coe_le_norm i) _)

def actPre (T : ℕ →ᵇ (E →L[ℂ] F)) : Pre ω E →L[ℂ] Pre ω F :=
  (actPreLinear ω T).mkContinuous ‖T‖ (norm_actPreLinear_le ω T)

def act (T : ℕ →ᵇ (E →L[ℂ] F)) : Space ω E →L[ℂ] Space ω F :=
  (actPre ω T).completion

@[simp] lemma act_coe (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) :
    act ω T x=(actPreLinear ω T x : Space ω F) :=
  ContinuousLinearMap.completion_apply_coe _ _

lemma norm_act_apply_le (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Space ω E) :
    ‖act ω T x‖≤‖T‖*‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa only [act_coe,Completion.norm_coe] using norm_actPreLinear_le ω T x

lemma norm_act_le (T : ℕ →ᵇ (E →L[ℂ] F)) : ‖act ω T‖≤‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_act_apply_le ω T)

lemma act_eq_of_coe (S T : Space ω E →L[ℂ] Space ω F)
    (h : ∀ x : Pre ω E, S x=T x) : S=T := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => exact h x

lemma act_add (S T : ℕ →ᵇ (E →L[ℂ] F)) : act ω (S+T)=act ω S+act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [add_apply,act_coe,act_coe,act_coe,← Completion.coe_add]
  congr 1

lemma act_smul (r : ℂ) (T : ℕ →ᵇ (E →L[ℂ] F)) : act ω (r • T)=r • act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [smul_apply,act_coe,act_coe,← Completion.coe_smul]
  congr 1

lemma act_constant (T : E →L[ℂ] F) (x : E) :
    act ω (BoundedContinuousFunction.const ℕ T) (constant ω E x)=constant ω F (T x) := by
  rw [constant_apply,act_coe,constant_apply]
  congr 1

lemma norm_act_constant (T : E →L[ℂ] F) :
    ‖act ω (BoundedContinuousFunction.const ℕ T)‖=‖T‖ := by
  apply le_antisymm
  · simpa using norm_act_le ω (BoundedContinuousFunction.const ℕ T)
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (act ω (BoundedContinuousFunction.const ℕ T)))
    intro x
    have h := (act ω (BoundedContinuousFunction.const ℕ T)).le_opNorm (constant ω E x)
    simpa only [act_constant,LinearIsometry.norm_map] using h

lemma act_zero : act ω (0 : ℕ →ᵇ (E →L[ℂ] F))=0 := by
  apply act_eq_of_coe ω
  intro x
  rw [act_coe,zero_apply,← Completion.coe_zero]
  congr 1

lemma act_mul (S T : ℕ →ᵇ (E →L[ℂ] E)) : act ω (S*T)=act ω S*act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [mul_apply_eq_comp,act_coe,act_coe,act_coe]
  congr 1

lemma act_one : act ω (1 : ℕ →ᵇ (E →L[ℂ] E))=1 := by
  apply act_eq_of_coe ω
  intro x
  rw [act_coe,one_apply_eq_self]
  congr 1

variable [CompleteSpace E]

lemma act_star (T : ℕ →ᵇ (E →L[ℂ] E)) : act ω (star T)=star (act ω T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      rw [act_coe,act_coe,Completion.inner_coe,Completion.inner_coe]
      apply tendsto_nhds_unique (tendsto_inner ω E (actPreLinear ω (star T) x) y)
      have h := tendsto_inner ω E x (actPreLinear ω T y)
      simpa only [actPreLinear_seq,BoundedContinuousFunction.star_apply,
        ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using h

def actionHom : (ℕ →ᵇ (E →L[ℂ] E)) →⋆ₐ[ℂ] (Space ω E →L[ℂ] Space ω E) where
  toFun := act ω
  map_one' := act_one ω
  map_zero' := act_zero ω
  map_add' := act_add ω
  map_mul' := act_mul ω
  map_star' := act_star ω
  commutes' r := by
    change act ω (r • (1 : ℕ →ᵇ (E →L[ℂ] E)))=r • (1 : Space ω E →L[ℂ] Space ω E)
    rw [act_smul,act_one]

end Kadison.HilbertSequence

end

end
end

end OAI
