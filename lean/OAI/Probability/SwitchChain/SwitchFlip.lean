import OAI.Probability.SwitchChain.PairSquaredEnergy
import OAI.Probability.SwitchChain.SwitchInFiber

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.SwitchFlip

variable {n : ℕ} {d : Fin n → ℕ}

lemma not_valid_reverse {G : SimpleGraph (Fin n)} {p : SwitchProposal n}
    (h : validSwitch G p) : ¬ validSwitch G (reverseProposal p) := by
  intro hr
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < p.1.val.card by rw [p.1.property]; omega)
  obtain ⟨v, hv, _⟩ := (p.2.val.1.property u).1 hu
  exact hr.2 hv (h.1 hv)

lemma valid_reverse_result {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    validSwitch (proposalState G p).val (reverseProposal p) := by
  change validSwitch (proposalResult G.val p) (reverseProposal p)
  rw [proposalResult_of_valid h]
  exact validSwitch_reverse_replace h

lemma state_reverse {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    proposalState (proposalState G p) (reverseProposal p) = G := by
  apply Subtype.ext
  exact proposalResult_reverse h

def flip (p : SwitchProposal n) (G : GraphState n d) : GraphState n d :=
  if validSwitch G.val p then proposalState G p
  else if validSwitch G.val (reverseProposal p) then proposalState G (reverseProposal p)
  else G

@[simp] theorem flip_of_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val p) : flip p G = proposalState G p := by
  simp [flip, h]

@[simp] theorem flip_of_reverse_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val (reverseProposal p)) :
    flip p G = proposalState G (reverseProposal p) := by
  have hn : ¬ validSwitch G.val p := by simpa using not_valid_reverse h
  simp [flip, hn, h]

@[simp] theorem flip_reverse (p : SwitchProposal n) (G : GraphState n d) :
    flip (reverseProposal p) G = flip p G := by
  by_cases h : validSwitch G.val p
  · simp [flip, h, not_valid_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p) <;> simp [flip, h, hr]

 theorem flip_involutive (p : SwitchProposal n) :
    Function.Involutive (flip (d := d) p) := by
  intro G
  by_cases h : validSwitch G.val p
  · rw [flip_of_valid p G h,
      flip_of_reverse_valid p _ (valid_reverse_result h), state_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hr]
      have hv : validSwitch (proposalState G (reverseProposal p)).val p := by
        simpa using valid_reverse_result hr
      rw [flip_of_valid p _ hv]
      simpa using state_reverse hr
    · simp [flip, h, hr]

def equiv (p : SwitchProposal n) : Equiv.Perm (GraphState n d) :=
  ⟨flip p, flip p, flip_involutive p, flip_involutive p⟩

@[simp] theorem equiv_apply (p : SwitchProposal n) (G : GraphState n d) :
    equiv p G = flip p G := rfl

def isometry (p : SwitchProposal n) :
    PairResampling.StateSpace n d ≃ₗᵢ[ℝ] PairResampling.StateSpace n d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (equiv p)

@[simp] theorem isometry_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    isometry p f G = f (flip p G) := rfl

def operator (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (isometry p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem operator_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    operator p f G = f (flip p G) := rfl

@[simp] theorem operator_involutive (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : operator p (operator p f) = f := by
  ext G
  simp only [operator_apply, flip_involutive p G]

 theorem operator_symmetric (p : SwitchProposal n) :
    (operator (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫
  have h := (isometry (d := d) p).inner_map_map f (operator p g)
  change ⟪operator p f, operator p (operator p g)⟫ = ⟪f, operator p g⟫ at h
  simpa only [operator_involutive] using h

def projection (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ - operator p)

@[simp] theorem projection_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    projection p f G = (f G - f (flip p G)) / 2 := by
  simp [projection, div_eq_mul_inv, mul_comm]

 theorem projection_idempotent (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : projection p (projection p f) = projection p f := by
  ext G
  simp only [projection_apply, flip_involutive p G]
  ring

 theorem projection_symmetric (p : SwitchProposal n) :
    (projection (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪(1 / 2 : ℝ) • (f - operator p f), g⟫ =
    ⟪f, (1 / 2 : ℝ) • (g - operator p g)⟫
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  have h := operator_symmetric p f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫ at h
  rw [h]

 theorem inner_projection (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) :
    ⟪f, projection p f⟫ = ‖projection p f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := projection_symmetric p f (projection p f)
  change ⟪projection p f, projection p f⟫ = ⟪f, projection p (projection p f)⟫ at h
  simpa only [projection_idempotent] using h.symm

@[simp] theorem projection_reverse (p : SwitchProposal n) :
    projection (d := d) (reverseProposal p) = projection p := by
  ext f G
  simp only [projection_apply, flip_reverse]

theorem norm_projection_sq (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ G : GraphState n d, (f G - f (flip p G)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PairResampling.state_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G _
  rw [projection_apply]
  ring

theorem proposal_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (proposalState G p).val := by
  apply sameFiber_of_same_side a G (proposalState G p)
  intro u v hside
  have hm : ¬ (removedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inl h)
    tauto
  have hn : ¬ (addedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inr h)
    tauto
  by_cases hv : validSwitch G.val p
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    rw [proposalResult_of_valid hv]
    change G.val.Adj u v ↔ (G.val.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
      (addedMatching p).Adj u v
    simp [hm, hn]
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    simp [proposalResult, hv]

theorem flip_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (flip p G).val := by
  have hr : SwitchPairFiber.Crosses (reverseProposal p) a := by
    intro u v h
    apply hcross u v
    simpa only [removedMatching_reverse, addedMatching_reverse, or_comm] using h
  by_cases hv : validSwitch G.val p
  · rw [flip_of_valid p G hv]
    exact proposal_sameFiber p a hcross G
  · by_cases hv' : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hv']
      exact proposal_sameFiber (reverseProposal p) a hr G
    · simp only [flip, ite_eq_right hv, ite_eq_right hv']
      exact PairResampling.SameFiber.refl a G.val

theorem projection_eq_zero_of_fiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d)
    (hf : f ∈ PairResampling.fiberSpace n d a) : projection p f = 0 := by
  ext G
  change projection p f G = 0
  rw [projection_apply, hf G (flip p G) (flip_sameFiber p a hcross G)]
  ring

theorem projection_mem_orthogonal (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p f ∈ (PairResampling.fiberSpace n d a)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have h := projection_symmetric p g f
  change ⟪projection p g, f⟫ = ⟪g, projection p f⟫ at h
  rw [projection_eq_zero_of_fiber p a hcross g hg, inner_zero_left] at h
  exact h.symm

@[simp] theorem projection_expectation (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.expectation n d a f) = 0 :=
  projection_eq_zero_of_fiber p a hcross _ (PairResampling.expectation_mem a f)

 theorem fluctuation_projection (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    PairResampling.fluctuation n d a (projection p f) = projection p f := by
  exact (Submodule.starProjection_eq_self_iff).mpr
    (projection_mem_orthogonal p a hcross f)

 theorem projection_fluctuation (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.fluctuation n d a f) = projection p f := by
  rw [PairResampling.fluctuation_eq_sub, map_sub,
    projection_expectation p a hcross, sub_zero]

theorem isSymmetricProjection (p : SwitchProposal n) :
    (projection (d := d) p).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, projection_symmetric p⟩
  apply LinearMap.ext
  intro f
  change projection p (projection p f) = projection p f
  exact projection_idempotent p f

theorem norm_projection_le_of_mem (p : SwitchProposal n)
    (J : Submodule ℝ (PairResampling.StateSpace n d))
    (hJ : ∀ f, projection p f ∈ J) (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ≤ ‖J.starProjection f‖ := by
  have hz := Submodule.starProjection_inner_eq_zero (K := J) f
    (projection p f) (hJ f)
  rw [inner_sub_left, inner_projection] at hz
  have hc := real_inner_le_norm (J.starProjection f) (projection p f)
  have hp := norm_nonneg (projection p f)
  have hj := norm_nonneg (J.starProjection f)
  by_cases he : ‖projection p f‖ = 0
  · rw [he]
    exact hj
  · have hp' : 0 < ‖projection p f‖ := lt_of_le_of_ne hp (Ne.symm he)
    nlinarith

theorem projection_mem_jointOrthogonal (p : SwitchProposal n)
    (a b : Finset (Fin n)) (ha : SwitchPairFiber.Crosses p a)
    (hb : SwitchPairFiber.Crosses p b) (f : PairResampling.StateSpace n d) :
    projection p f ∈ (PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ := by
  rw [← Submodule.inf_orthogonal]
  exact ⟨projection_mem_orthogonal p a ha f, projection_mem_orthogonal p b hb f⟩

theorem norm_projection_le_jointOrthogonal (p : SwitchProposal n)
    (a b : Finset (Fin n)) (ha : SwitchPairFiber.Crosses p a)
    (hb : SwitchPairFiber.Crosses p b) (f : PairResampling.StateSpace n d) :
    ‖projection p f‖ ≤ ‖(PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ.starProjection f‖ := by
  exact norm_projection_le_of_mem p _ (projection_mem_jointOrthogonal p a b ha hb) f

end Problem315.SwitchFlip

end

end OAI
