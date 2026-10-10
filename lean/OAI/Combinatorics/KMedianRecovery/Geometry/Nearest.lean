import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.LinearPayment
import OAI.Combinatorics.KMedianRecovery.Recovery.Form

namespace OAI

namespace MetricKMedianRecovery.RationalOpenability
open RationalLinearFeasibility OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def nearest (d : X → D → ℚ) (W : Finset X) (j : D) : ℚ :=
  if h : W.Nonempty then W.inf' h (fun f => d f j) else 0

omit [Fintype D] [DecidableEq X] in
lemma nearest_cast (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (W : Finset X) (j : D) : (nearest d W j:ℝ)=nearestDistance (loc j) W := by
  classical
  unfold nearest nearestDistance
  split_ifs with h
  · obtain ⟨f,hf,he⟩ := Finset.exists_mem_eq_inf' h (fun f => d f j)
    have hmin : ∀ g ∈ W, d f j ≤ d g j := by
      intro g hg
      rw [←he]
      exact Finset.inf'_le _ hg
    apply le_antisymm
    · apply Finset.le_inf' h
      intro g hg
      rw [he,hd,dist_comm]
      have hh : (d f j:ℝ) ≤ (d g j:ℝ) := Rat.cast_le.mpr (hmin g hg)
      simpa only [hd,dist_comm] using hh
    · rw [he,hd,dist_comm]
      exact Finset.inf'_le _ hf
  · simp

inductive Kind (D W F : Type*) where
  | lower : D → Kind D W F
  | upper : D → Kind D W F
  | cap : D → W → Kind D W F
  | far : D → Kind D W F
  | payment : Kind D W F
  | slackZero : F → D → D → Kind D W F
  | slackTerm : F → D → D → Kind D W F
  | dual : F → D → Kind D W F
  deriving Fintype

abbrev Variables (D F : Type*) := D ⊕ (F × D × D)

noncomputable def bid (F : Type*) (j : D) : Form (Variables D F) := by
  classical
  exact Form.coord (.inl j)
noncomputable def slack {Facilities : Type*} (f : Facilities) (a j : D) :
    Form (Variables D Facilities) := by
  classical
  exact Form.coord (.inr (f,a,j))

noncomputable def paymentForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (i : X) : Form (Variables D F) := by
  classical
  exact Form.sum (fun j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    if dist i (loc j) ≤ (v:ℝ)*(z:ℝ) then (bid F j).sub (Form.const ((1-3*v)*d i j))
    else Form.const (max (z-(1-3*v)*d i j) 0)
    else Form.const (max ((1-3*v)*nearest d W j-(1-3*v)*d i j) 0))

noncomputable def dualForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (f : F) (a j : D) : Form (Variables D F) := by
  classical
  exact if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    (bid F j).sub (Form.const (d f j))
    else (bid F a).sub (Form.const (2*d f j+d f a))

noncomputable def system (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z lam eta : ℚ) (i : X) : Kind D W F → Form (Variables D F) := by
  classical
  exact fun k => match k with
  | .lower j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j) then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (paymentForm loc d F W v z i)
  | .slackZero f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.const 0).sub (slack f a j) else Form.const 0
  | .slackTerm f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (dualForm loc d F W v z f a j).sub (slack f a j) else Form.const 0
  | .dual f a => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.sum (fun j => slack f a j)).sub (Form.const lam) else Form.const 0

@[simp] lemma bid_eval (F : Type*) [Fintype F] (j : D) (x : Variables D F → ℝ) :
    (bid F j).realEval x = x (.inl j) := by
  classical
  simp [bid]
@[simp] lemma slack_eval (F : Type*) [Fintype F] (f : F) (a j : D) (x : Variables D F → ℝ) :
    (slack f a j).realEval x = x (.inr (f,a,j)) := by
  classical
  simp [slack]

omit [DecidableEq X] in
lemma payment_eval (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z : ℚ) (i : X) (x : Variables D F → ℝ) :
    (paymentForm loc d F W v z i).realEval x =
      linearPayment loc (1-3*(v:ℝ)) (v:ℝ) (z:ℝ) W i (fun j => x (.inl j)) := by
  classical
  unfold paymentForm linearPayment
  rw [Form.realEval_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [Form.realEval_sub,Form.realEval_const,bid_eval]
  · push_cast
    rw [hd]
  · push_cast
    rw [hd]
  · push_cast
    rw [nearest_cast loc d hd,hd]

omit [DecidableEq X] in
lemma dual_eval (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z : ℚ) (f : F) (a j : D) (x : Variables D F → ℝ) :
    (dualForm loc d F W v z f a j).realEval x =
      dualTerm loc (1-3*(v:ℝ)) (z:ℝ) W f (fun j => x (.inl j)) a j := by
  classical
  unfold dualForm dualTerm
  split_ifs <;> simp only [Form.realEval_sub,Form.realEval_const,bid_eval]
  · rw [hd]
  · push_cast
    rw [hd,hd]
    ring

omit [DecidableEq X] in
lemma system_iff (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z lam eta : ℚ) (i : X) (x : Variables D F → ℝ) :
    (∀ k, (system loc d F W v z lam eta i k).realEval x ≤ 0) ↔
      Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
        (fun j => x (.inl j)) (fun f a j => x (.inr (f,a,j))) := by
  classical
  have hcap (j : D) (f : X) : (((1-3*v)*d f j:ℚ):ℝ)=(1-3*(v:ℝ))*dist f (loc j) := by push_cast; rw [hd]
  have hphase : (((1+v^2)*z:ℚ):ℝ)=(1+(v:ℝ)^2)*(z:ℝ) := by push_cast; rfl
  have hpay : ((lam-(Fintype.card D:ℚ)*eta:ℚ):ℝ)=(lam:ℝ)-(Fintype.card D:ℝ)*(eta:ℝ) := by push_cast; rfl
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro j hj
      have hl := h (.lower j)
      have hu := h (.upper j)
      simp only [system,ite_eq_left hj,Form.realEval_sub,Form.realEval_const,bid_eval,hphase] at hl hu
      refine ⟨by linarith,by linarith,?_,?_⟩
      · intro f hf
        have hh := h (.cap j ⟨f,hf⟩)
        simp only [system,ite_eq_left hj,Form.realEval_sub,Form.realEval_const,bid_eval,hcap] at hh
        rw [dist_comm] at hh
        linarith
      · intro hf
        have hh := h (.far j)
        have ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j) := ⟨hj,hf⟩
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval] at hh
        linarith
    · have hh := h .payment
      simp only [system,Form.realEval_sub,Form.realEval_const,payment_eval loc d hd,hpay] at hh
      linarith
    · intro f a ha
      refine ⟨?_,?_⟩
      · intro j
        have hl := h (.slackZero f a j)
        have ht := h (.slackTerm f a j)
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,slack_eval,Rat.cast_zero,zero_sub,
          dual_eval loc d hd] at hl ht
        constructor <;> linarith
      · have hh := h (.dual f a)
        simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,Form.realEval_sum,slack_eval] at hh
        linarith
  · rintro ⟨hb,hp,hdrow⟩ k
    cases k with
    | lower j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,sub_nonpos] using (hb j ha).1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | upper j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,hphase,sub_nonpos] using (hb j ha).2.1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | cap j f =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,hcap,sub_nonpos,dist_comm] using (hb j ha).2.2.1 f f.property
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | far j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j)
      · simp only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,bid_eval,(hb j ha.1).2.2.2 ha.2,sub_self,le_refl]
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | payment => simpa only [system,Form.realEval_sub,Form.realEval_const,payment_eval loc d hd,hpay,sub_nonpos] using hp
    | slackZero f a j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,slack_eval,Rat.cast_zero,sub_nonpos] using (hdrow f a ha).1 j |>.1
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | slackTerm f a j =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,slack_eval,dual_eval loc d hd,sub_nonpos] using (hdrow f a ha).1 j |>.2
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]
    | dual f a =>
      by_cases ha : activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a
      · simpa only [system,ite_eq_left ha,Form.realEval_sub,Form.realEval_const,Form.realEval_sum,slack_eval,sub_nonpos] using (hdrow f a ha).2
      · simp only [system,ite_eq_right ha,Form.realEval_const,Rat.cast_zero,le_refl]

omit [DecidableEq X] in

theorem rational_openable (loc : D → X) (d : X → D → ℚ) (hd : ∀ f j, (d f j:ℝ)=dist f (loc j))
    (F W : Finset X) (v z lam eta : ℚ) (i : X)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i ↔
      ∃ tau : D → ℚ, ∃ y : F → D → D → ℚ,
        Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
          (fun j => (tau j:ℝ)) (fun f a j => (y f a j:ℝ)) := by
  classical
  rw [openable_iff_linear_feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz]
  constructor
  · rintro ⟨tau,y,h⟩
    let x : Variables D F → ℝ := Sum.elim tau (fun p => y p.1 p.2.1 p.2.2)
    have hh : ∀ k, (system loc d F W v z lam eta i k).realEval x ≤ 0 :=
      (system_iff loc d hd F W v z lam eta i x).mpr h
    obtain ⟨q,hq⟩ := (affine_rational_witness (system loc d F W v z lam eta i)).mp ⟨x,hh⟩
    refine ⟨fun j => q (.inl j),fun f a j => q (.inr (f,a,j)),?_⟩
    apply (system_iff loc d hd F W v z lam eta i (fun w => (q w:ℝ))).mp
    intro k
    rw [Form.realEval_cast]
    exact_mod_cast hq k
  · rintro ⟨tau,y,h⟩
    exact ⟨fun j => (tau j:ℝ),fun f a j => (y f a j:ℝ),h⟩

end MetricKMedianRecovery.RationalOpenability

end OAI
