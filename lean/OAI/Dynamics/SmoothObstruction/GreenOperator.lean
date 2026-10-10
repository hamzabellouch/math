import OAI.Dynamics.SmoothObstruction.SpectralBins

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Finite fundamental matrices, with the output time first. -/
structure Evolution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  map : ℕ → ℕ → E →L[ℝ] E
  self : ∀ t,map t t=ContinuousLinearMap.id ℝ E
  compose : ∀ t s u,(map t s).comp (map s u)=map t u

namespace Evolution
variable (A : Evolution E)

@[simp] lemma self_apply (t : ℕ) (v : E) : A.map t t v=v := by rw [A.self]; rfl
lemma comp_apply (t s u : ℕ) (v : E) : A.map t s (A.map s u v)=A.map t u v :=
  congrArg (fun F : E →L[ℝ] E => F v) (A.compose t s u)

noncomputable def forward (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) (t : ℕ) : E :=
  A.map t 0 a + ∑ j ∈ range t,A.map t (j+1) (P (j+1) (f j))

noncomputable def backward (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) (n t : ℕ) : E :=
  A.map t n c - ∑ j ∈ Ico t n,A.map t (j+1) (P (j+1) (f j))

@[simp] lemma forward_zero (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) :
    A.forward P f a 0=a := by simp [forward]
@[simp] lemma backward_end (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) (n : ℕ) :
    A.backward P f c n n=c := by simp [backward]

lemma forward_step (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) (t : ℕ) :
    A.forward P f a (t+1)=A.map (t+1) t (A.forward P f a t)+P (t+1) (f t) := by
  simp only [forward,sum_range_succ,map_add,map_sum,A.comp_apply,A.self_apply]
  abel

lemma backward_step (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) {n t : ℕ} (ht : t<n) :
    A.backward P f c n (t+1)=A.map (t+1) t (A.backward P f c n t)+P (t+1) (f t) := by
  have hs := sum_eq_sum_Ico_succ_bot ht (fun j => A.map (t+1) (j+1) (P (j+1) (f j)))
  simp only [backward,map_sub,map_sum,A.comp_apply]
  rw [hs,A.self_apply]
  abel

lemma forward_project (P : ℕ → E →L[ℝ] E)
    (hPP : ∀ t,(P t).comp (P t)=P t)
    (hPA : ∀ t s,(P t).comp (A.map t s)=(A.map t s).comp (P s))
    (f : ℕ → E) (a : E) (ha : P 0 a=a) (t : ℕ) :
    P t (A.forward P f a t)=A.forward P f a t := by
  have hcomm (t s : ℕ) (v : E) : P t (A.map t s v)=A.map t s (P s v) :=
    congrArg (fun F : E →L[ℝ] E => F v) (hPA t s)
  have hid (t : ℕ) (v : E) : P t (P t v)=P t v :=
    congrArg (fun F : E →L[ℝ] E => F v) (hPP t)
  simp only [forward,map_add,map_sum,hcomm,hid,ha]

lemma backward_project (P : ℕ → E →L[ℝ] E)
    (hPP : ∀ t,(P t).comp (P t)=P t)
    (hPA : ∀ t s,(P t).comp (A.map t s)=(A.map t s).comp (P s))
    (f : ℕ → E) (c : E) (n t : ℕ) (hc : P n c=c) :
    P t (A.backward P f c n t)=A.backward P f c n t := by
  have hcomm (t s : ℕ) (v : E) : P t (A.map t s v)=A.map t s (P s v) :=
    congrArg (fun F : E →L[ℝ] E => F v) (hPA t s)
  have hid (t : ℕ) (v : E) : P t (P t v)=P t v :=
    congrArg (fun F : E →L[ℝ] E => F v) (hPP t)
  simp only [backward,map_sub,map_sum,hcomm,hid,hc]

lemma recurrence_unique {v w : ℕ → E} {f : ℕ → E} {n : ℕ}
    (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (hw : ∀ t<n,w (t+1)=A.map (t+1) t (w t)+f t)
    (h0 : v 0=w 0) : ∀ t≤n,v t=w t := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ t ih => rw [hv t (by omega),hw t (by omega),ih (by omega)]

lemma backward_recurrence_unique {v w : ℕ → E} {f : ℕ → E} {n : ℕ}
    (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (hw : ∀ t<n,w (t+1)=A.map (t+1) t (w t)+f t)
    (hn : v n=w n) : ∀ t≤n,v t=w t := by
  intro t ht
  induction ht using Nat.decreasingInduction with
  | self => exact hn
  | of_succ t ht ih =>
    have hh : A.map (t+1) t (v t)=A.map (t+1) t (w t) := by
      have hh := ih
      rw [hv t ht,hw t ht] at hh
      exact add_right_cancel hh
    have hh' := congrArg (A.map t (t+1)) hh
    simpa only [A.comp_apply,A.self_apply] using hh'

end Evolution
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- An invariant complementary splitting. Empty groups are permitted. -/
structure Splitting (A : Evolution E) where
  slow : ℕ → E →L[ℝ] E
  fast : ℕ → E →L[ℝ] E
  slow_idem : ∀ t,(slow t).comp (slow t)=slow t
  fast_idem : ∀ t,(fast t).comp (fast t)=fast t
  add : ∀ t,slow t+fast t=ContinuousLinearMap.id ℝ E
  slow_inv : ∀ t s,(slow t).comp (A.map t s)=(A.map t s).comp (slow s)
  fast_inv : ∀ t s,(fast t).comp (A.map t s)=(A.map t s).comp (fast s)

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

lemma add_apply (t : ℕ) (v : E) : B.slow t v+B.fast t v=v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.add t)
lemma slow_comm (t s : ℕ) (v : E) : B.slow t (A.map t s v)=A.map t s (B.slow s v) :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.slow_inv t s)
lemma fast_comm (t s : ℕ) (v : E) : B.fast t (A.map t s v)=A.map t s (B.fast s v) :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.fast_inv t s)
lemma slow_self (t : ℕ) (v : E) : B.slow t (B.slow t v)=B.slow t v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.slow_idem t)
lemma fast_self (t : ℕ) (v : E) : B.fast t (B.fast t v)=B.fast t v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.fast_idem t)
lemma slow_fast (t : ℕ) (v : E) : B.slow t (B.fast t v)=0 := by
  have hh := congrArg (B.slow t) (B.add_apply t v)
  rw [map_add,B.slow_self] at hh
  exact add_left_cancel (hh.trans (add_zero _).symm)
lemma fast_slow (t : ℕ) (v : E) : B.fast t (B.slow t v)=0 := by
  have hh := congrArg (B.fast t) (B.add_apply t v)
  rw [map_add,B.fast_self] at hh
  exact add_right_cancel (hh.trans (zero_add _).symm)

/-- The endpoint projection has a specified bounded inverse on the actual
fast space. It need not annihilate the slow space. -/
structure Terminal (n : ℕ) where
  P : E →L[ℝ] H
  J : H →L[ℝ] E
  right : P.comp J=ContinuousLinearMap.id ℝ H
  left : (J.comp P).comp (B.fast n)=B.fast n
  range : (B.fast n).comp J=J

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)
lemma P_J (h : H) : C.P (C.J h)=h := congrArg (fun F : H →L[ℝ] H => F h) C.right
lemma J_P_fast (v : E) : C.J (C.P (B.fast n v))=B.fast n v :=
  congrArg (fun F : E →L[ℝ] E => F v) C.left
lemma fast_J (h : H) : B.fast n (C.J h)=C.J h :=
  congrArg (fun F : H →L[ℝ] E => F h) C.range

noncomputable def terminalValue (f : ℕ → E) (a : E) (h : H) : E :=
  C.J (h-C.P (A.forward B.slow f a n))
noncomputable def trajectory (f : ℕ → E) (a : E) (h : H) (t : ℕ) : E :=
  A.forward B.slow f a t+A.backward B.fast f (C.terminalValue f a h) n t

lemma trajectory_step (f : ℕ → E) (a : E) (h : H) {t : ℕ} (ht : t<n) :
    C.trajectory f a h (t+1)=A.map (t+1) t (C.trajectory f a h t)+f t := by
  rw [trajectory,A.forward_step,A.backward_step _ _ _ ht,trajectory,map_add]
  have hh := B.add_apply (t+1) (f t)
  calc
    _ = A.map (t+1) t (A.forward B.slow f a t)+
        A.map (t+1) t (A.backward B.fast f (C.terminalValue f a h) n t)+
        (B.slow (t+1) (f t)+B.fast (t+1) (f t)) := by abel
    _ = _ := by rw [hh]


lemma trajectory_terminal (f : ℕ → E) (a : E) (h : H) :
    C.P (C.trajectory f a h n)=h := by
  simp only [trajectory,A.backward_end,map_add,terminalValue,C.P_J]
  abel

lemma trajectory_slow_initial (f : ℕ → E) (a : E) (ha : B.slow 0 a=a) (h : H) :
    B.slow 0 (C.trajectory f a h 0)=a := by
  have hb := A.backward_project B.fast B.fast_idem B.fast_inv f
    (C.terminalValue f a h) n 0 (C.fast_J _)
  rw [trajectory,A.forward_zero,map_add,ha]
  rw [←hb,B.slow_fast,add_zero]

/-- Existence and uniqueness of the half-orbit boundary problem are proved
from the actual finite recurrence. No implicit-function hypothesis. -/
theorem trajectory_unique (f : ℕ → E) (a : E) (_ha : B.slow 0 a=a) (h : H)
    (v : ℕ → E) (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (h0 : B.slow 0 (v 0)=a) (hn : C.P (v n)=h) :
    ∀ t≤n,v t=C.trajectory f a h t := by
  have hs : ∀ t≤n,B.slow t (v t)=A.forward B.slow f a t := by
    apply A.recurrence_unique (f:=fun t => B.slow (t+1) (f t))
    · intro t ht
      rw [hv t ht,map_add,B.slow_comm]
    · intro t _
      exact A.forward_step B.slow f a t
    · simpa only [A.forward_zero] using h0
  have hend : B.fast n (v n)=C.terminalValue f a h := by
    unfold terminalValue
    rw [←hs n le_rfl,←hn,←map_sub]
    have he : v n-B.slow n (v n)=B.fast n (v n) := by
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using (B.add_apply n (v n)).symm
    rw [he,C.J_P_fast]
  have hf : ∀ t≤n,B.fast t (v t)=A.backward B.fast f (C.terminalValue f a h) n t := by
    apply A.backward_recurrence_unique (f:=fun t => B.fast (t+1) (f t))
    · intro t ht
      rw [hv t ht,map_add,B.fast_comm]
    · intro t ht
      exact A.backward_step B.fast f _ ht
    · simpa only [A.backward_end] using hend
  intro t ht
  rw [←B.add_apply t (v t),hs t ht,hf t ht]
  rfl

/-- Endpoint correction on the slow initial data. Both decaying factors
are kept explicitly, as required in (future-kernel-graph). -/
noncomputable def kernel : E →L[ℝ] E :=
  -((A.map 0 n).comp (C.J.comp (C.P.comp ((A.map n 0).comp (B.slow 0)))))

lemma kernel_factor : C.kernel=
    -(((A.map 0 n).comp (B.fast n)).comp
      (C.J.comp (C.P.comp ((A.map n 0).comp (B.slow 0))))) := by
  unfold kernel
  congr 1
  ext v
  change A.map 0 n (C.J (C.P (A.map n 0 (B.slow 0 v))))=
    A.map 0 n (B.fast n (C.J (C.P (A.map n 0 (B.slow 0 v)))))
  rw [C.fast_J]

lemma kernel_norm {G g : ℝ} (hG : 0 ≤ G)
    (hback : ‖(A.map 0 n).comp (B.fast n)‖ ≤ G*Real.exp (-g*n))
    (hforw : ‖(A.map n 0).comp (B.slow 0)‖ ≤ G*Real.exp (-g*n))
    (hJ : ‖C.J‖ ≤ 2) (hP : ‖C.P‖ ≤ 1) :
    ‖C.kernel‖ ≤ 2*G^2*Real.exp (-2*g*n) := by
  rw [C.kernel_factor,norm_neg]
  calc
    _ ≤ ‖(A.map 0 n).comp (B.fast n)‖*(‖C.J‖*(‖C.P‖*‖(A.map n 0).comp (B.slow 0)‖)) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (G*Real.exp (-g*n))*(2*(1*(G*Real.exp (-g*n)))) := by gcongr
    _ = 2*G^2*Real.exp (-2*g*n) := by
      rw [show -2*g*(n:ℝ)=(-g*n)+(-g*n) by ring,Real.exp_add]
      ring

end Terminal
end Splitting
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def evolution (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) :
    FiniteGreen.Evolution (EuclideanSpace ℝ (Fin d)) where
  map t s := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  self t := by
    rw [transition_self U V lam hUV]
    exact map_one _
  compose t s u := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam u s)=_
    rw [←map_mul,transition_comp U V lam hVU]

noncomputable def splitting (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d)) :
    FiniteGreen.Splitting (evolution U V lam hUV hVU) where
  slow t := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)
  fast t := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)
  slow_idem t := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)=_
    rw [←map_mul,projection_idem U V hVU]
  fast_idem t := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)=_
    rw [←map_mul,projection_idem U V hVU]
  add t := by
    rw [←map_add,projection_compl U V hUV]
    exact map_one _
  slow_inv t s := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s)
    rw [←map_mul,←map_mul,transition_projection U V lam hVU]
  fast_inv t s := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ s)
    rw [←map_mul,←map_mul,transition_projection U V lam hVU]

lemma forward_decay (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))
    {K g : ℝ} {s t : ℕ} (hst : s ≤ t)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V s‖ ≤ Real.exp K)
    (hgap : ∀ j∈S,lam j ≤ -g) :
    ‖((evolution U V lam hUV hVU).map t s).comp
      ((splitting U V lam hUV hVU S).slow s)‖ ≤
      Real.exp (2*K)*Real.exp (-g*((t:ℝ)-s)) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s)‖ ≤ _
  rw [←map_mul,Matrix.l2_opNorm_toEuclideanCLM,←Real.exp_add]
  convert norm_transition_projection U V hVU lam S s t hst hU hV hgap using 1
  congr 1
  ring

lemma backward_decay (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))
    {K g : ℝ} {s t : ℕ} (hst : s ≤ t)
    (hU : ‖U s‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K)
    (hgap : ∀ j∈Sᶜ,g ≤ lam j) :
    ‖((evolution U V lam hUV hVU).map s t).comp
      ((splitting U V lam hUV hVU S).fast t)‖ ≤
      Real.exp (2*K)*Real.exp (-g*((t:ℝ)-s)) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam t s)*
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)‖ ≤ _
  rw [←map_mul,Matrix.l2_opNorm_toEuclideanCLM,←Real.exp_add]
  convert norm_backward_projection U V hVU lam Sᶜ s t hst hU hV hgap using 1
  congr 1
  ring

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))

lemma splitting_slow_norm {K : ℝ} (t : ℕ)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    ‖(splitting U V lam hUV hVU S).slow t‖≤Real.exp (2*K) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)‖≤_
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_projection U V S t hU hV

lemma splitting_fast_norm {K : ℝ} (t : ℕ)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    ‖(splitting U V lam hUV hVU S).fast t‖≤Real.exp (2*K) := by
  exact splitting_slow_norm U V lam hUV hVU Sᶜ t hU hV

/-- The genuine unweighted Green bounds do not require negative slow rates.
Their growth is only the threshold times the window, not the largest rate. -/
theorem unweighted_bounds {K a : ℝ} {n : ℕ} (ha : 0≤a)
    (hU : ∀ t≤n,‖U t‖≤Real.exp K) (hV : ∀ t≤n,‖V t‖≤Real.exp K)
    (hs : ∀ j∈S,lam j≤a) (hf : ∀ j∈Sᶜ,-a≤lam j) :
    (∀ s t,s≤t → t≤n → ‖((evolution U V lam hUV hVU).map t s).comp
      ((splitting U V lam hUV hVU S).slow s)‖≤Real.exp (2*K+a*n)) ∧
    (∀ s t,s≤t → t≤n → ‖((evolution U V lam hUV hVU).map s t).comp
      ((splitting U V lam hUV hVU S).fast t)‖≤Real.exp (2*K+a*n)) := by
  have ht (s t : ℕ) (htn : t≤n) : a*((t:ℝ)-s)≤a*n := by
    have hh : (t:ℝ)≤n := by exact_mod_cast htn
    nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  constructor
  · intro s t hst htn
    have hh := forward_decay U V lam hUV hVU S (g:=-a) hst (hU t htn)
      (hV s (hst.trans htn)) (by simpa only [neg_neg] using hs)
    simp only [neg_neg] at hh
    apply hh.trans
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add le_rfl (ht s t htn))
  · intro s t hst htn
    have hh := backward_decay U V lam hUV hVU S (g:=-a) hst
      (hU s (hst.trans htn)) (hV t htn) hf
    simp only [neg_neg] at hh
    apply hh.trans
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add le_rfl (ht s t htn))

/-- At the full endpoints the threshold cancels between slow forward and
fast inverse growth, including the positive-slow case. -/
theorem endpoint_gap_bounds {K γ g : ℝ} (n : ℕ)
    (hU : ∀ t≤n,‖U t‖≤Real.exp K) (hV : ∀ t≤n,‖V t‖≤Real.exp K)
    (hs : ∀ j∈S,lam j≤γ-g) (hf : ∀ j∈Sᶜ,γ+g≤lam j) :
    ‖((evolution U V lam hUV hVU).map n 0).comp
      ((splitting U V lam hUV hVU S).slow 0)‖≤Real.exp (2*K)*Real.exp ((γ-g)*n) ∧
    ‖((evolution U V lam hUV hVU).map 0 n).comp
      ((splitting U V lam hUV hVU S).fast n)‖≤Real.exp (2*K)*Real.exp (-(γ+g)*n) := by
  constructor
  · simpa only [Nat.cast_zero,sub_zero,neg_neg] using
      forward_decay U V lam hUV hVU S (g:=-(γ-g)) (Nat.zero_le n)
        (hU n le_rfl) (hV 0 (Nat.zero_le n)) (by simpa only [neg_neg] using hs)
  · simpa only [Nat.cast_zero,sub_zero] using
      backward_decay U V lam hUV hVU S (g:=γ+g) (Nat.zero_le n)
        (hU 0 (Nat.zero_le n)) (hV n le_rfl) hf
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Evolution E} (B : Splitting A)

lemma slow_range_self (t : ℕ) (x : (B.slow t).range) : B.slow t (x:E)=x := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.slow_self t y
lemma fast_range_self (t : ℕ) (x : (B.fast t).range) : B.fast t (x:E)=x := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.fast_self t y
lemma slow_fast_range (t : ℕ) (x : (B.fast t).range) : B.slow t (x:E)=0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.slow_fast t y
lemma fast_slow_range (t : ℕ) (x : (B.slow t).range) : B.fast t (x:E)=0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.fast_slow t y

/-- Exact middle-time complementary matching. No determinant or angle
nondegeneracy is assumed: it follows from the splitting identities. -/
noncomputable def referenceLinear (t : ℕ) : ((B.slow t).range × (B.fast t).range) ≃ₗ[ℝ] E where
  toFun x := (x.1:E)-(x.2:E)
  invFun x := (⟨B.slow t x,⟨x,rfl⟩⟩,⟨-B.fast t x,⟨-x,by simp⟩⟩)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change B.slow t ((x.1:E)-(x.2:E))=x.1
      rw [map_sub,B.slow_range_self,B.slow_fast_range,sub_zero]
    · apply Subtype.ext
      change -B.fast t ((x.1:E)-(x.2:E))=x.2
      rw [map_sub,B.fast_slow_range,B.fast_range_self,zero_sub,neg_neg]
  right_inv x := by
    change B.slow t x-(-B.fast t x)=x
    rw [sub_neg_eq_add,B.add_apply]
  map_add' x y := by change (x.1+y.1:E)-(x.2+y.2:E)=_; abel
  map_smul' c x := by change c • (x.1:E)-c • (x.2:E)=_; simp only [smul_sub,RingHom.id_apply]

variable [FiniteDimensional ℝ E]
noncomputable def referenceMatching (t : ℕ) : ((B.slow t).range × (B.fast t).range) ≃L[ℝ] E :=
  (B.referenceLinear t).toContinuousLinearEquiv

@[simp] lemma referenceMatching_apply (t : ℕ) (x : (B.slow t).range × (B.fast t).range) :
    B.referenceMatching t x=(x.1:E)-(x.2:E) := rfl

lemma referenceMatching_inverse_norm (t : ℕ) {K : ℝ}
    (hs : ‖B.slow t‖≤K) (hf : ‖B.fast t‖≤K) :
    ‖(B.referenceMatching t).symm.toContinuousLinearMap‖≤K := by
  have hK : 0≤K := (norm_nonneg (B.slow t)).trans hs
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  change ‖((⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range),
    (⟨-B.fast t x,⟨-x,by simp⟩⟩ : (B.fast t).range))‖≤K*‖x‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · exact ((B.slow t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))
  · change ‖-B.fast t x‖≤K*‖x‖
    rw [norm_neg]
    exact ((B.fast t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg x))
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def restrictProjection (U V : Submodule ℝ E) : U →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp U.subtypeL

/-- Equal-dimensional close spaces have a quantitatively invertible endpoint
projection. This includes zero and full spaces without a separate convention. -/
lemma lower (U V : Submodule ℝ E) (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) (x : U) :
    ‖x‖ ≤ 2*‖restrictProjection U V x‖ := by
  have he : (U.starProjection-V.starProjection) x=(x:E)-V.starProjection x := by
    simp only [_root_.sub_apply,U.starProjection_eq_self_iff.mpr x.property]
  have hn := (U.starProjection-V.starProjection).le_opNorm (x:E)
  rw [he] at hn
  have hne : ‖(x:E)-V.starProjection x‖ ≤ (1/2:ℝ)*‖x‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have hh : ‖x‖ ≤ ‖(x:E)-V.starProjection x‖+‖V.starProjection x‖ := by
    calc
      _ = ‖((x:E)-V.starProjection x)+V.starProjection x‖ := by rw [sub_add_cancel]; rfl
      _ ≤ _ := norm_add_le _ _
  change ‖x‖ ≤ 2*‖V.starProjection x‖
  linarith

lemma injective (U V : Submodule ℝ E) (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) :
    Function.Injective (restrictProjection U V) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := lower U V hclose (x-y)
  rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
  exact le_antisymm hh (norm_nonneg _)

noncomputable def equiv (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) : U ≃L[ℝ] V :=
  (LinearMap.linearEquivOfInjective (restrictProjection U V).toLinearMap
    (injective U V hclose) hdim).toContinuousLinearEquiv

@[simp] lemma equiv_apply (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) (x : U) :
    equiv U V hdim hclose x=restrictProjection U V x := rfl

lemma inverse_norm (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) :
    ‖(equiv U V hdim hclose).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply (equiv U V hdim hclose).symm.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro y
  have hh := lower U V hclose ((equiv U V hdim hclose).symm y)
  rwa [←equiv_apply U V hdim hclose,(equiv U V hdim hclose).apply_symm_apply] at hh

end SmoothObstruction.CloseProjection

namespace SmoothObstruction.BoundaryNeumann
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine inverse for an explicitly estimated perturbation of an
invertible matching map. This is the Neumann step in source (4.15),
with no bijectivity hypothesis on the perturbed map. -/
noncomputable def perturb (L : E ≃L[ℝ] F) (D : E →L[ℝ] F)
    (h : ‖L.symm.toContinuousLinearMap.comp D‖ < 1) : E ≃L[ℝ] F :=
  (ContinuousLinearEquiv.ofUnit (Units.oneSub (-(L.symm.toContinuousLinearMap.comp D))
    (by simpa only [norm_neg] using h))).trans L

lemma perturb_apply (L : E ≃L[ℝ] F) (D : E →L[ℝ] F)
    (h : ‖L.symm.toContinuousLinearMap.comp D‖ < 1) (x : E) :
    perturb L D h x=L x+D x := by
  change L (x - -(L.symm (D x)))=L x+D x
  rw [sub_neg_eq_add,map_add,L.apply_symm_apply]

omit [CompleteSpace E] in
lemma inverse_bound (L M : E ≃L[ℝ] F) (D : E →L[ℝ] F) {K : ℝ}
    (hM : ∀ x,M x=L x+D x)
    (hK : ‖L.symm.toContinuousLinearMap‖ ≤ K)
    (hD : ‖L.symm.toContinuousLinearMap.comp D‖ ≤ 1/2) :
    ‖M.symm.toContinuousLinearMap‖ ≤ 2*K := by
  have hKn : 0 ≤ K := (norm_nonneg _).trans hK
  apply ContinuousLinearMap.opNorm_le_bound M.symm.toContinuousLinearMap (by positivity)
  intro y
  let x := M.symm y
  have he : x+L.symm (D x)=L.symm y := by
    have hh := M.apply_symm_apply y
    change M x=y at hh
    rw [hM] at hh
    have hh' := congrArg L.symm hh
    simpa only [map_add,L.symm_apply_apply] using hh'
  have hnx : ‖x‖ ≤ ‖L.symm y‖+‖L.symm (D x)‖ := by
    calc
      _ = ‖L.symm y-L.symm (D x)‖ := by rw [←he,add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hny : ‖L.symm y‖ ≤ K*‖y‖ :=
    (L.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hdx : ‖L.symm (D x)‖ ≤ (1/2:ℝ)*‖x‖ :=
    ((L.symm.toContinuousLinearMap.comp D).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  change ‖x‖ ≤ _
  linarith

lemma inverse_norm (L : E ≃L[ℝ] F) (D : E →L[ℝ] F) {K : ℝ}
    (hK : ‖L.symm.toContinuousLinearMap‖ ≤ K)
    (hD : ‖L.symm.toContinuousLinearMap.comp D‖ ≤ 1/2) :
    ‖(perturb L D (hD.trans_lt (by norm_num))).symm.toContinuousLinearMap‖ ≤ 2*K :=
  inverse_bound L _ D (perturb_apply L D _) hK hD

end SmoothObstruction.BoundaryNeumann

namespace SmoothObstruction.CloseComplement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def difference (U V : Submodule ℝ E) : U × V →L[ℝ] E :=
  (U.subtypeL.comp (ContinuousLinearMap.fst ℝ U V))-
  (V.subtypeL.comp (ContinuousLinearMap.snd ℝ U V))

omit [FiniteDimensional ℝ E] in
@[simp] lemma difference_apply (U V : Submodule ℝ E) (x : U × V) :
    difference U V x=(x.1:E)-(x.2:E) := rfl

/-- A pair of spaces close to a quantitatively complementary reference pair
is genuinely complementary. The inverse is constructed by Neumann inversion
on the reference product, and its norm is controlled. -/
theorem exists_matching (U₀ V₀ U V : Submodule ℝ E)
    (L₀ : (U₀ × V₀) ≃L[ℝ] E) (hL₀ : ∀ x,L₀ x=(x.1:E)-(x.2:E))
    (hdU : Module.finrank ℝ U₀=Module.finrank ℝ U)
    (hdV : Module.finrank ℝ V₀=Module.finrank ℝ V)
    {ε K : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hcU : ‖U₀.starProjection-U.starProjection‖≤ε)
    (hcV : ‖V₀.starProjection-V.starProjection‖≤ε)
    (hK : ‖L₀.symm.toContinuousLinearMap‖≤K) (hsmall : K*(2*ε)≤1/2) :
    ∃ L : (U × V) ≃L[ℝ] E,(∀ x,L x=(x.1:E)-(x.2:E)) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*K := by
  let eU := CloseProjection.equiv U₀ U hdU (hcU.trans hεhalf)
  let eV := CloseProjection.equiv V₀ V hdV (hcV.trans hεhalf)
  let J : (U₀ × V₀) ≃L[ℝ] U × V := eU.prodCongr eV
  have hJ : ‖J.toContinuousLinearMap‖≤1 := by
    apply J.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro x
    rw [one_mul,Prod.norm_def,max_le_iff]
    constructor
    · change ‖U.starProjection (x.1:E)‖≤‖x‖
      exact (Submodule.norm_starProjection_apply_le _ _).trans (norm_fst_le x)
    · change ‖V.starProjection (x.2:E)‖≤‖x‖
      exact (Submodule.norm_starProjection_apply_le _ _).trans (norm_snd_le x)
  have hdiffU (x : U₀) : ‖(eU x:E)-(x:E)‖≤ε*‖x‖ := by
    have h := (U₀.starProjection-U.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,U₀.starProjection_eq_self_iff.mpr x.property] at h
    change ‖U.starProjection (x:E)-(x:E)‖≤ε*‖x‖
    rw [norm_sub_rev]
    exact h.trans (mul_le_mul_of_nonneg_right hcU (norm_nonneg _))
  have hdiffV (x : V₀) : ‖(eV x:E)-(x:E)‖≤ε*‖x‖ := by
    have h := (V₀.starProjection-V.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,V₀.starProjection_eq_self_iff.mpr x.property] at h
    change ‖V.starProjection (x:E)-(x:E)‖≤ε*‖x‖
    rw [norm_sub_rev]
    exact h.trans (mul_le_mul_of_nonneg_right hcV (norm_nonneg _))
  let D := (difference U V).comp J.toContinuousLinearMap-L₀.toContinuousLinearMap
  have hD : ‖D‖≤2*ε := by
    apply D.opNorm_le_bound (by positivity)
    intro x
    change ‖difference U V (J x)-L₀ x‖≤(2*ε)*‖x‖
    rw [difference_apply,hL₀]
    have he : ((J x).1:E)-((J x).2:E)-((x.1:E)-(x.2:E))=
      ((eU x.1:E)-(x.1:E))-((eV x.2:E)-(x.2:E)) := by
        change (eU x.1:E)-(eV x.2:E)-((x.1:E)-(x.2:E))=_
        abel
    rw [he]
    calc
      _ ≤ ‖(eU x.1:E)-(x.1:E)‖+‖(eV x.2:E)-(x.2:E)‖ := norm_sub_le _ _
      _ ≤ ε*‖x.1‖+ε*‖x.2‖ := add_le_add (hdiffU _) (hdiffV _)
      _ ≤ ε*‖x‖+ε*‖x‖ := by gcongr <;> [exact norm_fst_le x; exact norm_snd_le x]
      _ = _ := by ring
  have hKn : 0≤K := (norm_nonneg L₀.symm.toContinuousLinearMap).trans hK
  have hsmall' : ‖L₀.symm.toContinuousLinearMap.comp D‖≤1/2 := by
    apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    exact (mul_le_mul hK hD (norm_nonneg D) hKn).trans hsmall
  let M := BoundaryNeumann.perturb L₀ D (hsmall'.trans_lt (by norm_num))
  let L := J.symm.trans M
  refine ⟨L,?_,?_⟩
  · intro x
    change M (J.symm x)=(x.1:E)-(x.2:E)
    rw [BoundaryNeumann.perturb_apply]
    change L₀ (J.symm x)+(difference U V (J (J.symm x))-L₀ (J.symm x))=_
    rw [J.apply_symm_apply,difference_apply]
    abel
  · have hMi : ‖M.symm.toContinuousLinearMap‖≤2*K := BoundaryNeumann.inverse_norm L₀ D hK hsmall'
    change ‖J.toContinuousLinearMap.comp M.symm.toContinuousLinearMap‖≤2*K
    apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    exact (mul_le_mul hJ hMi (norm_nonneg M.symm.toContinuousLinearMap) zero_le_one).trans_eq (one_mul _)

end SmoothObstruction.CloseComplement

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : Evolution E} (B : Splitting A)

/-- Fixed endpoint-bin orthogonal projection, together with its genuine
inverse on the moving fast space. Empty endpoint spaces are included. -/
noncomputable def terminalProjection (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) : B.Terminal (H:=V) n where
  P := V.orthogonalProjectionOnto
  J := (B.fast n).range.subtypeL.comp
    (CloseProjection.equiv (B.fast n).range V hdim hclose).symm.toContinuousLinearMap
  right := by
    ext x
    exact congrArg Subtype.val ((CloseProjection.equiv (B.fast n).range V hdim hclose).apply_symm_apply x)
  left := by
    ext x
    let v : (B.fast n).range := ⟨B.fast n x,⟨x,rfl⟩⟩
    change ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm
      (CloseProjection.equiv (B.fast n).range V hdim hclose v):E)=(v:E)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  range := by
    ext x
    change B.fast n (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)=_
    have hv := ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x).property
    obtain ⟨v,hv⟩ := hv
    change B.fast n (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)=
      (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)
    change B.fast n v=(((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E) at hv
    rw [←hv,B.fast_self]

lemma terminalProjection_P_norm (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) :
    ‖(B.terminalProjection n V hdim hclose).P‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖V.starProjection x‖≤1*‖x‖
  rw [one_mul]
  exact Submodule.norm_starProjection_apply_le _ _

lemma terminalProjection_J_norm (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) :
    ‖(B.terminalProjection n V hdim hclose).J‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(CloseProjection.equiv (B.fast n).range V hdim hclose).symm x‖≤2*‖x‖
  apply ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm.toContinuousLinearMap.le_opNorm x).trans
  exact mul_le_mul_of_nonneg_right (CloseProjection.inverse_norm _ _ hdim hclose) (norm_nonneg x)
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.FiniteGreen.Splitting.Terminal
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {A : Evolution E} {B : Splitting A} {n : ℕ} (C : B.Terminal (H:=H) n)

/-- The endpoint graph correction is small even when the slow rates are
positive. The two complementary exponentials cancel their threshold,
leaving the spectral gap; no hyperbolic sign assumption was added. -/
lemma kernel_norm_gap {G g γ : ℝ} (hG : 0≤G)
    (hback : ‖(A.map 0 n).comp (B.fast n)‖≤G*Real.exp (-(γ+g)*n))
    (hforw : ‖(A.map n 0).comp (B.slow 0)‖≤G*Real.exp ((γ-g)*n))
    (hJ : ‖C.J‖≤2) (hP : ‖C.P‖≤1) :
    ‖C.kernel‖≤2*G^2*Real.exp (-2*g*n) := by
  rw [C.kernel_factor,norm_neg]
  calc
    _ ≤ ‖(A.map 0 n).comp (B.fast n)‖*(‖C.J‖*(‖C.P‖*‖(A.map n 0).comp (B.slow 0)‖)) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (G*Real.exp (-(γ+g)*n))*(2*(1*(G*Real.exp ((γ-g)*n)))) := by gcongr
    _ = 2*G^2*Real.exp (-2*g*n) := by
      rw [show -2*g*(n:ℝ)=-(γ+g)*n+(γ-g)*n by ring,Real.exp_add]
      ring
end SmoothObstruction.FiniteGreen.Splitting.Terminal

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ} (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))

lemma splitting_slow_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).slow t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) S := by
  ext x
  rw [groupSpace_fixed]
  constructor
  · rintro ⟨y,rfl⟩
    exact (splitting U V lam hUV hVU S).slow_self t y
  · intro hx
    exact ⟨x,hx⟩

lemma splitting_fast_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).fast t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) Sᶜ :=
  splitting_slow_range U V lam hUV hVU Sᶜ t
end SmoothObstruction.EuclideanSplitting

end

end OAI
