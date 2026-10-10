import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericDifferentiation
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_register (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s : List ℝ) (a : ℕ) :
    ((o.dual d k).realFrom x s).getD (5+a) 0 = s.getD a 0 := by
  have h := congrArg (fun l : List ℝ => l.getD a 0) (o.dual_drop d k x s)
  simpa [List.getD, List.getElem?_drop] using h

lemma dual_length (k : Fin d) (o : NumericOp) : (o.dual d k).length = 5 := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> rfl

lemma dual_scoped (k : Fin d) (o : NumericOp) {n : ℕ} (h : o.Scoped n) :
    (o.dual d k).ScopedFrom (5*n) := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ScopedFrom, Scoped, tag, left, right] at h ⊢
  all_goals omega

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def jetStep (k : Fin d) (p : NumericProgram) : NumericProgram :=
  p.flatMap (NumericOp.dual d k)

lemma jetStep_length (k : Fin d) (p : NumericProgram) : (p.jetStep k).length = 5*p.length := by
  induction p with
  | nil => rfl
  | cons o p ih => simp only [jetStep, List.flatMap_cons, List.length_append,
      NumericOp.dual_length, List.length_cons] at ih ⊢; omega

lemma jetStep_scoped (k : Fin d) (p : NumericProgram) {n : ℕ} (h : p.ScopedFrom n) :
    (p.jetStep k).ScopedFrom (5*n) := by
  induction p generalizing n with
  | nil => trivial
  | cons o p ih =>
    rw [jetStep, List.flatMap_cons, scopedFrom_concat, NumericOp.dual_length]
    exact ⟨o.dual_scoped d k h.1, by simpa [jetStep, Nat.mul_add] using ih h.2⟩

lemma jetStep_closed (k : Fin d) (p : NumericProgram) (h : p.Closed) :
    (p.jetStep k).Closed := p.jetStep_scoped k h

lemma jetStep_validFrom (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ)
    (s q : List ℝ) (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : p.ValidFrom x s) :
    (p.jetStep k).ValidFrom x q ∧
      ∀ a, ((p.jetStep k).realFrom x q).getD (5*a+4) 0 = (p.realFrom x s).getD a 0 := by
  induction p generalizing s q with
  | nil => exact ⟨trivial, h⟩
  | cons o p ih =>
    have ho := o.dual_valid d k x s q h hv.1
    have hh (a : ℕ) : ((o.dual d k).realFrom x q).getD (5*a+4) 0 =
        (o.real d x s :: s).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k x s q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5,
          List.getD_cons_succ] using (o.dual_register d k x q (5*a+4)).trans (h a)
    have hi := ih _ _ hh hv.2
    refine ⟨?_, ?_⟩
    · exact (validFrom_concat _ _ x q).mpr ⟨ho, hi.1⟩
    · simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
        List.foldl_cons, List.foldl_append] using hi.2

lemma jetStep_valid (k : Fin d) (p : NumericProgram) {x : Fin d → ℝ} (hv : p.Valid x) :
    (p.jetStep k).Valid x := (p.jetStep_validFrom k x [] [] (by simp) hv).1

lemma jetStep_hasDerivAtFrom (k : Fin d) (p : NumericProgram)
    (x : ℝ → Fin d → ℝ) (s : ℝ → List ℝ) (q : List ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (h : ∀ a, q.getD (5*a+4) 0 = (s t).getD a 0)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (q.getD (5*a) 0) t)
    (hv : p.ValidFrom (x t) (s t)) :
    ∀ a, HasDerivAt (fun t => (p.realFrom (x t) (s t)).getD a 0)
      (((p.jetStep k).realFrom (x t) q).getD (5*a) 0) t := by
  induction p generalizing s q with
  | nil => exact hs
  | cons o p ih =>
    let s' : ℝ → List ℝ := fun v => o.real d (x v) (s v) :: s v
    let q' : List ℝ := (o.dual d k).realFrom (x t) q
    have hh (a : ℕ) : q'.getD (5*a+4) 0 = (s' t).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k (x t) (s t) q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5, s', q',
          List.getD_cons_succ] using (o.dual_register d k (x t) q (5*a+4)).trans (h a)
    have hd (a : ℕ) : HasDerivAt (fun v => (s' v).getD a 0) (q'.getD (5*a) 0) t := by
      cases a with
      | zero =>
        change HasDerivAt (fun v => o.real d (x v) (s v))
          (((o.dual d k).realFrom (x t) q).getD 0 0) t
        rw [o.dual_differential d k (x t) (s t) q h]
        exact o.hasDerivAt d k x s _ t hx hs hv.1
      | succ a =>
        change HasDerivAt (fun v => (s v).getD a 0)
          (((o.dual d k).realFrom (x t) q).getD (5*(a+1)) 0) t
        rw [show 5*(a+1)=5+5*a by omega, o.dual_register d k]
        exact hs a
    have hi := ih s' q' hh hd hv.2
    simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
      List.foldl_cons, List.foldl_append, s', q'] using hi

lemma differentiableAtFrom (p : NumericProgram) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : p.ValidFrom x (s x)) :
    ∀ a, DifferentiableAt ℝ (fun y => (p.realFrom y (s y)).getD a 0) x := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun y => o.real d y (s y) :: s y) ?_ hv.2
    intro a
    cases a with
    | zero => exact o.differentiableAt d x s hs hv.1
    | succ a => exact hs a

lemma differentiableAt (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    DifferentiableAt ℝ p.real x :=
  p.differentiableAtFrom x (fun _ => []) (fun _ => differentiableAt_const _) hv 0

lemma jetStep_real (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    (p.jetStep k).real x = fderiv ℝ p.real x (Pi.single k 1) := by
  let y : ℝ → Fin d → ℝ := fun t => x + t • Pi.single k 1
  have hy (i : Fin d) : HasDerivAt (fun t => y t i) (if i=k then 1 else 0) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single k (1:ℝ) : Fin d → ℝ) i))
    simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.const_apply, Pi.mul_apply, id_eq, mul_ite, mul_one, mul_zero, eq_comm, Pi.add_def, zero_add] using h
  have he : y 0 = x := by simp [y]
  have hh := p.jetStep_hasDerivAtFrom k y (fun _ => []) [] 0 hy (by simp)
    (by intro a; simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by change p.Valid (y 0); rw [he]; exact hv) 0
  have hf := (p.differentiableAt x hv).hasFDerivAt.hasLineDerivAt (Pi.single k 1)
  exact HasDerivAt.unique (by simpa only [real, he, Nat.mul_zero] using hh) hf

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
