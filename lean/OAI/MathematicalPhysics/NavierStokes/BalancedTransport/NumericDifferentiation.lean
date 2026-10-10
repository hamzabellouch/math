import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericEvaluation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

def differential (k : Fin d) (o : NumericOp) (s v : ℕ → ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => 0
  | 1 => if Fin.ofNat d a = k then 1 else 0
  | 2 => v a + v b
  | 3 => v a * s b + s a * v b
  | 4 => -v a
  | 5 => -(v a * (s a)⁻¹ ^ 2)
  | 6 => rhoJet (a+1) (s b) * v b
  | 7 => Real.exp (s a) * v a
  | 8 => 0

lemma hasDerivAt (k : Fin d) (o : NumericOp) (x : ℝ → Fin d → ℝ)
    (s : ℝ → List ℝ) (v : ℕ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (v a) t)
    (hv : o.Valid (s t)) :
    HasDerivAt (fun t => o.real d (x t) (s t))
      (o.differential d k (fun a => (s t).getD a 0) v) t := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> dsimp only [real, differential, tag, rat, left, right, Valid] at hv ⊢
  · exact hasDerivAt_const t _
  · exact hx _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hh : (s t).getD a 0 ≠ 0 := ne_of_gt ((by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)⁻¹).trans_le (hv rfl))
    apply HasDerivAt.congr_deriv ((hs a).inv hh)
    simp only [div_eq_mul_inv, inv_pow, neg_mul]
  · exact (rhoJet_hasDerivAt a ((s t).getD b 0)).comp t (hs b)
  · simpa only [mul_comm] using (hs a).exp
  · exact hasDerivAt_const t _

def dualCase (k : Fin d) (j : Fin 9) (o : NumericOp) : NumericProgram :=
  let a := o.left
  let b := o.right
  let z : NumericOp := (0,0,0,0)
  match j with
  | 0 => [o,z,z,z,z]
  | 1 => [o,z,z,z,(0,(if Fin.ofNat d a = k then 1 else 0),0,0)]
  | 2 => [(2,0,5*a+4,5*b+4),z,z,z,(2,0,5*a+4,5*b+4)]
  | 3 => [(3,0,5*a+4,5*b+4),(3,0,5*a+1,5*b+5),
      (3,0,5*a+6,5*b+2),z,(2,0,2,1)]
  | 4 => [(4,0,5*a+4,0),z,z,z,(4,0,5*a+4,0)]
  | 5 => [(5,0,5*a+4,b),z,(3,0,1,1),(3,0,5*a+3,0),(4,0,0,0)]
  | 6 => [(6,0,a,5*b+4),(6,0,a+1,5*b+5),z,z,(3,0,2,5*b+4)]
  | 7 => [(7,0,5*a+4,0),z,z,z,(3,0,3,5*a+4)]
  | 8 => [o,z,z,z,z]

def dual (k : Fin d) (o : NumericOp) : NumericProgram := dualCase d k o.tag o

lemma dual_drop (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (q : List ℝ) :
    ((o.dual d k).realFrom x q).drop 5 = q := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, tag]

lemma dual_value (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 4 0 = o.real d x s := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, real, tag, rat, left, right, h]

lemma dual_differential (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 0 0 =
      o.differential d k (fun a => s.getD a 0) (fun a => q.getD (5*a) 0) := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.realFrom, real, differential, tag, rat, left, right,
      Nat.add_assoc, h, pow_two]
  change (((if Fin.ofNat d a = k then 1 else 0) : ℚ) : ℝ) =
    (if Fin.ofNat d a = k then 1 else 0)
  by_cases hh : Fin.ofNat d a = k <;>
    simp only [hh, ite_true, ite_false, Rat.cast_one, Rat.cast_zero]

lemma dual_valid (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : o.Valid s) :
    (o.dual d k).ValidFrom x q := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ValidFrom, Valid, real, tag, rat, left, right, h] at hv ⊢
  exact hv

lemma differentiableAt (o : NumericOp) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : o.Valid (s x)) : DifferentiableAt ℝ (fun y => o.real d y (s y)) x := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> dsimp only [real, tag, rat, left, right, Valid] at hv ⊢
  · exact differentiableAt_const _
  · exact (differentiable_apply _).differentiableAt
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hh : (s x).getD a 0 ≠ 0 := ne_of_gt ((by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)⁻¹).trans_le (hv rfl))
    exact (hs a).inv hh
  · exact (rhoJet_hasDerivAt a _).differentiableAt.comp x (hs b)
  · exact (hs a).exp
  · exact differentiableAt_const _

end BalancedTransport.Effectivity.NumericOp
end

end OAI
