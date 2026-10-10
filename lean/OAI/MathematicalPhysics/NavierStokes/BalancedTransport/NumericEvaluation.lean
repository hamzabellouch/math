import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericBounds

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma magnitude (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (C : ℕ) (s : List ℝ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |x i| ≤ C) (hb : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : Valid o s) : |real d o x s| ≤ ((bound o C b).1 : ℝ) := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb a
  have hB := hb b'
  fin_cases j <;>
    dsimp +instances only [real, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact rat_abs_le_num r
  · exact hi _
  · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
  · simpa only [Nat.cast_mul, abs_mul] using mul_le_mul hA hB (abs_nonneg _) (by positivity)
  · simpa only [abs_neg] using hA
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
    simpa only [inv_inv] using inv_anti₀ hpos hh
  · exact rhoJet_bound_computable _ _
  · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
  · split_ifs with hr
    · exact log_abs_bound hr
    · simpa only [abs_zero] using (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ))

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def realFrom (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) : List ℝ :=
  p.foldl (fun s o => o.real d x s :: s) s

def rationalFrom (p : NumericProgram) (x : Fin d → ℚ) (n : ℕ) (s : List ℚ) : List ℚ :=
  p.foldl (fun s o => o.rational d x n s :: s) s

def boundFrom (p : NumericProgram) (C : ℕ) (s : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  p.foldl (fun s o => o.bound C s :: s) s

def ValidFrom (x : Fin d → ℝ) : NumericProgram → List ℝ → Prop
  | [], _ => True
  | o :: p, s => o.Valid s ∧ ValidFrom x p (o.real d x s :: s)

def Valid (p : NumericProgram) (x : Fin d → ℝ) : Prop := ValidFrom x p []

def real (p : NumericProgram) (x : Fin d → ℝ) : ℝ := (p.realFrom x []).getD 0 0

def bound (p : NumericProgram) (C : ℕ) : ℕ × ℕ := (p.boundFrom C []).getD 0 (0,0)

def approximation (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ) : ℚ :=
  (p.rationalFrom x (n + (p.bound C).2) []).getD 0 0

lemma boundFrom_estimate (p : NumericProgram) (x : Fin d → ℚ) (s : List ℝ)
    (q : List ℚ) (b : List (ℕ × ℕ)) (n C : ℕ) (hi : ∀ i, |(x i : ℝ)| ≤ C)
    (hh : RegisterEstimate n s q b) (hv : p.ValidFrom (fun i => (x i : ℝ)) s) :
    RegisterEstimate n (p.realFrom (fun i => (x i : ℝ)) s) (p.rationalFrom x n q)
      (p.boundFrom C b) := by
  induction p generalizing s q b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ _ ?_ hv.2
    have hb := o.estimate d x n C s q b hi hh hv.1
    constructor
    · intro j
      cases j with
      | zero => exact hb.1
      | succ j => exact hh.magnitude j
    · intro j
      cases j with
      | zero => exact hb.2
      | succ j => exact hh.accuracy j

lemma boundFrom_magnitude (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ)
    (b : List (ℕ × ℕ)) (C : ℕ) (hi : ∀ i, |x i| ≤ C)
    (hh : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : p.ValidFrom x s) :
    ∀ j, |(p.realFrom x s).getD j 0| ≤ (((p.boundFrom C b).getD j (0,0)).1 : ℝ) := by
  induction p generalizing s b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ ?_ hv.2
    intro j
    cases j with
    | zero => exact o.magnitude d x C s b hi hh hv.1
    | succ j => exact hh j

lemma approximation_spec (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ)
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hv : p.Valid (fun i => (x i : ℝ))) :
    |(p.approximation C x n : ℝ) - p.real (fun i => (x i : ℝ))| ≤ error n := by
  have hb := p.boundFrom_estimate x [] [] [] (n + (p.bound C).2) C hi
    ⟨by simp, by simp⟩ hv
  exact (hb.accuracy 0).trans (nat_mul_error_shift _ _)

lemma magnitude (p : NumericProgram) (C : ℕ) (x : Fin d → ℝ)
    (hi : ∀ i, |x i| ≤ C) (hv : p.Valid x) : |p.real x| ≤ ((p.bound C).1 : ℝ) :=
  p.boundFrom_magnitude x [] [] C hi (by simp) hv 0

lemma computable_rationalStep (d : ℕ) [NeZero d] :
    Computable (fun z : (NumericProgram × (Fin d → ℚ) × ℕ × List ℚ) × (List ℚ × NumericOp) =>
      z.2.2.rational d z.1.2.1 z.1.2.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have ho : Computable (fun z : A × (List ℚ × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hx : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hp : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hs : Computable (fun z : A × (List ℚ × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := (NumericOp.computable_rational d).comp (ho.pair (hx.pair (hp.pair hs)))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_rationalFrom (d : ℕ) [NeZero d] :
    Computable (fun z : NumericProgram × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalFrom z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact computable_foldl hf hg (computable_rationalStep d).to₂

lemma computable_boundStep : Computable
    (fun z : (NumericProgram × ℕ × List (ℕ × ℕ)) × (List (ℕ × ℕ) × NumericOp) =>
      z.2.2.bound z.1.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have ho : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hC : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := NumericOp.computable_bound.comp (ho.pair (hC.pair hs))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_boundFrom : Computable
    (fun z : NumericProgram × ℕ × List (ℕ × ℕ) => boundFrom z.1 z.2.1 z.2.2) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2) := Computable.snd.comp Computable.snd
  exact computable_foldl hf hg computable_boundStep.to₂

lemma computable_bound : Computable₂ bound := by
  exact ((Primrec.list_getD (0,0)).to_comp.comp
    (computable_boundFrom.comp (Computable.fst.pair (Computable.snd.pair (Computable.const []))))
    (Computable.const 0))

lemma computable_approximation (d : ℕ) [NeZero d] : Computable
    (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ =>
      approximation z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have herr : Computable (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ => (z.1.bound z.2.1).2) := Computable.snd.comp (computable_bound.comp Computable.fst (Computable.fst.comp Computable.snd))
  exact (Primrec.list_getD (0 : ℚ)).to_comp.comp
    ((computable_rationalFrom d).comp (Computable.fst.pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Primrec.nat_add.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) herr).pair
          (Computable.const []))))) (Computable.const 0)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
