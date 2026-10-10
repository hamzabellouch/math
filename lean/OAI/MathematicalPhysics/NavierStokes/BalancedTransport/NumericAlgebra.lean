import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericJets
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputabilityRules

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma computable_dual : Computable (fun z : Fin d × NumericOp => z.2.dual d z.1) := by
  have hi : Computable (fun a : ℕ => Fin.ofNat d a) :=
    (Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))).to_comp
  have he : Computable (fun z : Fin d × NumericOp => decide (Fin.ofNat d z.2.left = z.1)) :=
    Primrec.eq.decide.to_comp.comp (hi.comp (by unfold left; fun_prop)) Computable.fst
  have hb : Computable (fun z : Fin d × NumericOp =>
      if Fin.ofNat d z.2.left = z.1 then (1:ℚ) else 0) :=
    computable_ite he (Computable.const 1) (Computable.const 0)
  have hc (j : Fin 9) : Computable (fun z : Fin d × NumericOp =>
      dualCase d z.1 j z.2) := by
    fin_cases j <;> dsimp only [dualCase, left, right] <;> fun_prop
  exact computable_fin_cases (i := fun z => z.2.tag) (by unfold tag; fun_prop) hc

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma computable_jetStep : Computable (fun z : Fin d × NumericProgram => z.2.jetStep z.1) := by
  unfold jetStep
  have hd : Computable (fun z : (Fin d × NumericProgram) × NumericOp => z.2.dual d z.1.1) :=
    Computable.comp (f := fun z : Fin d × NumericOp => z.2.dual d z.1)
      (g := fun z : (Fin d × NumericProgram) × NumericOp => (z.1.1,z.2))
      (NumericOp.computable_dual d) (by fun_prop)
  exact ComputableRules.flatMapList (f := fun z : Fin d × NumericProgram => z.2)
    (g := fun z o => o.dual d z.1) Computable.snd
    hd

def literal (q : ℚ) : NumericProgram := [(0,q,0,0)]

def coordinate (k : Fin d) : NumericProgram := [(1,0,k.val,0)]

def unary (j : Fin 9) (n : ℕ) (p : NumericProgram) : NumericProgram := p ++ [(j,0,0,n)]

def binary (j : Fin 9) (p q : NumericProgram) : NumericProgram :=
  (p ++ q) ++ [(j,0,q.length,0)]

lemma literal_closed (q : ℚ) : (literal q).Closed := by trivial

lemma literal_valid (q : ℚ) (x : Fin d → ℝ) : (literal q).Valid x := by
  simp [literal, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma literal_real (q : ℚ) (x : Fin d → ℝ) : (literal q).real x = q := rfl

omit [NeZero d] in
lemma coordinate_closed (k : Fin d) : (coordinate k).Closed := by trivial

lemma coordinate_valid (k : Fin d) (x : Fin d → ℝ) : (coordinate k).Valid x := by
  simp [coordinate, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma coordinate_real (k : Fin d) (x : Fin d → ℝ) : (coordinate k).real x = x k := by
  simp [coordinate, real, realFrom, NumericOp.real, NumericOp.tag, NumericOp.left, Fin.ofNat_eq_cast]

lemma unary_real (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ) :
    (unary j n p).real x = NumericOp.real d (j,0,0,n) x (p.realFrom x []) := by
  simp [unary, real, realFrom, List.foldl_append]

lemma unary_valid (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ)
    (hp : p.Valid x) (hi : j = 5 → ((n+1:ℕ):ℝ)⁻¹ ≤ p.real x) :
    (unary j n p).Valid x := by
  exact (validFrom_concat _ _ _ _).mpr ⟨hp, ⟨hi, trivial⟩⟩

lemma unary_closed (j : Fin 9) (n : ℕ) (p : NumericProgram) (hp : p.Closed)
    (hne : p ≠ []) (hj : j = 4 ∨ j = 5 ∨ j = 7) : (unary j n p).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hne
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨hp, ?_⟩
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.left] using hn,trivial⟩

lemma realFrom_head {s : List ℝ} (hs : 0 < s.length) (t : List ℝ) :
    (s ++ t).getD 0 0 = s.getD 0 0 := by
  simp only [List.getD, List.getElem?_append_left hs]

lemma binary_real (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ [])
    (x : Fin d → ℝ) :
    (binary j p q).real x =
      NumericOp.real d (j,0,q.length,0) x (q.realFrom x [] ++ p.realFrom x []) := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons head tail =>
    simp only [binary, real, realFrom_concat]
    rw [realFrom_empty_append (head :: tail) hq]
    rfl

lemma binary_register_left (p q : NumericProgram) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD q.length 0 = p.real x := by
  have he := q.realFrom_length x []
  simp only [List.length_nil, Nat.add_zero] at he
  rw [← he]
  simp only [List.getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma binary_register_right (p q : NumericProgram) (hne : q ≠ []) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD 0 0 = q.real x := by
  apply realFrom_head
  simpa only [realFrom_length, List.length_nil, Nat.add_zero] using List.length_pos_iff.mpr hne

lemma binary_valid (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hj : j ≠ 5)
    (x : Fin d → ℝ) (hpv : p.Valid x) (hqv : q.Valid x) : (binary j p q).Valid x := by
  apply (validFrom_concat _ _ _ _).mpr
  refine ⟨(validFrom_concat _ _ _ _).mpr ⟨hpv,
    (validFrom_of_closed q hq x _).mpr hqv⟩, ?_⟩
  exact ⟨fun h => (hj h).elim, trivial⟩

lemma binary_closed (j : Fin 9) (p q : NumericProgram) (hp : p.Closed) (hq : q.Closed)
    (hnep : p ≠ []) (hneq : q ≠ []) (hj : j = 2 ∨ j = 3) : (binary j p q).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hnep
  have hqn : 0 < q.length := List.length_pos_iff.mpr hneq
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨(scopedFrom_concat _ _ _).mpr ⟨hp, q.scopedFrom_mono (Nat.zero_le _) hq⟩, ?_⟩
  rcases hj with rfl | rfl <;>
    simp only [ScopedFrom, NumericOp.Scoped, NumericOp.tag, NumericOp.left,
      NumericOp.right, List.length_append]
  all_goals exact ⟨⟨by omega, by omega⟩,trivial⟩

lemma binary_add_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 2 p q).real x = p.real x + q.real x := by
  rw [binary_real 2 p q hq hne]
  exact congrArg₂ (· + ·) (binary_register_left p q x) (binary_register_right p q hne x)

lemma binary_mul_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 3 p q).real x = p.real x * q.real x := by
  rw [binary_real 3 p q hq hne]
  exact congrArg₂ (· * ·) (binary_register_left p q x) (binary_register_right p q hne x)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
