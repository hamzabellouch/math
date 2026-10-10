import OAI.MathematicalPhysics.Heisenberg.BoundaryPartition

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Matrix.Norms.Operator
namespace Heisenberg.SlotColor
variable {V : Type*}
abbrev Color := V → Bool
abbrev Cycles (π : Equiv.Perm V) := Quotient (Equiv.Perm.SameCycle.setoid π)

def cycleOf (π : Equiv.Perm V) (i : V) : Cycles π := Quotient.mk _ i

@[simp] lemma cycleOf_apply (π : Equiv.Perm V) (i : V) : cycleOf π (π i) = cycleOf π i :=
  Quotient.sound ((Equiv.Perm.SameCycle.refl π i).apply_left)

def permute (π : Equiv.Perm V) : Equiv.Perm (Color (V:=V)) where
  toFun c := c ∘ π.symm
  invFun c := c ∘ π
  left_inv c := by ext i; simp
  right_inv c := by ext i; simp

@[simp] lemma permute_apply (π : Equiv.Perm V) (c : Color (V:=V)) (i : V) :
    permute π c i = c (π.symm i) := rfl

lemma permute_mul (π ρ : Equiv.Perm V) : permute (π*ρ) = permute π * permute ρ := by
  ext c i
  rfl

lemma permute_fixed (π : Equiv.Perm V) (c : Color (V:=V)) :
    permute π c = c ↔ ∀ i, c (π i) = c i := by
  constructor
  · intro h i
    have he := congrFun h (π i)
    simpa using he.symm
  · intro h
    ext i
    have he := h (π.symm i)
    simpa using he.symm

variable [Fintype V]

def matrix (π : Equiv.Perm V) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  fun c b => if permute π b = c then 1 else 0

lemma matrix_one : matrix (1 : Equiv.Perm V) = 1 := by
  ext c b
  have he : permute (1 : Equiv.Perm V) b = b := by ext i; rfl
  simp [matrix,he,Matrix.one_apply,eq_comm]

lemma matrix_mul (π ρ : Equiv.Perm V) : matrix (π*ρ) = matrix π * matrix ρ := by
  ext c b
  simp only [matrix,Matrix.mul_apply,permute_mul,Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (permute ρ b)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

def representation : Equiv.Perm V →* Matrix (Color (V:=V)) (Color (V:=V)) ℝ where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

lemma trace_diagonal (π : Equiv.Perm V) (f : Color (V:=V) → ℝ) :
    Matrix.trace (matrix π * Matrix.diagonal f) =
      ∑ c, if ∀ i, c (π i) = c i then f c else 0 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal,matrix,permute_fixed]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

abbrev ClosedColor (π : Equiv.Perm V) := {c : Color (V:=V) // ∀ i, c (π i) = c i}
instance (π : Equiv.Perm V) : Fintype (ClosedColor π) := Fintype.ofFinite _
instance (π : Equiv.Perm V) : Fintype (Cycles π) := Fintype.ofFinite _

lemma const_cycle (π : Equiv.Perm V) (c : ClosedColor π) {i j : V}
    (h : π.SameCycle i j) : c.val i = c.val j := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hh : ∀ n, c.val ((π^n) i) = c.val i := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,c.property,ih]
  rw [← hn,hh]

def cycleColorEquiv (π : Equiv.Perm V) : (Cycles π → Bool) ≃ ClosedColor π where
  toFun c := ⟨fun i => c (cycleOf π i),fun i => by simp⟩
  invFun c := Quotient.lift c.val (fun _ _ h => const_cycle π c h)
  left_inv c := by
    funext q
    induction q using Quotient.inductionOn with | _ i => rfl
  right_inv c := by ext i; rfl

theorem trace_cycle_colors (π : Equiv.Perm V) (f : Color (V:=V) → ℝ) :
    Matrix.trace (matrix π * Matrix.diagonal f) =
      ∑ ε : Cycles π → Bool, f (fun i => ε (cycleOf π i)) := by
  rw [trace_diagonal]
  calc
    _ = ∑ c : ClosedColor π, f c.val := by
      symm
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (fun c => by simp) f).symm
    _ = _ := (cycleColorEquiv π).sum_comp (fun c => f c.val) |>.symm

lemma trace_cycle_weight (π : Equiv.Perm V) :
    Matrix.trace (matrix π) = (2:ℝ) ^ Fintype.card (Cycles π) := by
  have he := trace_cycle_colors π (fun _ => 1)
  simpa using he

def magnetization (c : Color (V:=V)) : ℝ := ∑ i, if c i then (1:ℝ)/2 else -1/2

lemma magnetization_bound (c : Color (V:=V)) :
    |magnetization c| ≤ (Fintype.card V : ℝ)/2 := by
  calc
    _ ≤ ∑ i, |if c i then (1:ℝ)/2 else -1/2| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      have he (i : V) : |if c i then (1:ℝ)/2 else -1/2| = (1:ℝ)/2 := by
        cases c i <;> norm_num
      simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

theorem spectral_cycle_law (π : Equiv.Perm V) (Φ : ℝ → ℝ) :
    Matrix.trace (matrix π * Matrix.diagonal (fun c => Φ (magnetization c))) =
      ∑ ε : Cycles π → Bool, Φ (∑ i, if ε (cycleOf π i) then (1:ℝ)/2 else -1/2) :=
  trace_cycle_colors π _

end Heisenberg.SlotColor
end
end

end OAI
