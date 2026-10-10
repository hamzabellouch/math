import Mathlib
import OAI.Algebra.FiniteTensor.JetSolutions
import OAI.Algebra.FiniteTensor.NilpotentSubstitution
import OAI.Algebra.FiniteTensor.OffsetEquations

namespace OAI

/-! Algebraic tensor approximation and the characteristic-zero finite tensor obstruction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}

 

theorem tensor_algebraic_approximation
    (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M)
    (hF : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) :
    ∃ s : JetSolution M W,s.Algebraic := by
  classical
  obtain ⟨L,hL0,hLeq,hLalg,hLjet⟩ := algebraic_germ_artin (universalLeftEquation M W)
    (universalLeftEquation_algebraic M W hF hb)
    (fun i=>centerSeries (leftOriginal M W i)) (fun _=>centerSeries_zero _)
    (original_solves_left M W) 2
  obtain ⟨R,hR0,hReq,hRalg,hRjet⟩ := algebraic_germ_artin (universalRightEquation M W)
    (universalRightEquation_algebraic M W hF hb)
    (fun i=>centerSeries (rightOriginal M W i)) (fun _=>centerSeries_zero _)
    (original_solves_right M W) 2
  let s : JetSolution M W := {
    left := L
    right := R
    left_zero := hL0
    right_zero := hR0
    left_jet := by
      intro i j
      have h := (mem_jetIdeal_pow_iff_coeff _ 2).mp (hLjet i) (Finsupp.single j 1) (by simp)
      simpa only [map_sub,sub_eq_zero] using h
    right_jet := by
      intro i j
      have h := (mem_jetIdeal_pow_iff_coeff _ 2).mp (hRjet i) (Finsupp.single j 1) (by simp)
      simpa only [map_sub,sub_eq_zero] using h
    left_solve := hLeq
    right_solve := hReq }
  exact ⟨s,⟨hLalg,hRalg⟩⟩

 theorem tensor_algebraic_approximation_target : TensorAlgebraicApproximation := by
  intro K _ _ l m d c n e active M W hF hb
  exact tensor_algebraic_approximation M W hF hb

 

theorem no_formal_tensor_model (hm : 5 ≤ m)
    (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M)
    (hF : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) : False := by
  obtain ⟨s,hs⟩ := tensor_algebraic_approximation M W hF hb
  exact no_algebraic_jet_solution hm hF hb s hs

end
end PD4Tensor.Spreading

namespace PD4Tensor

open scoped BigOperators

variable (K : Type*) [Field K] (m : ℕ)

 
 
 
 
variable {K m}

variable (K m)

 

variable {K m}

 

 
end PD4Tensor

namespace PD4Tensor.Spreading
noncomputable section
variable {K : Type*} [Field K] {m : ℕ} {n : Fin (2*m) → ℕ}
  {active : Fin m ↪ Fin (2*m)} {d : ℕ}

 

def sourceIndex (h : PD4Tensor.Parametrizations K m n d) :
    PD4Tensor.Coordinates m n ≃ Fin d ⊕ Fin (PD4Tensor.N m n-d) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin]
    exact (Nat.add_sub_cancel' h.dimension_le).symm)

 

def sourceModel (g : PD4Tensor.Germs K m n active)
    (h : PD4Tensor.Parametrizations K m n d) (hc : PD4Tensor.TensorConditions g h) :
    TensorModel K (fun i=>Fin (n i)) m d (PD4Tensor.N m n-d) (sourceIndex h) active where
  F := g.F
  b := g.b
  F_zero := g.F_zero
  b_zero := g.b_zero
  H := h.HL
  G := h.HR
  H_zero := h.HL_zero
  G_zero := h.HR_zero
  tangent_unit := by
    apply isUnit_iff_ne_zero.mpr
    exact PD4Tensor.joinedMatrix_det_ne_zero (sourceIndex h) _ _
      hc.left_injective hc.right_injective hc.complementary
  left_vanishing := hc.left_vanishing
  right_vanishing := hc.right_vanishing
  left_triple := hc.left_triple
  right_triple := hc.right_triple

 

theorem source_primitives_exist (g : PD4Tensor.Germs K m n active)
    (h : PD4Tensor.Parametrizations K m n d) (hc : PD4Tensor.TensorConditions g h) :
    Nonempty (TensorPrimitives K (fun i=>Fin (n i)) m (sourceModel g h hc)) :=
  exists_tensorPrimitives K (fun i=>Fin (n i)) m (sourceModel g h hc)

end
end PD4Tensor.Spreading

 

theorem required_finite_tensor_obstruction : PD4Tensor.FiniteTensorObstruction := by
  intro K _ _ m hm n active g d h hc
  obtain ⟨W⟩ := PD4Tensor.Spreading.source_primitives_exist g h hc
  exact PD4Tensor.Spreading.no_formal_tensor_model hm
    (PD4Tensor.Spreading.sourceModel g h hc) W g.F_algebraic g.b_algebraic
end

end OAI
