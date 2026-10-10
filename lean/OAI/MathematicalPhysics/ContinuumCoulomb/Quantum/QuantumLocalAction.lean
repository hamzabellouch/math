import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalCoordinates

namespace OAI

/-! Actions of local flips and spectator-identity tensor factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaBitFlip (i : ι) (s : ι → Fin 2) : ι → Fin 2 :=
  Function.update s i (Equiv.swap (0:Fin 2) 1 (s i))

omit [Fintype ι] in
theorem qmaBitFlip_involutive (i : ι) : Function.Involutive (qmaBitFlip i) := by
  intro s
  funext j
  by_cases h : j = i
  · subst j
    simp [qmaBitFlip]
  · simp [qmaBitFlip,h]

def qmaBitFlipMatrix (i : ι) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  fun s t => if s = qmaBitFlip i t then 1 else 0

theorem qmaBitFlipMatrix_local (i : ι) : QMALocalOn {i} (qmaBitFlipMatrix i) := by
  apply qmaLocalOn_permutation {i} (qmaBitFlip i)
    (fun s j => Equiv.swap (0:Fin 2) 1 (s j))
  · intro s
    funext j
    have hj : j.val = i := Finset.mem_singleton.mp j.property
    simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaBitFlip,hj]
  · intro s
    funext j
    have hj : j.val ≠ i := by simpa using j.property
    simp [qmaSupportSplit,Equiv.piEquivPiSubtypeProd,qmaBitFlip,hj]

theorem qmaBitFlipMatrix_mulVec (i : ι) (u : (ι → Fin 2) → ℂ) (s : ι → Fin 2) :
    (qmaBitFlipMatrix i).mulVec u s = u (qmaBitFlip i s) := by
  change (∑ t, (if s = qmaBitFlip i t then (1:ℂ) else 0)*u t) = _
  have he (t : ι → Fin 2) : s = qmaBitFlip i t ↔ t = qmaBitFlip i s := by
    constructor
    · intro h
      rw [h,qmaBitFlip_involutive]
    · intro h
      rw [h,qmaBitFlip_involutive]
  simp only [he,ite_mul,one_mul,zero_mul]
  simp

theorem qmaJoinMatrix_one_left_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) (u : (ι ⊕ κ → Fin 2) → ℂ)
    (s : ι ⊕ κ → Fin 2) :
    (qmaJoinMatrix (ι := ι) 1 A).mulVec u s =
      A.mulVec (fun b => u (Sum.elim (s ∘ Sum.inl) b)) (s ∘ Sum.inr) := by
  let e := Equiv.sumArrowEquivProdArrow ι κ (Fin 2)
  change (∑ t, qmaJoinMatrix 1 A s t*u t) = _
  rw [←e.symm.sum_comp (fun t => qmaJoinMatrix 1 A s t*u t),Fintype.sum_prod_type]
  change (∑ a, ∑ b, (if (s ∘ Sum.inl) = a then (1:ℂ) else 0)*
    A (s ∘ Sum.inr) b*u (Sum.elim a b)) = _
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [eq_comm,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

end ContinuumCoulomb

end

end OAI
