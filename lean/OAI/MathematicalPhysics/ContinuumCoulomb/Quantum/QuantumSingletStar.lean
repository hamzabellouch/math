import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorEffective

namespace OAI

/-! Weighted multi-terminal singlet stars for the lattice routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliKernel (n : ℕ) (i j : Fin n) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  ∑ μ : Fin 3, sourceLocalPauli n i μ*sourceLocalPauli n j μ

theorem qmaPauliKernel_self (n : ℕ) (i : Fin n) : qmaPauliKernel n i i = (3:ℂ) • 1 := by
  simp only [qmaPauliKernel,sourceLocalPauli_sq]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  module

theorem qmaPauliKernel_eq (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    qmaPauliKernel n i j = sourceHeisenbergMatrix n i j := sourceLocalPauli_sum n i j hij

theorem qmaHeisenberg_symm (n : ℕ) (i j : Fin n) :
    sourceHeisenbergMatrix n i j = sourceHeisenbergMatrix n j i := by
  unfold sourceHeisenbergMatrix sourceSpinSwap
  rw [Equiv.swap_comm i j]

variable {κ : Type*} [Fintype κ]

def qmaSingletStar (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ a, (amplitude a:ℂ) • mediatorAxisSpoke n r e (site a) (member a)

theorem qmaSingletStar_compression (n r : ℕ) (Delta : ℝ) (e : Fin r)
    (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude *
      liftedMediatorInverse n r Delta * qmaSingletStar n r e site member amplitude) =
    ∑ a, ∑ b, (((amplitude a:ℂ)*(amplitude b:ℂ))*
      ((4*Delta)⁻¹:ℝ)*(if member a = member b then (1:ℂ) else -1)) •
        qmaPauliKernel n (site a) (site b) := by
  simp only [qmaSingletStar,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    map_sum,map_smul,mediatorAxisSpoke_compression,ite_true,qmaPauliKernel,smul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  by_cases hm : member a = member b
  · simp only [hm,ite_true]
    ring_nf
  · simp only [hm,ite_false]
    ring_nf

/-- Separate singlet pairs have zero mixed second-order compression. -/
theorem qmaSingletStar_cross_zero (n r : ℕ) (Delta : ℝ) (e f : Fin r) (hef : e ≠ f)
    (site site' : κ → Fin n) (member member' : κ → Fin 2) (amplitude amplitude' : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude *
      liftedMediatorInverse n r Delta * qmaSingletStar n r f site' member' amplitude') = 0 := by
  simp only [qmaSingletStar,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    map_sum,map_smul,mediatorAxisSpoke_compression,hef,ite_false,smul_zero,Finset.sum_const_zero]

/-- All routing stars are applied simultaneously, one per distinct singlet pair. -/
def qmaRoutingStars (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, qmaSingletStar n r e (site e) (member e) (amplitude e)

theorem qmaRoutingStars_compression (n r : ℕ) (Delta : ℝ)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorCompression n r (qmaRoutingStars n r site member amplitude *
      liftedMediatorInverse n r Delta * qmaRoutingStars n r site member amplitude) =
    ∑ e, mediatorCompression n r (qmaSingletStar n r e (site e) (member e) (amplitude e) *
      liftedMediatorInverse n r Delta * qmaSingletStar n r e (site e) (member e) (amplitude e)) := by
  simp only [qmaRoutingStars,Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_eq_single e
  · intro f _ hfe
    exact qmaSingletStar_cross_zero n r Delta f e hfe _ _ _ _ _ _
  · simp

end ContinuumCoulomb

end

end OAI
