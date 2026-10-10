import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockChargePolynomial

namespace OAI

/-! The spatial one-body matrix acts on both conserved spin modes and
agrees with the actual graph hopping operator. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

def spinLift (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ)
    (a b : Fin ((2*m+1)+1)) : ℂ :=
  if ((siteModes m).symm a).2 = ((siteModes m).symm b).2 then
    K (modeSite m a) (modeSite m b) else 0

def siteBilinear (m : ℕ) (i j : Fin (m+1)) : Module.End ℂ (Space (2*m+1)) :=
  transfer (siteMode m i 0) (siteMode m j 0) +
    transfer (siteMode m i 1) (siteMode m j 1)

def siteOneBody (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ) :
    Module.End ℂ (Space (2*m+1)) := ∑ i, ∑ j, K i j • siteBilinear m i j

theorem oneBodyOperator_spinLift (m : ℕ) (K : Fin (m+1) → Fin (m+1) → ℂ) :
    oneBodyOperator (spinLift m K) = siteOneBody m K := by
  unfold oneBodyOperator siteOneBody
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ σ : Fin 2, ∑ j : Fin (m+1),
        K i j • transfer (siteMode m i σ) (siteMode m j σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← (siteModes m).sum_comp]
      simp only [Fintype.sum_prod_type, spinLift, modeSite, Equiv.symm_apply_apply,
        ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, siteMode]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.sum_univ_two, siteBilinear, smul_add]

theorem siteOneBody_add (m : ℕ) (K L : Fin (m+1) → Fin (m+1) → ℂ) :
    siteOneBody m (fun i j => K i j + L i j) = siteOneBody m K + siteOneBody m L := by
  simp only [siteOneBody, add_smul, Finset.sum_add_distrib]

theorem siteOneBody_sum {I : Type*} [Fintype I] (m : ℕ)
    (K : I → Fin (m+1) → Fin (m+1) → ℂ) :
    siteOneBody m (fun i j => ∑ e, K e i j) = ∑ e, siteOneBody m (K e) := by
  unfold siteOneBody
  simp only [Finset.sum_smul]
  calc
    _ = ∑ i, ∑ e, ∑ j, K e i j • siteBilinear m i j :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem siteOneBody_single (m : ℕ) (i j : Fin (m+1)) (z : ℂ) :
    siteOneBody m (fun k l => if k=i ∧ l=j then z else 0) =
      z • siteBilinear m i j := by
  have h (k l : Fin (m+1)) : (if k=i ∧ l=j then z else 0) =
      if k=i then (if l=j then z else 0) else 0 := by
    by_cases hki : k=i <;> by_cases hlj : l=j <;> simp [hki,hlj]
  simp only [siteOneBody,h,ite_smul,zero_smul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

def graphHoppingMatrix {Edge : Type*} [Fintype Edge] (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) (i j : Fin (m+1)) : ℂ :=
  ∑ e, ((if i=left e ∧ j=right e then t e else 0) +
    (if i=right e ∧ j=left e then t e else 0))

theorem oneBodyOperator_graphHopping {Edge : Type*} [Fintype Edge] (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) :
    oneBodyOperator (spinLift m (graphHoppingMatrix m left right t)) =
      graphHopping m left right t := by
  rw [oneBodyOperator_spinLift]
  unfold graphHoppingMatrix
  rw [siteOneBody_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [siteOneBody_add,siteOneBody_single,siteOneBody_single]
  simp only [siteBilinear,siteHopping,twoSiteHopping,bondTransfer,smul_add]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
