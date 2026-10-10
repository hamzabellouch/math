import Mathlib
import OAI.Combinatorics.UniformKServer.LevelAllowances
import OAI.Combinatorics.UniformKServer.ScaleAllowances
import OAI.Combinatorics.UniformKServer.ActualAuxiliary
import OAI.Combinatorics.UniformKServer.ActualPilot

namespace OAI

noncomputable section

/-! Full expected key-edit charge, including the actual posterior unit mover. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def editRate (A : Config X) : ℝ := 198/A.P.gammaH+1/Real.log (1+A.P.deltaH)+(8*A.C+24)

def keyEditCost (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) : ℝ :=
  if ht : t<N then ∑ j∈range J, ∑ p,
    HiddenFlow.filtered D t ω p * ((A.input (N:=N) (J:=J) D hk ω).level j).data.editCost
      ⟨t,ht⟩ ((A.input (N:=N) (J:=J) D hk ω).level j).order p else 0

theorem charges_identity (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (ω : Ω) (n : Fin N) :
    (∑ j∈range J,((A.input (N:=N) (J:=J) D hk ω).level j).charges n)=
      A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω := by
  unfold totalPilotCharge
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_option]
  unfold pilotCharge PartitionLevel.Input.charges PartitionLevel.Input.order
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq]
  rfl

theorem level_mass_step (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (j : ℕ) :
    let I := ((A.input (N:=N) (J:=J) D hk ω).level j)
    (∑ p,HiddenFlow.filtered D n.val ω p*I.data.editCost n I.order p)+
      linearPotential (HiddenFlow.current D (n.val+1) ω) (I.data.auxiliary I.order (n.val+1))-
      linearPotential (HiddenFlow.filtered D n.val ω) (I.data.auxiliary I.order n.val)≤
    98*I.charges n+∑ p,HiddenFlow.mover D n.val ω p*I.data.moverAllowance I.order A.P.gammaH n p := by
  let F := HiddenFlow.flow D
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j)
  let s : X→ℝ := fun p=>F.filtered n.val ω p-F.mover n.val ω p
  have hs (p : X) : 0≤ s p := sub_nonneg.mpr (F.mover_le n.val ω p)
  have hs' (p : X) : s p≤I.μ n p := by
    have he := F.update n.val ω p
    change I.μ n p= s p + (if p=I.center n then 1 else 0) at he
    rw [he]
    split_ifs <;> linarith
  have h := I.data.mass_ledger n I.order A.P.gammaH (by linarith [A.P.gammaH_small])
    s (F.mover n.val ω) hs (F.mover_nonneg n.val ω) (F.mover_total n.val ω)
  have hstat := I.stationary_allowance n s hs hs'
  have hdecomp : (fun p=>s p+F.mover n.val ω p)=F.filtered n.val ω := by funext p; dsimp [s]; ring
  have hpost (b : X→ℝ) : (∑ p,s p*b p)+b (I.data.center n)=linearPotential (F.post (n.val+1) ω) b := by
    unfold linearPotential
    simp only [F.update,add_mul,sum_add_distrib,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true]
    rfl
  simp only [congrFun hdecomp] at h
  rw [hpost] at h
  dsimp only [linearPotential] at h ⊢
  change _≤98*I.charges n+_
  change _≤98*I.charges n at hstat
  have hstat' : (∑ p,s p*I.data.stationaryAllowance I.order A.P.gammaH n p)≤98*I.charges n := hstat
  exact h.trans (add_le_add hstat' le_rfl)

theorem key_mass_step (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) :
    A.keyEditCost (N:=N) (J:=J) D hk n.val ω+
      linearPotential (HiddenFlow.current D (n.val+1) ω) (A.auxiliary (N:=N) (J:=J) D hk (n.val+1) ω)-
      linearPotential (HiddenFlow.filtered D n.val ω) (A.auxiliary (N:=N) (J:=J) D hk n.val ω)≤
    147*A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω+
      A.editRate*(1+Real.log k)*moverCost (HiddenFlow.flow D) n.val ω := by
  let I := A.input (N:=N) (J:=J) D hk ω
  let F := HiddenFlow.flow D
  have hm := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (I.mover_allowance_sum n p) (F.mover_nonneg n.val ω p))
  have hme : (∑ p,F.mover n.val ω p*(49*(∑ j∈range J,(I.level j).charges n)+
       I.editCoefficient*(1+Real.log I.k)*dist (I.center n) p))=
      49*(∑ j∈range J,(I.level j).charges n)+A.editRate*(1+Real.log k)*moverCost F n.val ω := by
    simp only [mul_add,sum_add_distrib,←sum_mul,F.mover_total,one_mul]
    congr 1
    unfold moverCost
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    change F.mover n.val ω p*((A.editRate*1+A.editRate*Real.log k)*dist (I.center n) p)=
      (A.editRate*1+A.editRate*Real.log k)*(F.mover n.val ω p*dist (I.center n) p)
    ring
  rw [hme] at hm
  have h := sum_le_sum (s:=range J) (fun j _=>A.level_mass_step (J:=J) D hk ω n j)
  change (∑ j∈range J,((∑ p,F.filtered n.val ω p*(I.level j).data.editCost n (I.level j).order p)+
    linearPotential (F.post (n.val+1) ω) ((I.level j).data.auxiliary (I.level j).order (n.val+1))-
    linearPotential (F.filtered n.val ω) ((I.level j).data.auxiliary (I.level j).order n.val)))≤
    ∑ j∈range J,(98*(I.level j).charges n+∑ p,F.mover n.val ω p*
      (I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p) at h
  rw [sum_sub_distrib,sum_add_distrib,sum_add_distrib,←mul_sum] at h
  have hlin (μ : X→ℝ) (t : ℕ) :
      (∑ j∈range J,linearPotential μ ((I.level j).data.auxiliary (I.level j).order t))=
      linearPotential μ (A.auxiliary (N:=N) (J:=J) D hk t ω) := by
    unfold linearPotential auxiliary
    rw [sum_comm]
    simp only [mul_sum]
    rfl
  rw [hlin,hlin] at h
  have hm2 : (∑ j∈range J,∑ p,F.mover n.val ω p*(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p)=
      ∑ p,F.mover n.val ω p*∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p := by
    rw [sum_comm]
    simp only [mul_sum]
  rw [hm2] at h
  change (∑ p,F.mover n.val ω p*∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p)≤_ at hm
  have hc : (∑ j∈range J,(I.level j).charges n)=A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω := A.charges_identity D hk ω n
  rw [hc] at h hm
  rw [keyEditCost,dite_eq_left n.isLt]
  change (∑ j∈range J,∑ p,F.filtered n.val ω p*(I.level j).data.editCost n (I.level j).order p)+
    linearPotential (F.post (n.val+1) ω) (A.auxiliary (N:=N) (J:=J) D hk (n.val+1) ω)-
    linearPotential (F.filtered n.val ω) (A.auxiliary (N:=N) (J:=J) D hk n.val ω)≤_
  linarith only [h,hm]

end UniformKServer.ActualPartitions.Config

end

end OAI
