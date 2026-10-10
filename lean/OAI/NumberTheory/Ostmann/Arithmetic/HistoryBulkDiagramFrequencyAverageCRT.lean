import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverageBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage
open ResidueHaar HistoryBulkResidueCRT
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

def coupledAverage (D R : ℕ) [NeZero D] [NeZero R]
    (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ) : ℂ :=
  average (fun x : ι→(ZMod (D*R))ˣ=>
    average (fun a=>F a (fun i=>ZMod.unitsMap (Nat.dvd_mul_right D R) (x i)))*
    average (fun b=>G b (fun i=>ZMod.unitsMap (Nat.dvd_mul_left R D) (x i))))

theorem coupledAverage_eq {D R : ℕ} [NeZero D] [NeZero R] (hc : D.Coprime R)
    (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ) :
    coupledAverage D R F G=average (fun a=>average (F a))*average (fun b=>average (G b)) := by
  unfold coupledAverage
  have he : (fun x : ι→(ZMod (D*R))ˣ=>
      average (fun a=>F a (fun i=>ZMod.unitsMap (Nat.dvd_mul_right D R) (x i)))*
      average (fun b=>G b (fun i=>ZMod.unitsMap (Nat.dvd_mul_left R D) (x i))))=
      (fun x : ι→(ZMod (D*R))ˣ=>average (fun a=>F a ((arrayEquiv hc x).1))*
        average (fun b=>G b ((arrayEquiv hc x).2))) := by
    funext x
    rw [(arrayEquiv_projections hc x).1,(arrayEquiv_projections hc x).2]
  rw [he]
  exact giant_array_product_average hc F G

theorem coupledAverage_eq_nested {D R : ℕ} [NeZero D] [NeZero R]
    (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ) :
    coupledAverage D R F G=
      average (fun x : ι→(ZMod (D*R))ˣ=>average (fun a=>average (fun b=>
        F a (fun i=>ZMod.unitsMap (Nat.dvd_mul_right D R) (x i))*
          G b (fun i=>ZMod.unitsMap (Nat.dvd_mul_left R D) (x i))))) := by
  unfold coupledAverage
  congr 1
  funext x
  simp only [average,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem norm_coupledAverage_le {D R : ℕ} [NeZero D] [NeZero R] (hc : D.Coprime R)
    (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ)
    {A B : ℝ} (hF : ‖average (fun a=>average (F a))‖≤A)
    (hG : ‖average (fun b=>average (G b))‖≤B) : ‖coupledAverage D R F G‖≤A*B := by
  rw [coupledAverage_eq hc,norm_mul]
  exact mul_le_mul hF hG (norm_nonneg _) ((norm_nonneg _).trans hF)

end Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage

end

end OAI
