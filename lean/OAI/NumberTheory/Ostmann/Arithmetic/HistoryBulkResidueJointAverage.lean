import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueCRT

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueCRT
open ResidueHaar
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

omit [Fintype ι] [DecidableEq ι] in

theorem average_swap (F : α→β→ℂ) :
    average (fun a=>average (F a))=average (fun b=>average (fun a=>F a b)) := by
  simp only [average,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem giant_array_product_average {D R : ℕ} [NeZero D] [NeZero R] (hc : D.Coprime R)
    (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ) :
    average (fun x : ι→(ZMod (D*R))ˣ=>
      average (fun a=>F a ((arrayEquiv hc x).1))*
      average (fun b=>G b ((arrayEquiv hc x).2)))=
      average (fun a=>average (F a))*average (fun b=>average (G b)) := by
  rw [array_product_average hc (fun z => average (fun a => F a z))
    (fun z => average (fun b => G b z))]
  rw [average_swap (fun z a => F a z), average_swap (fun z b => G b z)]

theorem norm_giant_array_product_average_le {D R : ℕ} [NeZero D] [NeZero R]
    (hc : D.Coprime R) (F : α→(ι→(ZMod D)ˣ)→ℂ) (G : β→(ι→(ZMod R)ˣ)→ℂ)
    {A B : ℝ} (hF : ‖average (fun a=>average (F a))‖≤A)
    (hG : ‖average (fun b=>average (G b))‖≤B) :
    ‖average (fun x : ι→(ZMod (D*R))ˣ=>
      average (fun a=>F a ((arrayEquiv hc x).1))*
      average (fun b=>G b ((arrayEquiv hc x).2)))‖≤A*B := by
  rw [giant_array_product_average,norm_mul]
  exact mul_le_mul hF hG (norm_nonneg _) ((norm_nonneg _).trans hF)

end Ostmann.Arithmetic.HistoryBulkResidueCRT

end

end OAI
