import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorFirstReplacement

namespace OAI

/-! The residual in any electron coordinate has the same polynomial bound.
The regrouping is an exact measure-preserving separation of that coordinate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def tensorSlotReplacement {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin n → ι) → ℂ) (i : Fin n) (x : Fin n → A) : ℂ :=
  ∑ b, c b * ∏ j, if j=i then r (b j) (x j) else v (b j) (x j)

theorem tensorSlotReplacement_regroup {A ι : Type*} [Fintype ι] {n : ℕ}
    (v r : ι → A → ℂ) (c : (Fin (n+1) → ι) → ℂ)
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    tensorSlotReplacement v r c i x =
      tensorFirstReplacement v r (fun a b => c (i.insertNth a b)) (i.removeNth x,x i) := by
  unfold tensorSlotReplacement
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => ι) i).sum_comp
    (fun b => c b * ∏ j, if j=i then r (b j) (x j) else v (b j) (x j))]
  rw [Fintype.sum_prod_type]
  unfold tensorFirstReplacement tensorCoefficientSlice
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNthEquiv_apply,Fin.insertNth_apply_same,ite_true,
    Fin.succAbove_ne,ite_false,Fin.insertNth_apply_succAbove]
  change c (i.insertNth a b) * (r a (x i) * ∏ j, v (b j) (x (i.succAbove j))) =
    (c (i.insertNth a b) * ∏ j, v (b j) (x (i.succAbove j))) * r a (x i)
  ring

theorem sum_insertNth_coefficient_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    (∑ a, ∑ b : Fin n → ι, ‖c (i.insertNth a b)‖^2) = ∑ b, ‖c b‖^2 := by
  calc
    _ = ∑ p : ι × (Fin n → ι), ‖c (i.insertNth p.1 p.2)‖^2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := (Fin.insertNthEquiv (fun _ : Fin (n+1) => ι) i).sum_comp
      (fun b => ‖c b‖^2)

def separateTensorSlot {A : Type*} [MeasurableSpace A] {n : ℕ}
    (i : Fin (n+1)) : (Fin (n+1) → A) ≃ᵐ (Fin n → A) × A :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => A) i).trans MeasurableEquiv.prodComm

theorem separateTensorSlot_apply {A : Type*} [MeasurableSpace A] {n : ℕ}
    (i : Fin (n+1)) (x : Fin (n+1) → A) :
    separateTensorSlot i x = (i.removeNth x,x i) := rfl

theorem separateTensorSlot_measurePreserving {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (separateTensorSlot i)
      (Measure.pi fun _ : Fin (n+1) => μ) ((Measure.pi fun _ : Fin n => μ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) i)

theorem tensorSlotReplacement_memLp {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    MemLp (tensorSlotReplacement v r c i) 2 (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (tensorFirstReplacement_memLp v r hv hr (fun a b => c (i.insertNth a b))).comp_measurePreserving
    (separateTensorSlot_measurePreserving (μ := μ) i)
  simpa only [Function.comp_def,separateTensorSlot_apply,← tensorSlotReplacement_regroup] using h

theorem tensorSlotReplacement_L2_bound {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (v r : ι → A → ℂ) (hv : ∀ a, MemLp (v a) 2 μ) (hr : ∀ a, MemLp (r a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a=b then (1:ℂ) else 0)
    (c : (Fin (n+1) → ι) → ℂ) (i : Fin (n+1)) :
    (∫ x, ‖tensorSlotReplacement v r c i x‖^2 ∂(Measure.pi fun _ : Fin (n+1) => μ)) ≤
      (∑ a, ∫ x, ‖r a x‖^2 ∂μ)*(∑ b, ‖c b‖^2) := by
  have he := (separateTensorSlot_measurePreserving (μ := μ) i).integral_comp'
    (fun z => ‖tensorFirstReplacement v r (fun a b => c (i.insertNth a b)) z‖^2)
  simp only [separateTensorSlot_apply,← tensorSlotReplacement_regroup] at he
  rw [he]
  have h := tensorFirstReplacement_L2_bound v r hv hr ho (fun a b => c (i.insertNth a b))
  rwa [sum_insertNth_coefficient_norm] at h

end ContinuumCoulomb

end

end OAI
