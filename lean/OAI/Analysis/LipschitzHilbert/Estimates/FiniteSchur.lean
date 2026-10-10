import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! The finite Schur estimate used to sum the measure classes in the
restricted-to-strong argument. No factor depends on the index counts. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_schur_bound {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (K : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (M : ℝ)
    (hM : 0≤M) (hK : ∀ i∈I, ∀ j∈J, 0≤K i j)
    (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j)
    (hrow : ∀ i∈I, (∑ j∈J, K i j)≤M)
    (hcol : ∀ j∈J, (∑ i∈I, K i j)≤M) :
    (∑ i∈I, ∑ j∈J, K i j*a i*b j)≤
      M*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
  classical
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (I×ˢJ)
    (r:=fun p => K p.1 p.2*a p.1*b p.2)
    (f:=fun p => K p.1 p.2*(a p.1)^2)
    (g:=fun p => K p.1 p.2*(b p.2)^2)
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun p _ => by ring_nf; exact le_rfl)
  simp only [Finset.sum_product] at hs
  have hleft : (∑ i∈I, ∑ j∈J, K i j*(a i)^2)≤M*(∑ i∈I, (a i)^2) := by
    calc
      _ = ∑ i∈I, (∑ j∈J, K i j)*(a i)^2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ i∈I, M*(a i)^2 := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hright : (∑ i∈I, ∑ j∈J, K i j*(b j)^2)≤M*(∑ j∈J, (b j)^2) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j∈J, (∑ i∈I, K i j)*(b j)^2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ j∈J, M*(b j)^2 := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hleft0 : 0≤∑ i∈I, ∑ j∈J, K i j*(a i)^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hright0 : 0≤∑ i∈I, ∑ j∈J, K i j*(b j)^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hsq := hs.trans (mul_le_mul hleft hright hright0 (hleft0.trans hleft))
  have hS0 : 0≤∑ i∈I, ∑ j∈J, K i j*a i*b j :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (mul_nonneg (hK i hi j hj) (ha i hi)) (hb j hj)))
  have htarget : 0≤M*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by positivity
  apply (sq_le_sq₀ hS0 htarget).mp
  calc
    _ ≤ (M*(∑ i∈I, (a i)^2))*(M*(∑ j∈J, (b j)^2)) := hsq
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]; ring

end LipschitzHilbert

end

end OAI
