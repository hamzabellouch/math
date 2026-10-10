import OAI.NumberTheory.Ostmann.Tree.MellinSquare

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mellin_const_mul (f : Fˣ → ℂ) (c : ℂ) (χ : MulChar F ℂ) :
    mellin (fun t => c*f t) χ=c*mellin f χ := by
  simp only [mellin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem mellin_sum {ι : Type*} (S : Finset ι) (f : ι → Fˣ → ℂ) (χ : MulChar F ℂ) :
    mellin (fun t => ∑ i ∈ S, f i t) χ=∑ i ∈ S, mellin (f i) χ := by
  simp only [mellin, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mellin_mulRight (f : Fˣ → ℂ) (u : Fˣ) (χ : MulChar F ℂ) :
    mellin (fun t => f (t*u)) χ=χ u*mellin f χ := by
  have hc : χ u*conj (χ u)=1 := by
    rw [Complex.mul_conj', mulChar_norm_unit]
    norm_num
  have he (t : Fˣ) : f (t*u)*conj (χ t)=χ u*(f (t*u)*conj (χ (t*u))) := by
    rw [map_mul,map_mul]
    calc
      _ = (f (t*u)*conj (χ t))*(χ u*conj (χ u)) := by rw [hc]; ring
      _ = _ := by ring
  unfold mellin
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hs := (Equiv.mulRight u).bijective.sum_comp (fun t : Fˣ => f t*conj (χ t))
  change (∑ t : Fˣ, f (t*u)*conj (χ (t*u)))=∑ t : Fˣ, f t*conj (χ t) at hs
  rw [hs]
  ring

end
end Ostmann.FiniteField

end OAI
