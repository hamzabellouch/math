import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
variable (p : M) (hδ : δ p=0) (hκ : κ p=1)
local instance laurentRegradePureRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradePureAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradePureAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

include hδ hκ in
lemma pure_laurentBounded (f : PowerSeries R) :
    LaurentBounded v Ω δ κ B (raySeries v Ω p f) := by
  intro n m hm
  rw [coeff_raySeries] at hm
  have he : m=n • p := by
    by_contra H
    exact hm (Finsupp.single_eq_of_ne H)
  subst m
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  exact ⟨le_rfl,Int.natCast_nonneg _,le_rfl⟩

include hδ hκ in
lemma laurentRegrade_pure (f : PowerSeries R) :
    laurentRegrade v Ω δ κ B (raySeries v Ω p f)
      (pure_laurentBounded v Ω δ κ B p hδ hκ f)=
    PowerSeries.C (HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f)) := by
  classical
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [laurentRegrade_coeff]
  simp_rw [coeff_raySeries,laurentHomogenize_monomial]
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,mul_zero,Int.toNat_zero,coeff_monomial]
  by_cases hd : d=0
  · subst d
    simp only [coeff_C,Nat.cast_zero,mul_zero,add_zero,ite_true]
    by_cases hz : 0≤z
    · lift z to ℕ using hz with j hj
      simp [HahnSeries.coeff_single]
    · have hz' : z<0 := lt_of_not_ge hz
      have H (j : ℕ) : z≠(j:ℤ) := by omega
      simp_rw [HahnSeries.coeff_single,ite_eq_right (H _)]
      rw [Finset.sum_const_zero,HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
      rintro ⟨n,hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega
  · simp only [ite_eq_right hd,HahnSeries.coeff_zero,Finset.sum_const_zero,coeff_C]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
