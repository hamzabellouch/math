import OAI.NumberTheory.CubicMoment.Estimates.PrimeCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeExclusions

namespace OAI

/-! A divisor smaller than every supported prime is coprime to every
actual squarefree prime-product coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_coprime_small_element {R D : ℝ}
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e d : Eisenstein) (hd : d ≠ 0) (hsmall : norm d ≤ D)
    {a : Eisenstein} (ha : a ∈ fullSquarefreePrimeSupport R W X e) : IsCoprime a d := by
  have hprim := fullSquarefreePrimeSupport_primary R W X e ha
  by_contra hcop
  obtain ⟨p,hp,hpd⟩ := not_coprime_prime_cover hprim.1 hprim.2 hcop
  have hpp := (primaryPrimeFactor_spec hprim.1 hp).1
  obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X hpp
    (primaryPrimeFactor_spec hprim.1 hp).2 (Finset.mem_filter.mp ha).1
  have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
  have hratio : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
  have hn : X i ≤ norm p := by simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hratio
  have hpD : norm p ≤ D := (norm_le_of_dvd hd hpd).trans hsmall
  exact (not_lt_of_ge (hn.trans hpD)) (hrough i)

end CubicFirstMoment

end

end OAI
