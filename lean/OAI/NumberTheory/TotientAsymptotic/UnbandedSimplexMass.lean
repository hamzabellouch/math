import OAI.NumberTheory.TotientAsymptotic.UnbandedPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.UnbandedGridVolume
import OAI.NumberTheory.TotientAsymptotic.UnbandedEnlargementLower
import OAI.NumberTheory.TotientAsymptotic.PrimeBoxInput

namespace OAI

/-! The prime-prefix mass bound used before the first failed simplex row. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem unbanded_simplex_prime_mass : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, H < m x →
    ∀ Q : Finset (Fin (m x-H) → ℕ),
      (∀ p ∈ Q, (∀ i, (p i).Prime) ∧
        primePrefixCoord p ∈ enlargedSimplex (m x-H) (B x)
          (1+simplexBoxError 0 (m x))
          (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) ∧
        (∀ i, i.val+1=m x-H → (1/100:ℝ) ≤ primePrefixCoord p i)) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤ C*G x (m x-H) := by
  obtain ⟨A,hA,hvolume⟩ := unbanded_grid_uniform_volume
  obtain ⟨c,hc,hlower⟩ := reverse_enlarged_linear_lower
  obtain ⟨D,hD,hmass⟩ := unbanded_prime_mass_bound fordUnitPrimeBoxInput
  refine ⟨Real.exp (D*(1-Real.exp (-c))⁻¹)*A,
    mul_pos (Real.exp_pos _) hA, ?_⟩
  filter_upwards [hvolume] with x hx
  intro H hH Q hQ
  have hcoords (p) (hp : p ∈ Q) :
      ∀ i, c*(m x-H-i.val:ℕ) ≤ primePrefixCoord p i :=
    hlower (m x) (m x-H) (Nat.sub_le _ _) (B x) (primePrefixCoord p)
      (hQ p hp).2.1 (hQ p hp).2.2
  have hcard : ((tupleUnitGrid Q).card:ℝ) ≤ A*G x (m x-H) := by
    apply hx H hH
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨primePrefixCoord p,tupleUnitGrid_cell (fun i => ?_),(hQ p hp).2.1⟩
    exact (mul_nonneg hc.le (Nat.cast_nonneg _)).trans (hcoords p hp i)
  have hh := hmass Q c (A*G x (m x-H)) hc
    (fun p hp i => ⟨(hQ p hp).1 i,hcoords p hp i⟩) hcard
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
