import OAI.NumberTheory.TotientAsymptotic.FixedTerminalGrid
import OAI.NumberTheory.TotientAsymptotic.UnbandedSimplexMass

namespace OAI

/-! The terminal cap persists for actual reciprocal shifted-prime mass. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_prime_mass (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+1+H=m x → ∀ t : ℝ,0 ≤ t →
    ∀ Q : Finset (Fin (N+1) → ℕ),
    (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
      primePrefixCoord p ∈ enlargedSimplex (N+1) (B x)
        (1+simplexBoxError 0 (m x))
        (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) ∧
      (1/100:ℝ) ≤ primePrefixCoord p (Fin.last N) ∧
      t ≤ primePrefixCoord p (Fin.last N)) →
    (∑ p ∈ Q,reciprocalShiftWeight p) ≤ C*G x (N+1)*Real.exp (-c*t) := by
  obtain ⟨A,c,hA,hc,hgrid⟩ := fixed_terminal_grid_bound H
  obtain ⟨d,hd,hlower⟩ := reverse_enlarged_linear_lower
  obtain ⟨D,hD,hmass⟩ := unbanded_prime_mass_bound fordUnitPrimeBoxInput
  refine ⟨Real.exp (D*(1-Real.exp (-d))⁻¹)*A,c,by positivity,hc,?_⟩
  filter_upwards [hgrid] with x hx
  intro N hN t ht Q hQ
  have hcoords (p) (hp : p ∈ Q) : ∀ i,d*(N+1-i.val:ℕ) ≤ primePrefixCoord p i := by
    apply hlower (m x) (N+1) (by omega) (B x) (primePrefixCoord p) (hQ p hp).2.1
    intro i hi
    have he : i=Fin.last N := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [he] using (hQ p hp).2.2.1
  have hcard : ((tupleUnitGrid Q).card:ℝ) ≤ A*G x (N+1)*Real.exp (-c*t) := by
    apply hx N hN t ht
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨primePrefixCoord p,tupleUnitGrid_cell (fun i => ?_),(hQ p hp).2.1,(hQ p hp).2.2.2⟩
    exact (mul_nonneg hd.le (Nat.cast_nonneg _)).trans (hcoords p hp i)
  have hh := hmass Q d (A*G x (N+1)*Real.exp (-c*t)) hd
    (fun p hp i => ⟨(hQ p hp).1 i,hcoords p hp i⟩) hcard
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
