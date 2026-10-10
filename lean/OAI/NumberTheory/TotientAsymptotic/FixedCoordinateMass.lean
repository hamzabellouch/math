import OAI.NumberTheory.TotientAsymptotic.FixedCoordinateGrid
import OAI.NumberTheory.TotientAsymptotic.UnbandedSimplexMass

namespace OAI

/-! Prime reciprocal mass inherits the fixed-coordinate concentration bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_prime_mass (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ Q : Finset (Fin (N+2) → ℕ),
    (∀ p∈Q,(∀ j,(p j).Prime) ∧
      primePrefixCoord p∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (∀ j,j.val+1=N+2 → (1/100:ℝ) ≤ primePrefixCoord p j) ∧
      (primePrefixCoord p i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primePrefixCoord p i)) →
    (∑ p∈Q,reciprocalShiftWeight p) ≤ 
      C*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,c,hA,hc,hgrid⟩ := fixed_coordinate_grid_bound H
  obtain ⟨d,hd,hlower⟩ := reverse_enlarged_linear_lower
  obtain ⟨D,_hD,hmass⟩ := unbanded_prime_mass_bound fordUnitPrimeBoxInput
  refine ⟨Real.exp (D*(1-Real.exp (-d))⁻¹)*A,c,by positivity,hc,?_⟩
  filter_upwards [hgrid] with P hP
  filter_upwards [hP] with x hx
  intro N hN i hi Q hQ
  have hcoords (p) (hp : p∈Q) : ∀ j,d*(N+2-j.val:ℕ) ≤ primePrefixCoord p j := by
    apply hlower (m x) (N+2) (by omega) (B x) (primePrefixCoord p)
    · simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using (hQ p hp).2.1
    · exact (hQ p hp).2.2.1
  have hcard : ((tupleUnitGrid Q).card:ℝ) ≤ 
      A*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N hN i hi
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨primePrefixCoord p,tupleUnitGrid_cell (fun j => ?_),
      (hQ p hp).2.1,(hQ p hp).2.2.2⟩
    exact (mul_nonneg hd.le (Nat.cast_nonneg _)).trans (hcoords p hp j)
  have hh := hmass Q d _ hd
    (fun p hp j => ⟨(hQ p hp).1 j,hcoords p hp j⟩) hcard
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
