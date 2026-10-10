import OAI.NumberTheory.TotientAsymptotic.GeometricCube
import OAI.NumberTheory.TotientAsymptotic.GeometricPrimeMass

namespace OAI

/-! The outer grid has both positive prime mass and strict arithmetic coordinates. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ambient_successor_fifth_budget :
    ∀ᶠ x : ℝ in atTop,100*(m x+1:ℝ)^5 ≤ B x := by
  filter_upwards [ambient_polynomial_budget 3200 5,
    m_tendsto.eventually (eventually_ge_atTop 1)] with x hx hm
  have hm' : (1:ℝ) ≤ m x := by exact_mod_cast hm
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ m x+1)
    (show (m x:ℝ)+1 ≤ 2*m x by linarith only [hm']) 5
  have he : (2*(m x:ℝ))^5=32*(m x:ℝ)^5 := by ring
  rw [he] at hpow
  linarith only [hpow,hx]

lemma geometric_grid_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ b ∈ geometricPrimeGrid x c n,
        ∀ v : Fin n → ℝ,v ∈ unitGridCell b →
          v ∈ relaxedGeometricFamily (m x) n (B x) (c/2) := by
  filter_upwards [geometric_dominates_polynomial hc 100 5] with H hH
  filter_upwards [ambient_successor_fifth_budget] with x hx
  intro n hn b hb v hv
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  apply geometric_family_unit_cube (by omega) hfamily
    (unitGridCell_coordinate_distance hu hv) _ hx
  intro i
  exact (hH _ (by have := i.isLt; omega)).trans (hfamily.2.1 i)

theorem geometric_prime_mass_and_coordinates : ∃ c : ℝ,0 < c ∧
    ∀ᶠ H : ℕ in atTop,∃ δ : ℝ,0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (m x) ≤ gridPrimeMass (geometricPrimeGrid x c (N+2)) ∧
        ∀ b ∈ geometricPrimeGrid x c (N+2),∀ v : Fin (N+2) → ℝ,
          v ∈ unitGridCell b → v ∈ relaxedGeometricFamily (m x) (N+2) (B x) (c/2) := by
  obtain ⟨c,hc,hmass⟩ := geometric_prime_mass_lower
  refine ⟨c,hc,?_⟩
  filter_upwards [hmass,geometric_grid_coordinates hc] with H hm hcoord
  obtain ⟨δ,hδ,hδmass⟩ := hm
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hδmass,hcoord] with x hx hxc
  intro N hN
  exact ⟨hx N hN,hxc (N+2) hN⟩

end TotientAsymptotic

end

end OAI
