import Mathlib
import OAI.Analysis.HardSphere.PathBounds.CloseTailBaseTendsto
import OAI.Analysis.HardSphere.Conditioning.PairCloseLabels

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma density_forces_two_particles {n : ℕ} (L : Length) {D : ℝ}
    (hL : 100≤L.val) (hDeq : D=(n:ℝ)/L.val^3) (hD : 1≤D) : 2≤n := by
  have hLp : 0<L.val^3 := pow_pos L.property _
  have hn : L.val^3≤(n:ℝ) := by
    have hh : 1≤(n:ℝ)/L.val^3 := by rwa [←hDeq]
    simpa only [one_mul] using (le_div_iff₀ hLp).mp hh
  have hlarge : (100:ℝ)^3≤L.val^3 := by gcongr
  have hn2 : (2:ℝ)≤n := by linarith only [hn,hlarge]
  exact_mod_cast hn2

theorem spatial_full_and_bath_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g → ∀ A : Finset (CubeCell K),
      (groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((pairCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card))) ∧
      ∀ (m : ℕ) (e : Fin m ↪ Fin n),
      ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
        {Y | ∀ v∈A, θ*D≤((pairCloseLabels L (spatialCloseScale D b) (unitCenter L v) Y).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K L hL D α hL100 hDeq hD hα hαmax g hg A
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr
    (density_forces_two_particles L hL100 hDeq (hD₀.trans hD))
  have hfull := hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg A
  constructor
  · simpa only [localCloseLabels_eq_pairCloseLabels] using hfull
  · intro m e
    exact (closeBath_marginal_le L (spatialCloseScale D b) (θ*D) e
      (groundPositionLaw n L g) (unitCenter L) A).trans hfull

end HardSphere

end

end OAI
