import OAI.Geometry.NodalSets.Waves.LatticeCovariance2
import OAI.Geometry.NodalSets.Waves.SeededGaussianJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeSeededRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : Coord → ℝ) (x : Coord) (b : ℝ) (v : Coord)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : ℝ :=
  letI := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  Real.exp (-(n:ℝ)*S x)*(b*(seed x+gaussianWaveField V coeff x)+
    (n:ℝ)⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V coeff z) x v)

lemma variance_latticeSeededRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : Coord → ℝ) (x : Coord) (hseed : DifferentiableAt ℝ seed x)
    (hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x)
    (b : ℝ) (v : Coord) :
    letI := hfin
    Var[a.latticeSeededRandomDual hUD n hfin seed x b v; gaussianPairs] =
      a.latticeEnergy hUD n hfin x b v := by
  let := hfin
  exact seeded_gaussian_dual_variance
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
    seed x v (fun i ↦ hV i.1 i.2) hseed (n:ℝ) (S x) b

theorem actual_lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ (seed : Coord → ℝ) (x : Coord), x ∈ Q → DifferentiableAt ℝ seed x → ∀ (b : ℝ) (v : Coord),
      c/(n:ℝ)*(b^2+∑ i : Fin 4, (v i)^2) ≤
        Var[a.latticeSeededRandomDual hUD n hfin seed x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.euclidean_lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hb,lattice_wave_estimates a.cover a.beams hUD] with n hn hs
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro seed x hx hseed b v
  have hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x :=
    fun z j ↦ ((hs z j).1.differentiable (by simp)).differentiableAt
  rw [a.variance_latticeSeededRandomDual hUD n hfin seed x hseed hV]
  have hb := hbound x hx b v
  rw [a.variance_latticeRandomDual] at hb
  exact hb

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
