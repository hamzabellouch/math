import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientVariance
import OAI.Geometry.NodalSets.Waves.LatticeEnergyLowerBound

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : Coord) (b : ℝ) (v : Coord) : (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) → ℝ :=
  letI := hfin
  pairLinearSum (fun i : SourceGrid U n × Fin 3 ↦
    dualWaveCoefficient n (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v)

lemma variance_latticeRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : Coord) (b : ℝ) (v : Coord) :
    letI := hfin
    Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] = a.latticeEnergy hUD n hfin x b v := by
  let := hfin
  exact variance_pairLinearSum _

theorem lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      letI := hfin
      c/(n:ℝ)*(b^2+‖v‖^2) ≤ Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.lattice_energy_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hb] with n hn
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx b v
  rw [a.variance_latticeRandomDual]
  exact hbound x hx b v

theorem euclidean_lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      letI := hfin
      c/(n:ℝ)*(b^2+∑ i : Fin 4, (v i)^2) ≤ Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with n hn hn1
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx b v
  apply le_trans _ (hbound x hx b v)
  have hcoord (i : Fin 4) : (v i)^2 ≤ ‖v‖^2 := by
    have hh := norm_le_pi_norm v i
    change |v i| ≤ ‖v‖ at hh
    nlinarith [sq_abs (v i),norm_nonneg v,abs_nonneg (v i)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hcoord i)
  norm_num at hsum
  have hh : b^2+∑ i : Fin 4, (v i)^2 ≤ 4*(b^2+‖v‖^2) := by nlinarith [sq_nonneg b]
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ c/(4*(n:ℝ)))
  convert hh' using 1 <;> ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
