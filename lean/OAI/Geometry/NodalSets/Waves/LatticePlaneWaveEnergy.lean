import OAI.Geometry.NodalSets.Elliptic.FrequencyDerivativeEnergy
import OAI.Geometry.NodalSets.Waves.LatticeFrequencyAnnulus
import OAI.Geometry.NodalSets.Waves.LatticeFullPlaneWaveApprox
import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
namespace LocalCompactWaveData
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma latticePlaneWaveCoefficient_smooth (hUD : U ⊆ D) (n : ℕ)
    [Fintype (SourceGrid U n)] (x : Coord) (s : ℝ) (i : SourceGrid U n × Fin 3) :
    ContDiff ℝ ∞ (a.latticePlaneWaveCoefficient hUD n x s i) := by
  classical
  unfold latticePlaneWaveCoefficient
  split_ifs
  · exact contDiff_const.mul (planeWave_smooth _ _)
  · exact contDiff_const

lemma latticePlaneWaveCoefficient_energy (hUD : U ⊆ D) (n : ℕ)
    [Fintype (SourceGrid U n)] (x : Coord) (s : ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hm : ∑ i : SourceGrid U n × Fin 3, ‖a.latticeAlpha hUD n x i‖^2 ≤ 1)
    (hb : ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) s) ≤ B)
    (k : ℕ) (v : Coord) :
    ∑ i : SourceGrid U n × Fin 3,
      ‖iteratedFDeriv ℝ k (a.latticePlaneWaveCoefficient hUD n x s i) v‖^2 ≤
        (k.factorial*(4*B)^k)^2 := by
  classical
  have hbound (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k (a.latticePlaneWaveCoefficient hUD n x s i) v‖ ≤
        ‖a.latticeAlpha hUD n x i‖*(k.factorial*(4*B)^k) := by
    unfold latticePlaneWaveCoefficient
    split_ifs with hi
    · exact weighted_planeWave_derivative_bound _ _ s hB (hb i hi) k v
    · simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      positivity
  calc
    _ ≤ ∑ i : SourceGrid U n × Fin 3,
        (‖a.latticeAlpha hUD n x i‖*(k.factorial*(4*B)^k))^2 :=
      Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2)
    _ = (∑ i : SourceGrid U n × Fin 3, ‖a.latticeAlpha hUD n x i‖^2)*
        (k.factorial*(4*B)^k)^2 := by simp only [mul_pow,Finset.sum_mul]
    _ ≤ _ := by nlinarith [sq_nonneg ((k.factorial:ℝ)*(4*B)^k)]
end LocalCompactWaveData

theorem lattice_planeWave_derivative_energy
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : Coord, ∀ k : ℕ, k ≤ d →
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ k
            (a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x) i) v‖^2 ≤ C := by
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus g hH hg hp
  let B' := max 1 B
  let C := ((d.factorial:ℝ)*(4*B')^d)^2
  have hB' : 1 ≤ B' := le_max_left _ _
  have h4 : 1 ≤ 4*B' := by linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
  filter_upwards [hann w S D U m J K k0 a hHD hUD hUH,
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)] with n hn hm
  obtain ⟨hfin,hm⟩ := hm
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v k hk
  apply (a.latticePlaneWaveCoefficient_energy hUD n x _ hB' (by rw [(hm x hx).1])
    (fun i hi ↦ ((hn x (hUH (hQU hx)) i hi).2).trans (le_max_right _ _)) k v).trans
  have hf : (k.factorial:ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hk
  have hpow := pow_le_pow_right₀ h4 hk
  dsimp [C]
  gcongr

end
end Yau.Geometry

end OAI
