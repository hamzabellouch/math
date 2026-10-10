import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField
import OAI.Geometry.NodalSets.Waves.LatticeFieldBounds

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem literal_seeded_lattice_field_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := fun z ↦ seedCoordinateField n z + gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z
        ContDiff ℝ ∞ u ∧ ∀ x ∈ Q, ∀ k : Fin (k0+1),
          ‖iteratedFDeriv ℝ k.val u x‖ ≤ C*(n:ℝ)^(k.val+3)*
            max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
  have hs (j : Fin (k0+1)) := seedCoordinateField_derivative_bound hQ hQB j.val
  choose b hb hseed using hs
  let B : ℝ := ∑ j, b j
  have hB : 0 < B := (hb ⟨0,by omega⟩).trans_le
    (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
  obtain ⟨C,hC,hfield⟩ := a.lattice_field_derivative_bound hUD hUb
  refine ⟨B+C,by positivity,?_⟩
  filter_upwards [hfield,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hbnd⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hc
  obtain ⟨hV,hVb⟩ := hbnd coeff hc
  have hseedSmooth := seedCoordinateField_smooth n
  refine ⟨hseedSmooth.add hV,?_⟩
  intro x hx k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hseed' : ‖iteratedFDeriv ℝ k.val (seedCoordinateField n) x‖ ≤
      B*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
    have h := hseed k n hnpos x hx
    refine h.trans ?_
    have hbB : b k ≤ B := Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _)
    gcongr
    · omega
    · exact le_max_right _ _
  have hrand : ‖iteratedFDeriv ℝ k.val (gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤
      C*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
    refine (hVb x k).trans ?_
    gcongr
    exact le_max_left _ _
  change ‖iteratedFDeriv ℝ k.val (seedCoordinateField n + gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hseedSmooth.of_le
    (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hV.of_le (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  have h := (norm_add_le _ _).trans (add_le_add hseed' hrand)
  convert h using 1; first | rfl | ring

end
end Yau.Target

end OAI
