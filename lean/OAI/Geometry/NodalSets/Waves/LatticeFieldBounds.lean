import OAI.Geometry.NodalSets.Waves.FiniteWaveDerivativeBounds
import OAI.Geometry.NodalSets.Waves.LatticeCount
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_field_derivative_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        ContDiff ℝ ∞ (gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) ∧
        ∀ x : Coord, ∀ k : Fin (k0+1),
          ‖iteratedFDeriv ℝ k.val (gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤
          C*(n:ℝ)^(k.val+3)*Real.exp ((n:ℝ)*S x) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hUb
  have hcw := a.beams.Cw_pos
  have hbc := a.beams.c_pos
  refine ⟨C*a.beams.Cw,mul_pos hC a.beams.Cw_pos,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  intro coeff hc
  refine ⟨gaussianWaveField_contDiff V coeff hV,?_⟩
  intro x k
  have hb (i : SourceGrid U n × Fin 3) : ‖iteratedFDeriv ℝ k.val (V i) x‖ ≤
      a.beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    refine h.trans ?_
    gcongr
    exact sub_le_self _ (by positivity : 0 ≤ a.beams.c*(n:ℝ)*
      (sourceEuclideanNorm (x-coverSourceCenter a.cover (latticeFrame a.cover hUD n i.1)))^2)
  have h := gaussianWaveField_iterated_bound V coeff hV k.val x (by positivity) hc hb
  have hcardR : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard n hnpos
  refine h.trans ?_
  calc
    _ ≤ (C*(n:ℝ)^2)*(n:ℝ)*(a.beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x)) := by
      gcongr
    _ = (C*a.beams.Cw)*(n:ℝ)^(k.val+3)*Real.exp ((n:ℝ)*S x) := by
      rw [pow_add]
      ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
