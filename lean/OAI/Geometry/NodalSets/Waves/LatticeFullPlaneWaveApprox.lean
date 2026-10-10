import OAI.Geometry.NodalSets.Waves.LatticePlaneWaveJets
import OAI.Geometry.NodalSets.Waves.RescaledLatticeTail

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticePlaneWaveCoefficient (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : Coord) (s : ℝ) (i : SourceGrid U n × Fin 3) (v : Coord) : ℂ :=
  if sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) then
    a.latticeAlpha hUD n x i *
      planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s v
  else 0

theorem lattice_full_jet_approximation (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i : SourceGrid U n × Fin 3,
        ‖iteratedFDeriv ℝ k.val (fun z ↦
          normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
            (a.latticeSigma hUD n x) x z - a.latticePlaneWaveCoefficient hUD n x s i z) v‖^2 ≤ e := by
  classical
  filter_upwards [a.lattice_main_jet_approximation hUD hU hUb hQ hQU R hR k0 (e/2) (by positivity),
    a.rescaled_lattice_nonmain_negligible hUD hU hUb hQ hQU hS R hR (e/2) (by positivity)]
    with n hmain htail
  obtain ⟨hfin,hm⟩ := hmain
  obtain ⟨hfin',ht⟩ := htail
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  let P := fun i : SourceGrid U n × Fin 3 ↦
    sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)
  let err := fun i : SourceGrid U n × Fin 3 ↦
    ‖iteratedFDeriv ℝ k.val (fun z ↦
      normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
        (a.latticeSigma hUD n x) x z-a.latticePlaneWaveCoefficient hUD n x s i z) v‖^2
  have hm' : ∑ i ∈ Finset.univ.filter P, err i ≤ e/2 := by
    have hh := hm x hx s hs v hv k.val (by omega)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    dsimp only [P] at hp
    simp only [err,latticePlaneWaveCoefficient,ite_eq_left hp]
  have ht' : ∑ i ∈ Finset.univ.filter (fun i ↦ ¬P i), err i ≤ e/2 := by
    have hh := ht x hx s hs v hv k
    convert hh using 1
    · apply Finset.sum_congr
      · ext i; simp only [P,Finset.mem_filter,not_le]
      · intro i hi
        have hp := (Finset.mem_filter.mp hi).2
        simp only [err,latticePlaneWaveCoefficient,ite_eq_right (not_le.mpr hp),sub_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) P err
  change ∑ i, err i ≤ e
  linarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
