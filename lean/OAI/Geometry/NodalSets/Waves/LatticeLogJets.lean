import OAI.Geometry.NodalSets.Elliptic.LocalLogJetBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeEta (hUD : U ⊆ D) (n : ℕ) (z : SourceGrid U n) (j : Fin 3) : ℝ :=
  a.originalEta (latticeFrame a.cover hUD n z,j)

theorem lattice_logarithmic_jet_estimates (hUD : U ⊆ D) (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3) (x : Coord),
      ‖x-scaledLatticePoint n z‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
      let t := (latticeFrame a.cover hUD n z,j)
      let V := latticeWave a.cover a.beams hUD n z j
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧ V x ≠ 0 ∧
      (c ≤ ‖V x‖*Real.exp (-(n:ℝ)*S x) ∧ ‖V x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
      ∀ v,
      |(normalizedLogJet n V x v).re -
        (fderiv ℝ S x v-a.latticeEta hUD n z j*g (scaledLatticePoint n z) (x-scaledLatticePoint n z) v)| ≤ Cr/n*‖v‖ ∧
      |(normalizedLogJet n V x v).im - g (scaledLatticePoint n z) (a.cover.triple.q t.1 t.2) v| ≤
        Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖ := by
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,hb⟩ := a.original_logarithmic_jet_estimates L hL
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,?_⟩
  filter_upwards [hb] with n hn
  intro z j x hx
  have hx' : ‖x-coverSourceCenter a.cover (latticeFrame a.cover hUD n z)‖ ≤ L*(n:ℝ)^(-1/2:ℝ) := by
    simpa only [latticeFrame_center] using hx
  simpa only [latticeWave,TripleSourceWaveData.wave,latticeEta,latticeFrame_center] using
    hn (latticeFrame a.cover hUD n z,j) x hx'

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
