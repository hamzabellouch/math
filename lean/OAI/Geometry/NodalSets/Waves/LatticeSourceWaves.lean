import OAI.Geometry.NodalSets.Waves.CompactSourceWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def scaledLatticePoint (n : ℕ) (z : Fin 4 → ℤ) : Coord :=
  (n:ℝ)^(-1/2:ℝ) • (fun i ↦ (z i:ℝ))

abbrev SourceGrid (U : Set Coord) (n : ℕ) := {z : Fin 4 → ℤ // scaledLatticePoint n z ∈ U}

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}

def selectFrame (d : SourceCompactFrameCover g S D) (x : D) : d.Parameter :=
  Classical.choose (d.surjective_center x)

lemma selectFrame_center (d : SourceCompactFrameCover g S D) (x : D) :
    coverSourceCenter d (selectFrame d x) = x :=
  congrArg Subtype.val (Classical.choose_spec (d.surjective_center x))

def latticeFrame (d : SourceCompactFrameCover g S D) (hUD : U ⊆ D)
    (n : ℕ) (z : SourceGrid U n) : d.Parameter :=
  selectFrame d ⟨scaledLatticePoint n z,hUD z.property⟩

lemma latticeFrame_center (d : SourceCompactFrameCover g S D) (hUD : U ⊆ D)
    (n : ℕ) (z : SourceGrid U n) :
    coverSourceCenter d (latticeFrame d hUD n z) = scaledLatticePoint n z :=
  selectFrame_center d _

def latticeWave (d : SourceCompactFrameCover g S D)
    (b : TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0)
    (hUD : U ⊆ D) (n : ℕ) (z : SourceGrid U n) (j : Fin 3) : Coord → ℂ :=
  chartPushforward (b.F (latticeFrame d hUD n z,j))
    (coordinateWave b.phi b.A J (n:ℝ) (latticeFrame d hUD n z,j))

theorem lattice_wave_estimates (d : SourceCompactFrameCover g S D)
    (b : TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0)
    (hUD : U ⊆ D) :
    ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3),
      ContDiff ℝ ∞ (latticeWave d b hUD n z j) ∧ HasCompactSupport (latticeWave d b hUD n z j) ∧
      tsupport (latticeWave d b hUD n z j) ⊆
        {x | sourceEuclideanNorm (x-scaledLatticePoint n z) ≤ b.R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ x : Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (latticeWave d b hUD n z j) x‖ ≤
          b.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x-b.c*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2)) ∧
        DerivativeBound k0 (fun x ↦ sourceWeightedOperator g w (latticeWave d b hUD n z j) x +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*latticeWave d b hUD n z j x) x
            (b.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
  filter_upwards [b.estimates] with n hn
  intro z j
  simpa only [latticeWave,latticeFrame_center] using hn (latticeFrame d hUD n z,j)

theorem lattice_direction_properties (d : SourceCompactFrameCover g S D)
    (hUD : U ⊆ D) (n : ℕ) (z : SourceGrid U n) :
    let x := scaledLatticePoint n z
    let q := d.triple.q (latticeFrame d hUD n z)
    LinearIndependent ℝ q ∧ ∀ j,
      g x (metricGradient g S x) (q j) = 0 ∧
      g x (q j) (q j) = g x (metricGradient g S x) (metricGradient g S x)+4 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x)+sourceHessian g S x (q j) (q j) := by
  have he := latticeFrame_center d hUD n z
  refine ⟨d.triple.independent _,?_⟩
  intro j
  have hp := d.triple.perpendicular (latticeFrame d hUD n z) j
  have hl := d.triple.length (latticeFrame d hUD n z) j
  have hs := d.triple.strict (latticeFrame d hUD n z) j
  change g (coverSourceCenter d _) (metricGradient g S (coverSourceCenter d _)) _ = 0 at hp
  change g (coverSourceCenter d _) _ _ = g (coverSourceCenter d _) (metricGradient g S (coverSourceCenter d _))
    (metricGradient g S (coverSourceCenter d _))+4 at hl
  change 0 < sourceHessian g S (coverSourceCenter d _) (metricGradient g S (coverSourceCenter d _))
    (metricGradient g S (coverSourceCenter d _))+sourceHessian g S (coverSourceCenter d _) _ _ at hs
  rw [he] at hp hl hs
  exact ⟨hp,hl,hs⟩

end
end Yau.Geometry

end OAI
