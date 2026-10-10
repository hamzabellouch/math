import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HoleTail
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.NaturalTailMoments
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters

namespace OAI

noncomputable section

open scoped BigOperators

open Set MeasureTheory

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

lemma measurable_siteDiameter {Ω : Type*} [MeasurableSpace Ω] (B : Ω → Finset Vertex)
    (hB : Measurable B) (lo hi z : Vertex) :
    Measurable (fun ω => siteDiameter (holes (B ω) lo hi) z) :=
  (measurable_of_countable (fun C : Finset Vertex => siteDiameter (holes C lo hi) z)).comp hB

lemma measurable_edgeDiameter {Ω : Type*} [MeasurableSpace Ω] (B : Ω → Finset Vertex)
    (hB : Measurable B) (lo hi : Vertex) (e : Edge) :
    Measurable (fun ω => edgeDiameter (holes (B ω) lo hi) e) :=
  (measurable_of_countable (fun C : Finset Vertex => edgeDiameter (holes C lo hi) e)).comp hB

lemma hole_moments (q : ℕ) : ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Finset Vertex) (B : Ω → Finset Vertex)
    (lo hi : Vertex), Measurable B → (∀ ω, B ω ⊆ A) → A ⊆ box lo hi →
    (∀ S : Finset Vertex, μ {ω | S ⊆ B ω} ≤ (1/1024:ENNReal)^S.card) →
    (∀ z : Vertex, (∫⁻ ω,((siteDiameter (holes (B ω) lo hi) z+1:ℕ):ENNReal)^q ∂μ) ≤ C) ∧
    (∀ e : Edge, (∫⁻ ω,((edgeDiameter (holes (B ω) lo hi) e+1:ℕ):ENNReal)^q ∂μ) ≤ 2*C) := by
  obtain ⟨C,hC⟩ := natural_tail_moments q
  refine ⟨C,?_⟩
  intro Ω _ μ _ A B lo hi hB hBA hbox hsparse
  have hz (z : Vertex) : (∫⁻ ω,((siteDiameter (holes (B ω) lo hi) z+1:ℕ):ENNReal)^q ∂μ) ≤ C :=
    hC μ _ (measurable_siteDiameter B hB lo hi z) (hole_diameter_tail μ A B lo hi hBA hbox hsparse z)
  refine ⟨hz,?_⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hpoint (ω : Ω) : ((edgeDiameter (holes (B ω) lo hi) s(x,y)+1:ℕ):ENNReal)^q ≤
        ((siteDiameter (holes (B ω) lo hi) x+1:ℕ):ENNReal)^q+
        ((siteDiameter (holes (B ω) lo hi) y+1:ℕ):ENNReal)^q := by
      change ((max (siteDiameter (holes (B ω) lo hi) x) (siteDiameter (holes (B ω) lo hi) y)+1:ℕ):ENNReal)^q ≤ _
      rcases le_total (siteDiameter (holes (B ω) lo hi) x) (siteDiameter (holes (B ω) lo hi) y) with hh|hh
      · rw [max_eq_right hh];exact le_add_self
      · rw [max_eq_left hh];exact le_self_add
    have hxM : Measurable (fun ω => ((siteDiameter (holes (B ω) lo hi) x+1:ℕ):ENNReal)^q) :=
      (measurable_of_countable (fun n : ℕ => ((n+1:ℕ):ENNReal)^q)).comp (measurable_siteDiameter B hB lo hi x)
    have hyM : Measurable (fun ω => ((siteDiameter (holes (B ω) lo hi) y+1:ℕ):ENNReal)^q) :=
      (measurable_of_countable (fun n : ℕ => ((n+1:ℕ):ENNReal)^q)).comp (measurable_siteDiameter B hB lo hi y)
    calc
      _ ≤ ∫⁻ ω,((siteDiameter (holes (B ω) lo hi) x+1:ℕ):ENNReal)^q+
          ((siteDiameter (holes (B ω) lo hi) y+1:ℕ):ENNReal)^q ∂μ := lintegral_mono hpoint
      _ = (∫⁻ ω,((siteDiameter (holes (B ω) lo hi) x+1:ℕ):ENNReal)^q ∂μ)+
          (∫⁻ ω,((siteDiameter (holes (B ω) lo hi) y+1:ℕ):ENNReal)^q ∂μ) := lintegral_add_left hxM _
      _ ≤ C+C := add_le_add (hz x) (hz y)
      _ = 2*C := by ring

end SparseHoles

end

end OAI
