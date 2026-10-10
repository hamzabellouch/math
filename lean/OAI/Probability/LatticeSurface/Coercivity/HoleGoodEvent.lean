import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleMoments
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HoleTail
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.MomentMarkov
import OAI.Probability.LatticeSurface.Coercivity.NaturalTailMoments
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Coercivity.ThreeEvents

namespace OAI

noncomputable section

open scoped BigOperators

open Set MeasureTheory

open MeasureTheory

open scoped NNReal ENNReal

open MeasureTheory

open scoped NNReal ENNReal

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

lemma hole_good_moment_event (q : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset Vertex) (B : Ω → Finset Vertex) (lo hi : Vertex),
    Measurable B → (∀ ω,B ω⊆A) → A⊆box lo hi →
    (∀ S : Finset Vertex, μ {ω | S⊆B ω} ≤ (1/1024:ENNReal)^S.card) →
    ∀ (S P : Finset Vertex) (F : Finset Edge) (ν : Vertex → ℝ≥0),
    ∃ G : Set (Finset Vertex),
      (1/2:ENNReal) ≤ μ {ω | B ω∈G} ∧
      ∀ D∈G,
        (∑ z∈S,(siteDiameter (holes D lo hi) z+1:ℝ)^q) ≤ C*(S.card+1) ∧
        (∑ e∈F,(edgeDiameter (holes D lo hi) e+1:ℝ)^q) ≤ C*(F.card+1) ∧
        (∑ z∈P,(ν z:ℝ)*(siteDiameter (holes D lo hi) z+1)) ≤ C*((∑ z∈P,(ν z:ℝ))+1) := by
  classical
  obtain ⟨Cq,hCq⟩ := hole_moments q
  obtain ⟨C1,hC1⟩ := hole_moments 1
  let C₀ : ℝ≥0 := 2*Cq+C1
  let C : ℝ≥0 := 64*(C₀+1)
  have hC : 1 ≤ C := by
    exact (show (1:ℝ≥0)≤64 by norm_num).trans (by simp [C])
  refine ⟨C,by exact_mod_cast hC,?_⟩
  intro Ω _ μ _ A B lo hi hB hBA hbox hsparse S P F ν
  have hq := hCq μ A B lo hi hB hBA hbox hsparse
  have h1 := hC1 μ A B lo hi hB hBA hbox hsparse
  have hqc : (Cq:ENNReal) ≤ C₀ := by
    have hh : Cq≤C₀ := by dsimp [C₀];nlinarith [show (0:ℝ≥0)≤Cq from bot_le,show (0:ℝ≥0)≤C1 from bot_le]
    exact_mod_cast hh
  have hqe : (2*Cq:ENNReal) ≤ C₀ := by
    have hh : 2*Cq≤C₀ := by dsimp [C₀];exact le_self_add
    exact_mod_cast hh
  have hqc1 : (C1:ENNReal) ≤ C₀ := by
    have hh : C1≤C₀ := by dsimp [C₀];exact le_add_self
    exact_mod_cast hh
  let fS : Finset Vertex → ℝ≥0 := fun D => ∑ z∈S,((siteDiameter (holes D lo hi) z+1:ℕ):ℝ≥0)^q
  let fF : Finset Vertex → ℝ≥0 := fun D => ∑ e∈F,((edgeDiameter (holes D lo hi) e+1:ℕ):ℝ≥0)^q
  let fP : Finset Vertex → ℝ≥0 := fun D => ∑ z∈P,ν z*((siteDiameter (holes D lo hi) z+1:ℕ):ℝ≥0)
  let tS : ℝ≥0 := C*(S.card+1)
  let tF : ℝ≥0 := C*(F.card+1)
  let tP : ℝ≥0 := C*((∑ z∈P,ν z)+1)
  let ES : Set Ω := {ω | tS ≤ fS (B ω)}
  let EF : Set Ω := {ω | tF ≤ fF (B ω)}
  let EP : Set Ω := {ω | tP ≤ fP (B ω)}
  have hES : μ ES ≤ (1/64:ENNReal) := by
    have hm := weighted_moment_markov μ S (fun _ => 1)
      (fun z ω => ((siteDiameter (holes (B ω) lo hi) z+1:ℕ):ENNReal)^q)
      (fun z hz => (measurable_of_countable (fun D : Finset Vertex => ((siteDiameter (holes D lo hi) z+1:ℕ):ENNReal)^q)).comp hB)
      C₀ (fun z hz => (hq.1 z).trans hqc)
    convert hm using 1
    congr 1
    ext ω
    change tS ≤ fS (B ω) ↔ _
    rw [← ENNReal.coe_le_coe]
    simp [tS,C,fS]
  have hEF : μ EF ≤ (1/64:ENNReal) := by
    have hm := weighted_moment_markov μ F (fun _ => 1)
      (fun e ω => ((edgeDiameter (holes (B ω) lo hi) e+1:ℕ):ENNReal)^q)
      (fun e he => (measurable_of_countable (fun D : Finset Vertex => ((edgeDiameter (holes D lo hi) e+1:ℕ):ENNReal)^q)).comp hB)
      C₀ (fun e he => (hq.2 e).trans hqe)
    convert hm using 1
    congr 1
    ext ω
    change tF ≤ fF (B ω) ↔ _
    rw [← ENNReal.coe_le_coe]
    simp [tF,C,fF]
  have hEP : μ EP ≤ (1/64:ENNReal) := by
    have hm := weighted_moment_markov μ P ν
      (fun z ω => ((siteDiameter (holes (B ω) lo hi) z+1:ℕ):ENNReal)^1)
      (fun z hz => (measurable_of_countable (fun D : Finset Vertex => ((siteDiameter (holes D lo hi) z+1:ℕ):ENNReal)^1)).comp hB)
      C₀ (fun z hz => (h1.1 z).trans hqc1)
    convert hm using 1
    congr 1
    ext ω
    change tP ≤ fP (B ω) ↔ _
    rw [← ENNReal.coe_le_coe]
    simp [tP,C,fP]
  have mS : MeasurableSet ES := measurableSet_le measurable_const ((measurable_of_countable fS).comp hB)
  have mF : MeasurableSet EF := measurableSet_le measurable_const ((measurable_of_countable fF).comp hB)
  have mP : MeasurableSet EP := measurableSet_le measurable_const ((measurable_of_countable fP).comp hB)
  let G : Set (Finset Vertex) := {D | fS D<tS ∧ fF D<tF ∧ fP D<tP}
  refine ⟨G,?_,?_⟩
  · have he : {ω | B ω∈G}=(ES ∪ EF ∪ EP)ᶜ := by ext ω;simp [G,ES,EF,EP,not_le];tauto
    rw [he]
    exact probability_three_complements μ ES EF EP mS mF mP hES hEF hEP
  · intro D hD
    have hs : (fS D:ℝ) ≤ tS := by exact_mod_cast hD.1.le
    have hf : (fF D:ℝ) ≤ tF := by exact_mod_cast hD.2.1.le
    have hp : (fP D:ℝ) ≤ tP := by exact_mod_cast hD.2.2.le
    constructor
    · simpa [fS,tS] using hs
    constructor
    · simpa [fF,tF] using hf
    · simpa [fP,tP] using hp

end SparseHoles

end

end OAI
