import OAI.Geometry.CylinderCovering.Beams.MainDefinitions
import OAI.Geometry.CylinderCovering.Beams.Finite
import OAI.Geometry.CylinderCovering.Beams.ShortenedBeamStrip
import OAI.Geometry.CylinderCovering.Beams.Rectangle
import OAI.Geometry.CylinderCovering.Beams.Cost
import OAI.Geometry.CylinderCovering.Convexity.CylinderBridge
import OAI.Geometry.CylinderCovering.Convexity.RegularCounterexamples

namespace OAI

noncomputable section
open Set MeasureTheory
namespace ShortenedBeam
open CylinderCovering

theorem triCylinder_hasTriangularBase (C : TriangularCovering.TriCylinder) :
    HasTriangularBase C.toCylinder := by
  obtain ⟨v,hv,hbase⟩ := C.triangular
  exact ⟨v,hv,C.toCylinder_base_image.trans hbase⟩

theorem stripCost_physical (a : ℝ) :
    (Real.sqrt 2/4)*BeamCost.stripCost a =
      ∫ t in (-1:ℝ)..1, width a t/Real.sqrt (1+(a*t-a^2*t^3)^2) := by
  have hs : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold BeamCost.stripCost BeamCost.stripDensity BeamCost.stripWidth width
  ring_nf
  rw [hs]
  ring

theorem finiteStripStatement : FiniteStripStatement := by
  intro a ε hε
  rw [stripCost_physical]
  exact finite_strip_actual a hε

theorem finiteCover_union {P : RuledApproximation.Cylinder → Prop}
    {S T : Set Space} {A B : ℝ}
    (hS : RuledApproximation.HasFiniteCover P S A)
    (hT : RuledApproximation.HasFiniteCover P T B) :
    RuledApproximation.HasFiniteCover P (S ∪ T) (A+B) := by
  obtain ⟨m,C,hC,hSC,hA⟩ := hS
  obtain ⟨n,D,hD,hTD,hB⟩ := hT
  let E : Fin (m+n) → RuledApproximation.Cylinder := Fin.addCases C D
  refine ⟨m+n,E,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [E] using hC j
    · simpa [E] using hD j
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (hSC hz)
      apply mem_iUnion.mpr
      exact ⟨i.castAdd n, by simpa [E] using hi⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (hTD hz)
      apply mem_iUnion.mpr
      exact ⟨i.natAdd m, by simpa [E] using hi⟩
  · change (∑ i, (E i).area) ≤ A+B
    rw [Fin.sum_univ_add]
    simpa [E, RuledApproximation.familyArea] using add_le_add hA hB

theorem finite_beams_mixed {a ε : ℝ} (ha : 0 < a) (ha' : a < 1/2)
    (hε : 0 < ε) :
    RuledApproximation.HasFiniteCover HasMixedBase (beamMinus a ∪ beamPlus a)
      ((Real.sqrt 2/4)*BeamCost.beamCost a+ε) := by
  obtain ⟨N,_,C,D,hC,hD,hcost⟩ := finite_beam_cover ha ha' hε
  have hleft : RuledApproximation.HasFiniteCover HasMixedBase (beamMinus a)
      (TriangularCovering.totalArea C) := by
    refine ⟨N,fun i => (C i).toCylinder,fun i => Or.inl (triCylinder_hasTriangularBase _),?_,?_⟩
    · intro z hz
      obtain ⟨i,hi⟩ := hC z hz
      exact mem_iUnion.mpr ⟨i,by simpa only [TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩
    · simp [RuledApproximation.familyArea,TriangularCovering.totalArea]
  have hright : RuledApproximation.HasFiniteCover HasMixedBase (beamPlus a)
      (TriangularCovering.totalArea D) := by
    refine ⟨N,fun i => (D i).toCylinder,fun i => Or.inl (triCylinder_hasTriangularBase _),?_,?_⟩
    · intro z hz
      obtain ⟨i,hi⟩ := hD z hz
      exact mem_iUnion.mpr ⟨i,by simpa only [TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩
    · simp [RuledApproximation.familyArea,TriangularCovering.totalArea]
  obtain ⟨n,E,hE,hcover,harea⟩ := finiteCover_union hleft hright
  exact ⟨n,E,hE,hcover,harea.trans hcost⟩

theorem canonicalCounterexample : CanonicalCounterexampleStatement := by
  obtain ⟨a,ha,ha',hgain⟩ := BeamCost.exists_strict_gain
  let A := (Real.sqrt 2/4)*(BeamCost.beamCost a+BeamCost.stripCost a)
  have hA : A < Real.sqrt 2 := by
    have h := mul_lt_mul_of_pos_left hgain (by positivity : 0 < Real.sqrt (2:ℝ)/4)
    dsimp [A]
    nlinarith
  let ε := (Real.sqrt 2-A)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbeams := finite_beams_mixed ha ha' hε
  obtain ⟨n,C,hC,hcover,hcost⟩ := finiteStripStatement a ε hε
  have hstrip : RuledApproximation.HasFiniteCover HasMixedBase (strip a)
      ((Real.sqrt 2/4)*BeamCost.stripCost a+ε) :=
    ⟨n,C,fun i => Or.inr ((hC i).hasRectangularBase),hcover,hcost⟩
  obtain ⟨m,D,hD,hcov,harea⟩ := finiteCover_union hbeams hstrip
  refine ⟨m,D,hD,(tetrahedron_covered ha.le ha'.le).trans hcov,?_⟩
  dsimp [A,ε] at *
  nlinarith

theorem finiteMixedStatement : CoreFiniteMixedStatement := by
  intro a ε ha ha' hε
  have he : 0 < ε/2 := by linarith
  have hbeams := finite_beams_mixed ha ha' he
  obtain ⟨n,C,hC,hcover,hcost⟩ := finiteStripStatement a (ε/2) he
  have hstrip : RuledApproximation.HasFiniteCover HasMixedBase (strip a)
      ((Real.sqrt 2/4)*BeamCost.stripCost a+ε/2) :=
    ⟨n,C,fun i => Or.inr ((hC i).hasRectangularBase),hcover,hcost⟩
  obtain ⟨m,D,hD,hcov,harea⟩ := finiteCover_union hbeams hstrip
  refine ⟨m,D,hD,(tetrahedron_covered ha.le ha'.le).trans hcov,?_⟩
  nlinarith

theorem regularMixedCounterexample : RegularMixedCounterexampleStatement := by
  intro K hK
  obtain ⟨n,C,hcover,harea,hrelative⟩ := regularTriangularCounterexample_result K hK
  refine ⟨n,fun i => (C i).toCylinder,
    fun i => Or.inl (triCylinder_hasTriangularBase _),?_,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,by simpa only [TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩
  · simpa only [RuledApproximation.familyArea,TriangularCovering.totalArea,
      TriangularCovering.TriCylinder.toCylinder_area] using harea
  · simpa only [relativeCost,triangularRelativeCost,
      TriangularCovering.TriCylinder.toCylinder_area,
      TriangularCovering.TriCylinder.toCylinder_axis] using hrelative

end ShortenedBeam

end

end OAI
