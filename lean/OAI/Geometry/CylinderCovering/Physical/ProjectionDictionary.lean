import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RadialPhysical
open CylinderCovering

lemma upperPhysicalAxis_canonical {b : ℝ} (hb : b ≠ 0) (eta s : ℝ) :
    upperPhysicalAxis b eta s =
      RadialPairedSweep.upperAxis (Real.sqrt 2) (effectiveTilt b eta) (s/b) := by
  have hv : point b 1 (-eta*(s^2+b^2)/2) (eta*s) =
      RadialPairedSweep.point 1
        (-(effectiveTilt b eta)*RadialCaps.G (s/b))
        (Real.sqrt 2*effectiveTilt b eta*(s/b)) := by
    ext i
    fin_cases i <;>
      simp [point, RadialPairedSweep.point, height, effectiveTilt, RadialCaps.G] <;>
      field_simp
    ring
  unfold upperPhysicalAxis RadialPairedSweep.upperAxis
  rw [hv]

lemma lowerPhysicalAxis_canonical {b : ℝ} (hb : b ≠ 0) (eta s : ℝ) :
    lowerPhysicalAxis b eta s =
      RadialPairedSweep.lowerAxis (Real.sqrt 2) (effectiveTilt b eta) (s/b) := by
  have hv : point b (eta*(s^2+b^2)/2) 1 (eta*s) =
      RadialPairedSweep.point ((effectiveTilt b eta)*RadialCaps.G (s/b)) 1
        (Real.sqrt 2*effectiveTilt b eta*(s/b)) := by
    ext i
    fin_cases i <;>
      simp [point, RadialPairedSweep.point, height, effectiveTilt, RadialCaps.G] <;>
      field_simp
    ring
  unfold lowerPhysicalAxis RadialPairedSweep.lowerAxis
  rw [hv]

lemma mapToCanonical_eq_similarity (b : ℝ) :
    mapToCanonical b = Similarity.map (-(!₂[0,0,Real.sqrt 2] : Space))
      (2/b) (LinearIsometryEquiv.refl ℝ Space) := by
  funext z
  change (2/b) • z - (!₂[0,0,Real.sqrt 2] : Space) =
    -(!₂[0,0,Real.sqrt 2] : Space) + (2/b) • z
  module

lemma mapCenteredToCanonical_eq_similarity (b : ℝ) :
    mapCenteredToCanonical b = Similarity.map (0 : Space)
      (1/b) (LinearIsometryEquiv.refl ℝ Space) := by
  funext z
  simp [mapCenteredToCanonical, Similarity.map]

lemma projection_mapToCanonical (b : ℝ) (u z : Space) :
    TriangularCovering.projection u (mapToCanonical b z) =
      (2/b) • TriangularCovering.projection u z -
        TriangularCovering.projection u (!₂[0,0,Real.sqrt 2] : Space) := by
  simp only [TriangularCovering.projection, mapToCanonical,
    inner_sub_right, inner_smul_right]
  module

lemma projection_mapCenteredToCanonical (b : ℝ) (u z : Space) :
    TriangularCovering.projection u (mapCenteredToCanonical b z) =
      (1/b) • TriangularCovering.projection u z := by
  simp only [TriangularCovering.projection, mapCenteredToCanonical, inner_smul_right]
  module

lemma projected_image_mapToCanonical (b : ℝ) (u : Space) (S : Set Space) :
    TriangularCovering.projection u '' (mapToCanonical b '' S) =
      (fun z => (2/b) • z -
        TriangularCovering.projection u (!₂[0,0,Real.sqrt 2] : Space)) ''
          (TriangularCovering.projection u '' S) := by
  simp only [Set.image_image]
  congr 1
  funext z
  exact projection_mapToCanonical b u z

lemma projected_image_mapCenteredToCanonical (b : ℝ) (u : Space) (S : Set Space) :
    TriangularCovering.projection u '' (mapCenteredToCanonical b '' S) =
      (fun z => (1/b) • z) '' (TriangularCovering.projection u '' S) := by
  simp only [Set.image_image]
  congr 1
  funext z
  exact projection_mapCenteredToCanonical b u z

lemma projected_area_mapToCanonical {b : ℝ} (hb : b ≠ 0) (u : Space) (S : Set Space) :
    TriangularCovering.area (TriangularCovering.projection u '' (mapToCanonical b '' S)) =
      (2/b)^2 * TriangularCovering.area (TriangularCovering.projection u '' S) := by
  rw [mapToCanonical_eq_similarity]
  exact Similarity.shadowArea_map S _ (div_ne_zero (by norm_num) hb)
    (LinearIsometryEquiv.refl ℝ Space) u

lemma projected_area_mapCenteredToCanonical {b : ℝ} (hb : b ≠ 0)
    (u : Space) (S : Set Space) :
    TriangularCovering.area
      (TriangularCovering.projection u '' (mapCenteredToCanonical b '' S)) =
      (1/b)^2 * TriangularCovering.area (TriangularCovering.projection u '' S) := by
  rw [mapCenteredToCanonical_eq_similarity]
  exact Similarity.shadowArea_map S _ (div_ne_zero one_ne_zero hb)
    (LinearIsometryEquiv.refl ℝ Space) u

lemma cylinder_mapToCanonical {b : ℝ} (hb : b ≠ 0) (u : Space) (B : Set Space) :
    mapToCanonical b '' RadialSweep.cylinder u B =
      RadialSweep.cylinder u
        ((fun z => (2/b) • z - TriangularCovering.projection u
          (!₂[0,0,Real.sqrt 2] : Space)) '' B) := by
  have hbase : Similarity.transportedBase B u (-(!₂[0,0,Real.sqrt 2] : Space))
      (2/b) (LinearIsometryEquiv.refl ℝ Space) =
        (fun z => (2/b) • z - TriangularCovering.projection u
          (!₂[0,0,Real.sqrt 2] : Space)) '' B := by
    unfold Similarity.transportedBase
    congr 1
    funext z
    change (-(!₂[0,0,Real.sqrt 2] : Space) -
        (inner ℝ u (-(!₂[0,0,Real.sqrt 2] : Space))) • u) + (2/b) • z =
      (2/b) • z - ((!₂[0,0,Real.sqrt 2] : Space) -
        (inner ℝ u (!₂[0,0,Real.sqrt 2] : Space)) • u)
    simp only [inner_neg_right, neg_smul]
    module
  rw [mapToCanonical_eq_similarity]
  change Similarity.map _ (2/b) (LinearIsometryEquiv.refl ℝ Space) ''
    Similarity.carrier B u = Similarity.carrier _ u
  rw [Similarity.carrier_image B u _ (div_ne_zero (by norm_num) hb), hbase]
  rfl

lemma cylinder_mapCenteredToCanonical {b : ℝ} (hb : b ≠ 0)
    (u : Space) (B : Set Space) :
    mapCenteredToCanonical b '' RadialSweep.cylinder u B =
      RadialSweep.cylinder u ((fun z => (1/b) • z) '' B) := by
  rw [mapCenteredToCanonical_eq_similarity]
  change Similarity.map _ (1/b) (LinearIsometryEquiv.refl ℝ Space) ''
    Similarity.carrier B u = Similarity.carrier _ u
  rw [Similarity.carrier_image B u _ (div_ne_zero one_ne_zero hb)]
  have hbase : Similarity.baseMap u (0 : Space) (1/b)
      (LinearIsometryEquiv.refl ℝ Space) = fun vector => (1/b) • vector := by
    funext vector
    simp [Similarity.baseMap, Similarity.project]
  exact congrArg (fun base => Similarity.carrier (base '' B) u) hbase

end RadialPhysical

end

end OAI
