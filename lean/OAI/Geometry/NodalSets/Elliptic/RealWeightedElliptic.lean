import OAI.Geometry.NodalSets.Elliptic.RealMatrixEnergy
import OAI.Geometry.NodalSets.Elliptic.RealWeightedTransport

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section

def realMatrixFlux (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  ∑ j, B x i j*Yau.coordPartial w x j

def realWeightedElliptic (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) : Yau.Jets.Coord → ℝ := Yau.weightedDiv gamma (realMatrixFlux B w)

lemma realMatrixFlux_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realMatrixFlux B w x i) :=
  ContDiff.sum (fun j _ ↦ (hB i j).mul (Yau.real_coordPartial_smooth w hw j))

lemma realMatrixFlux_compact (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport w) (i : Fin 4) : HasCompactSupport (fun x ↦ realMatrixFlux B w x i) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    (hc.fderiv_apply ℝ (Pi.single j 1)).mul_left (f := fun x ↦ B x i j))
  exact h

lemma realWeightedElliptic_smooth (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (realWeightedElliptic gamma B w) :=
  Yau.weightedDiv_smooth hg hgn (realMatrixFlux_smooth B w hB hw)

lemma realWeightedElliptic_compact (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport w) : HasCompactSupport (realWeightedElliptic gamma B w) := by
  have h := (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    ((realMatrixFlux_compact B w hc i).mul_left (f := gamma)).fderiv_apply ℝ (Pi.single i 1))).mul_left
      (f := fun x ↦ (gamma x)⁻¹)
  exact h

lemma realMatrixEnergy_pairing (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (realMatrixFlux B v) x = realMatrixEnergy B u v x := by
  simp only [Yau.pairing,realMatrixFlux,realMatrixEnergy_apply,Finset.mul_sum,mul_assoc]

lemma realMatrixEnergy_symmetric (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B u v x = realMatrixEnergy B v u x :=
  coordMatrixForm_symmetric (B x) (hs x) _ _

theorem real_weighted_elliptic_green (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u) :
    Integrable (fun x ↦ gamma x*realMatrixEnergy B u v x) ∧
    Integrable (fun x ↦ gamma x*u x*realWeightedElliptic gamma B v x) ∧
    (∫ x, gamma x*u x*realWeightedElliptic gamma B v x) =
      -(∫ x, gamma x*realMatrixEnergy B u v x) := by
  obtain ⟨hiE,hiL,he⟩ := Yau.compact_weighted_integration_by_parts gamma u hg hgn hu hc
    (realMatrixFlux B v) (realMatrixFlux_smooth B v hB hv)
  simp only [realMatrixEnergy_pairing] at hiE he
  refine ⟨hiE,hiL,?_⟩
  change (∫ x, gamma x*u x*Yau.weightedDiv gamma (realMatrixFlux B v) x) = _
  linarith only [he]

theorem real_weighted_elliptic_symmetric (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) :
    (∫ x, gamma x*u x*realWeightedElliptic gamma B v x) =
      (∫ x, gamma x*v x*realWeightedElliptic gamma B u x) := by
  rw [(real_weighted_elliptic_green gamma B u v hg hgn hB hu hv hcu).2.2,
    (real_weighted_elliptic_green gamma B v u hg hgn hB hv hu hcv).2.2]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [realMatrixEnergy_symmetric B hs u v]

end
end Yau.Geometry

end OAI
