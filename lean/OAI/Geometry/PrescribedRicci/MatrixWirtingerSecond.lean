import Mathlib
import OAI.Geometry.PrescribedRicci.MatrixWirtinger

namespace OAI

/-! Matrix Wirtinger Second. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

def barMatrixForm (a : Fin d) : (Coordinates d →L[ℝ] Mat) →L[ℝ] Mat :=
  (2:ℂ)⁻¹ • ((ContinuousLinearMap.apply ℝ Mat (coordinateVector a)) +
    Complex.I • (ContinuousLinearMap.apply ℝ Mat (Complex.I • coordinateVector a)))

def holMatrixForm (a : Fin d) : (Coordinates d →L[ℝ] Mat) →L[ℝ] Mat :=
  (2:ℂ)⁻¹ • ((ContinuousLinearMap.apply ℝ Mat (coordinateVector a)) -
    Complex.I • (ContinuousLinearMap.apply ℝ Mat (Complex.I • coordinateVector a)))

lemma fderiv_barDerivative {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => barDerivative f y a) z v =
      (2:ℂ)⁻¹ • (fderiv ℝ (fderiv ℝ f) z v (coordinateVector a) +
        Complex.I • fderiv ℝ (fderiv ℝ f) z v (Complex.I • coordinateVector a)) := by
  exact congrArg (fun L : Coordinates d →L[ℝ] Mat => L v)
    (((barMatrixForm a).hasFDerivAt.comp z
      ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv)

lemma fderiv_holDerivative {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) (v : Coordinates d) :
    fderiv ℝ (fun y => holDerivative f y a) z v =
      (2:ℂ)⁻¹ • (fderiv ℝ (fderiv ℝ f) z v (coordinateVector a) -
        Complex.I • fderiv ℝ (fderiv ℝ f) z v (Complex.I • coordinateVector a)) := by
  exact congrArg (fun L : Coordinates d →L[ℝ] Mat => L v)
    (((holMatrixForm a).hasFDerivAt.comp z
      ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv)

lemma bar_hol_comm {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a b : Fin d) :
    barDerivative (fun y => holDerivative f y a) z b =
      holDerivative (fun y => barDerivative f y b) z a := by
  unfold barDerivative holDerivative
  have ha := fderiv_holDerivative hf a (coordinateVector b)
  have hb := fderiv_holDerivative hf a (Complex.I • coordinateVector b)
  have hc := fderiv_barDerivative hf b (coordinateVector a)
  have hd := fderiv_barDerivative hf b (Complex.I • coordinateVector a)
  change fderiv ℝ (fun y => (2:ℂ)⁻¹ • (fderiv ℝ f y (coordinateVector a)-
    Complex.I • fderiv ℝ f y (Complex.I • coordinateVector a))) z (coordinateVector b) = _ at ha
  change fderiv ℝ (fun y => (2:ℂ)⁻¹ • (fderiv ℝ f y (coordinateVector a)-
    Complex.I • fderiv ℝ f y (Complex.I • coordinateVector a))) z (Complex.I • coordinateVector b) = _ at hb
  change fderiv ℝ (fun y => (2:ℂ)⁻¹ • (fderiv ℝ f y (coordinateVector b)+
    Complex.I • fderiv ℝ f y (Complex.I • coordinateVector b))) z (coordinateVector a) = _ at hc
  change fderiv ℝ (fun y => (2:ℂ)⁻¹ • (fderiv ℝ f y (coordinateVector b)+
    Complex.I • fderiv ℝ f y (Complex.I • coordinateVector b))) z (Complex.I • coordinateVector a) = _ at hd
  rw [ha,hb,hc,hd]
  have hs (u v : Coordinates d) : fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := by
    exact hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      change ((2:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top) u v
  rw [hs (coordinateVector a) (coordinateVector b),
    hs (coordinateVector a) (Complex.I • coordinateVector b),
    hs (Complex.I • coordinateVector a) (coordinateVector b),
    hs (Complex.I • coordinateVector a) (Complex.I • coordinateVector b)]
  ext i j
  simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul]
  ring

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma secondDerivative_col_symm (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a b i j : Fin d) :
    barDerivative (fun y => holDerivative (g.matrix q) y a) z b i j =
      barDerivative (fun y => holDerivative (g.matrix q) y j) z b i a := by
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have he : (fun y => holDerivative (g.matrix q) y a i j) =ᶠ[nhds z]
      (fun y => holDerivative (g.matrix q) y j i a) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.holDerivative_symm q hy a i j
  rw [← barDeriv_entry ((contDiffAt_holDerivative hs a).differentiableAt (by simp)),
    ← barDeriv_entry ((contDiffAt_holDerivative hs j).differentiableAt (by simp))]
  unfold barDeriv
  rw [he.fderiv_eq]

lemma secondDerivative_row_symm (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a b i j : Fin d) :
    barDerivative (fun y => holDerivative (g.matrix q) y a) z b i j =
      barDerivative (fun y => holDerivative (g.matrix q) y a) z i b j := by
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  rw [bar_hol_comm hs,bar_hol_comm hs]
  have he : (fun y => barDerivative (g.matrix q) y b i j) =ᶠ[nhds z]
      (fun y => barDerivative (g.matrix q) y i b j) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.barDerivative_symm q hy b i j
  rw [← holDeriv_entry ((contDiffAt_barDerivative hs b).differentiableAt (by simp)),
    ← holDeriv_entry ((contDiffAt_barDerivative hs i).differentiableAt (by simp))]
  unfold holDeriv
  rw [he.fderiv_eq]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
