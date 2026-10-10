import OAI.Probability.InvariantIsing.Magnetic.MagneticImplicitBias
import OAI.Probability.InvariantIsing.Fields.FieldHeightLocal

namespace OAI

/-! Identification of the joint finite-height derivatives with the actual
physical mean and curvature at every bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Classical
open scoped Topology

namespace InvariantIsing

lemma fieldFiniteFamily_mean_at_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) :
    F.X (r, b) = fieldBiasMean (fieldStepOfStrictHeights h r hs) b := by
  have hd := (F.spatial_derivative r hr b).sub_const (r (Fin.last h.depth) / 2)
  have he : (fun z => F.U (r, z) - r (Fin.last h.depth) / 2) =
      fieldValue (fieldStepOfStrictHeights h r hs) := by
    funext z
    rw [hU]
    exact fieldHeightJointValue_strict h r hs z
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldValue_bias (fieldStepOfStrictHeights h r hs) b)

lemma fieldFiniteFamily_curvature_at_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) :
    F.XX (r, b) = fieldBiasCurvature (fieldStepOfStrictHeights h r hs) b := by
  have hd := F.spatial_mean_derivative r hr b
  have he : (fun z => F.X (r, z)) = fieldBiasMean (fieldStepOfStrictHeights h r hs) := by
    funext z
    exact fieldFiniteFamily_mean_at_bias h F hU r hr hs z
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldBiasMean (fieldStepOfStrictHeights h r hs) b)

lemma fieldFiniteFamily_curvature_pos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) : 0 < F.XX (r, b) := by
  rw [fieldFiniteFamily_curvature_at_bias h F hU r hr hs]
  exact fieldBiasCurvature_pos _ _

/-- The unique interior minimizing bias for the actual literal height vector. -/
def magneticHeightBias (h : FieldStep) (s : ℝ) (r : Fin (h.depth + 1) → ℝ) : ℝ :=
  if hr : r ∈ fieldStrictHeightCone h.depth then
    magneticBias (fieldStepOfStrictHeights h r hr) s else 0

lemma magneticHeightBias_eq (h : FieldStep) (s : ℝ) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) :
    magneticHeightBias h s r = magneticBias (fieldStepOfStrictHeights h r hr) s := by
  simp only [magneticHeightBias, dite_eq_left hr]

lemma fieldFiniteFamily_magneticHeightBias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) {s : ℝ} (hs : |s| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    F.X (r, magneticHeightBias h s r) = s := by
  rw [fieldFiniteFamily_mean_at_bias h F hU r hr hrs, magneticHeightBias_eq h s r hrs]
  exact fieldBiasMean_magneticBias _ hs

lemma continuousAt_magneticHeightBias_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    ContinuousAt (fun t : ℝ => magneticHeightBias h s (r + t • d)) 0 := by
  let A := fun p : ℝ × ℝ => F.X (r + p.1 • d, p.2)
  have hpath : Continuous (fun t : ℝ => r + t • d) := by fun_prop
  have hN : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    exact hpath.continuousAt.eventually
      ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds (by simpa using And.intro hr hrs))
  apply parametric_bias_continuousAt (A := A)
  · intro z
    have hc : ContinuousAt F.X (r + (0 : ℝ) • d, z) := by
      simpa only [zero_smul, add_zero] using (F.derivativeX (r, z) hr).continuousAt
    have hp : ContinuousAt (fun t : ℝ => (r + t • d, z)) 0 := by fun_prop
    simpa only [A, zero_smul, add_zero, Function.comp_def] using
      (hc.comp (f := fun t : ℝ => (r + t • d, z)) hp)
  · filter_upwards [hN] with t ht
    have he : (fun z => A (t, z)) =
        fieldBiasMean (fieldStepOfStrictHeights h (r + t • d) ht.2) := by
      funext z
      exact fieldFiniteFamily_mean_at_bias h F hU _ ht.1 ht.2 z
    rw [he]
    exact strictMono_fieldBiasMean _
  · filter_upwards [hN] with t ht
    exact fieldFiniteFamily_magneticHeightBias h F hU hs _ ht.1 ht.2

end InvariantIsing

end

end OAI
