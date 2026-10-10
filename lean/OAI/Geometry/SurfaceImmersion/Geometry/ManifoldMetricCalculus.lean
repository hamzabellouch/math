import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! Exact metric identities for actual smooth maps on the surface. The
finite-sum identity retains every cross term between distinct chart modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4
section
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev surfaceDifferential (F : M → V) (p : M) : TangentSpace planeModel p →L[ℝ] V :=
  mfderiv planeModel 𝓘(ℝ,V) F p

end
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def inducedForm (F : M → V) (p : M) (v w : TangentSpace planeModel p) : ℝ :=
  inner ℝ (surfaceDifferential F p v) (surfaceDifferential F p w)

def linearMetricForm (F U : M → V) (p : M) (v w : TangentSpace planeModel p) : ℝ :=
  inner ℝ (surfaceDifferential F p v) (surfaceDifferential U p w) +
  inner ℝ (surfaceDifferential U p v) (surfaceDifferential F p w)

lemma surfaceDifferential_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) :
    surfaceDifferential (F+U) p = surfaceDifferential F p + surfaceDifferential U p :=
  mfderiv_add hF hU

lemma inducedForm_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) (v w : TangentSpace planeModel p) :
    inducedForm (F+U) p v w - inducedForm F p v w =
      linearMetricForm F U p v w + inducedForm U p v w := by
  unfold inducedForm linearMetricForm
  rw [surfaceDifferential_add hF hU]
  simp only [add_apply,inner_add_left,inner_add_right]
  ring

lemma mfderiv_finite_sum {ι : Type*} (s : Finset ι) (f : ι → M → V) {p : M}
    (hf : ∀ i ∈ s, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) :
    surfaceDifferential (∑ i ∈ s, f i) p =
      ∑ i ∈ s, surfaceDifferential (f i) p := by
  exact (HasMFDerivAt.sum (fun i hi => (hf i hi).hasMFDerivAt)).mfderiv

lemma inducedForm_finite_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → M → V) {p : M}
    (hf : ∀ i, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p)
    (v w : TangentSpace planeModel p) :
    inducedForm (∑ i, f i) p v w = (∑ i, inducedForm (f i) p v w) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (surfaceDifferential (f i) p v)
          (surfaceDifferential (f j) p w) := by
  unfold inducedForm
  rw [mfderiv_finite_sum Finset.univ f (fun i _ => hf i)]
  simp only [sum_apply]
  rw [sum_inner]
  simp_rw [inner_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (add_comm _ _).trans (Finset.sum_erase_add _ _ (Finset.mem_univ i)) |>.symm

lemma linearMetricForm_finite_sum {ι : Type*} [Fintype ι]
    (F : M → V) (f : ι → M → V) {p : M}
    (hf : ∀ i, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p)
    (v w : TangentSpace planeModel p) :
    linearMetricForm F (∑ i, f i) p v w = ∑ i, linearMetricForm F (f i) p v w := by
  unfold linearMetricForm
  rw [mfderiv_finite_sum Finset.univ f (fun i _ => hf i)]
  simp only [sum_apply,inner_sum,sum_inner,Finset.sum_add_distrib]

lemma inducedForm_free_forced {F U V' : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p)
    (hV : MDifferentiableAt planeModel 𝓘(ℝ,V) V' p)
    (v w : TangentSpace planeModel p) (T : ℝ) :
    inducedForm (F+(U+V')) p v w - inducedForm F p v w - T =
      linearMetricForm F U p v w + linearMetricForm F V' p v w +
      (inducedForm U p v w - T) + linearMetricForm U V' p v w +
      inducedForm V' p v w := by
  unfold inducedForm linearMetricForm
  rw [surfaceDifferential_add hF (hU.add hV), surfaceDifferential_add hU hV]
  simp only [add_apply,inner_add_left,inner_add_right]
  ring

end ClosedSurfaceR4

end

end OAI
