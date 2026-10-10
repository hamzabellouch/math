import OAI.Geometry.IsometricImmersion.Darboux.QMetricDensityDecomposition
import OAI.Geometry.IsometricImmersion.Calculus.SmoothMetricJet

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

abbrev QFirstInput := CurvatureFirstInput × DarbouxState

def qFirstDet (a : QFirstInput) : ℝ := (Matrix.of a.1.1).det
def qFirstConnection (a : QFirstInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet (Matrix.of a.1.1) a.1.2 k i j * stateGradient a.2 k
def qFirstXX (a : QFirstInput) : ℝ := a.2 5-qFirstConnection a 0 0
def qFirstMixed (a : QFirstInput) : ℝ := a.2 4-qFirstConnection a 0 1
def qFirstEnergy (a : QFirstInput) : ℝ :=
  qFirstDet a-(a.1.1 1 1*(stateGradient a.2 0)^2-
    (a.1.1 0 1+a.1.1 1 0)*stateGradient a.2 0*stateGradient a.2 1+
      a.1.1 0 0*(stateGradient a.2 1)^2)
def qFirstDensityFactor (a : QFirstInput) : ℝ :=
  qFirstEnergy a/(qFirstDet a*qFirstXX a)
def qFirstLower (a : QFirstInput) : ℝ :=
  qFirstConnection a 1 1+(qFirstMixed a)^2/qFirstXX a

def qFirstBundle (g : MetricField) (w : DarbouxState) : QFirstInput :=
  (actualCurvatureFirstInput g (statePoint w),w)

theorem qFirstDet_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDet (qFirstBundle g w) = (g (statePoint w)).det := rfl
theorem qFirstConnection_bundle (g : MetricField) (w : DarbouxState) (i j : Fin 2) :
    qFirstConnection (qFirstBundle g w) i j = stateConnection g i j w := rfl
theorem qFirstXX_bundle (g : MetricField) (w : DarbouxState) :
    qFirstXX (qFirstBundle g w) = stateQDenominator g w := rfl
theorem qFirstDensityFactor_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDensityFactor (qFirstBundle g w) = qMetricDensityFactor g w := rfl
theorem qFirstLower_bundle (g : MetricField) (w : DarbouxState) :
    qFirstLower (qFirstBundle g w) = qMetricFirstLower g w := rfl

theorem qFirstBundle_distance (g h : MetricField) (w : DarbouxState) :
    ‖qFirstBundle g w-qFirstBundle h w‖ =
      ‖actualCurvatureFirstInput g (statePoint w)-actualCurvatureFirstInput h (statePoint w)‖ := by
  simp [qFirstBundle,Prod.norm_def]

def qFirstBase : Set QFirstInput := {a | qFirstDet a ≠ 0}
def qFirstDomain : Set QFirstInput := {a | qFirstDet a ≠ 0 ∧ qFirstXX a ≠ 0}
def qFirstBaseTube (M d : ℝ) : Set QFirstInput :=
  Metric.closedBall 0 M ∩ qFirstDet ⁻¹' Ici d
def qFirstTube (M d c : ℝ) : Set QFirstInput :=
  qFirstBaseTube M d ∩ qFirstXX ⁻¹' {v : ℝ | c ≤ |v|}

theorem qFirstDet_contDiff : ContDiff ℝ ∞ qFirstDet := by
  unfold qFirstDet
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem qFirstBase_isOpen : IsOpen qFirstBase :=
  isOpen_ne_fun qFirstDet_contDiff.continuous continuous_const

theorem qFirstConnection_contDiffAt {a : QFirstInput} (ha : a ∈ qFirstBase)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun b => qFirstConnection b i j) a := by
  have hΓ (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => christoffelJet (Matrix.of b.1.1) b.1.2 k i j) a :=
    christoffelJet_contDiffAt (G := fun b : QFirstInput => Matrix.of b.1.1)
      (D := fun b : QFirstInput => b.1.2) (fun row column => by
        simp only [Matrix.of_apply]
        fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => stateGradient b.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simpa only [qFirstConnection,Fin.sum_univ_two] using
    ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem qFirstXX_contDiffOn : ContDiffOn ℝ ∞ qFirstXX qFirstBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 5) a by fun_prop).sub
    (qFirstConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem qFirstDomain_isOpen : IsOpen qFirstDomain :=
  qFirstXX_contDiffOn.continuousOn.isOpen_inter_preimage qFirstBase_isOpen
    isClosed_singleton.isOpen_compl

theorem qFirstEnergy_contDiff : ContDiff ℝ ∞ qFirstEnergy := by
  unfold qFirstEnergy
  have hv (k : Fin 2) : ContDiff ℝ ∞ (fun a : QFirstInput => stateGradient a.2 k) :=
    (contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))
  exact qFirstDet_contDiff.sub
    ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 1) by fun_prop).mul
      ((hv 0).pow 2)).sub
      ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 1) by fun_prop).add
        (show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 0) by fun_prop)).mul
          (hv 0)).mul (hv 1))).add
        ((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 0) by fun_prop).mul
          ((hv 1).pow 2)))

theorem qFirstDensityFactor_contDiffOn :
    ContDiffOn ℝ ∞ qFirstDensityFactor qFirstDomain := by
  intro a ha
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  exact (qFirstEnergy_contDiff.contDiffAt.div
    (qFirstDet_contDiff.contDiffAt.mul hx) (mul_ne_zero ha.1 ha.2)).contDiffWithinAt

theorem qFirstLower_contDiffOn : ContDiffOn ℝ ∞ qFirstLower qFirstDomain := by
  intro a ha
  have hΓ := qFirstConnection_contDiffAt ha.1
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  have hm : ContDiffAt ℝ ∞ qFirstMixed a :=
    (show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add ((hm.pow 2).div hx ha.2)).contDiffWithinAt

theorem qFirstBaseTube_isCompact (M d : ℝ) : IsCompact (qFirstBaseTube M d) :=
  (isCompact_closedBall (0 : QFirstInput) M).inter_right
    (isClosed_Ici.preimage qFirstDet_contDiff.continuous)

theorem qFirstBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    qFirstBaseTube M d ⊆ qFirstBase := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

theorem qFirstTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (qFirstTube M d c) := by
  have hbase := qFirstBaseTube_isCompact M d
  have hc : ContinuousOn qFirstXX (qFirstBaseTube M d) :=
    qFirstXX_contDiffOn.continuousOn.mono (qFirstBaseTube_subset_base M hd)
  have hclosed : IsClosed (qFirstTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qFirstTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    qFirstTube M d c ⊆ qFirstDomain := by
  intro a ha
  refine ⟨qFirstBaseTube_subset_base M hd ha.1,?_⟩
  intro hz
  have hh : c ≤ |qFirstXX a| := ha.2
  rw [hz,abs_zero] at hh
  linarith

theorem qFirstXX_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstBaseTube M d, ‖fderiv ℝ qFirstXX a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ qFirstXX) qFirstBase :=
    (qFirstXX_contDiffOn.fderiv_of_isOpen (m := 0) qFirstBase_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstBaseTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (qFirstBaseTube_subset_base M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem qFirstTube_fderiv_bound (f : QFirstInput → ℝ)
    (hf : ContDiffOn ℝ ∞ f qFirstDomain) (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstTube M d c, ‖fderiv ℝ f a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ f) qFirstDomain :=
    (hf.fderiv_of_isOpen (m := 0) qFirstDomain_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstTube_isCompact M hd c).exists_bound_of_continuousOn
    (hcont.mono (qFirstTube_subset_domain M hd hc))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

end SmoothLocal.Pulse

end

end OAI
