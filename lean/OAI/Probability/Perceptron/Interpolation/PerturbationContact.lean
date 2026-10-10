import Mathlib
import OAI.Probability.Perceptron.Interpolation.PerturbationComparison
import OAI.Probability.Perceptron.Sphere.CoordinateContact
import OAI.Probability.Perceptron.Variational.CompactJointMonomials

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceExpectedPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (u : Fin (n+1) → ℝ) : ℝ :=
  ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)

def sourcePenaltyWeight (N : ℕ) (j : Fin N) : ℝ := (2:ℝ)^(-((j.val+1:ℕ):ℤ))

lemma sourceExpectedPressure_continuousOn (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ContinuousOn (sourceExpectedPressure n k f p d h z t)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) := by
  apply box_comparison_continuous
    (L := fun j => 4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ))
    (fun j => by positivity)
  intro u hu v hv
  apply sourceExpectedPressure_box_comparison n k f p d h hh0 hh z hz hz0 hz1 t
  · exact fun j => ⟨(by linarith [hu.1 j]),hu.2 j⟩
  · exact fun j => ⟨(by linarith [hv.1 j]),hv.2 j⟩

lemma source_perturbation_contact_exists (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∃ u ∈ Icc (fun _ : Fin (n+1) => 1) (fun _ => 2),
      IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
        sourceExpectedPressure n k f p d h z t v)
        (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u :=
  exists_quadratic_box_min _ _ (sourceExpectedPressure_continuousOn n k f p d h hh0 hh z hz hz0 hz1 t)

lemma source_perturbation_contact_coord (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u : Fin (n+1) → ℝ} (hu : u ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f p d h z t v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u) (j : Fin (n+1)) :
    sourcePenaltyWeight (n+1) j*(u j-3/2)^2 ≤ 8*perturbationScale (n+1)^2 := by
  have hc : |sourceExpectedPressure n k f p d h z t u-
      sourceExpectedPressure n k f p d h z t (fun _ => 3/2)| ≤ 8*perturbationScale (n+1)^2 :=
    sourceExpectedPressure_perturbation_comparison n k f p d h hh0 hh z hz hz0 hz1 t
      (fun j => by constructor <;> norm_num)
      (fun j => ⟨by linarith [hu.1 j],hu.2 j⟩)
  exact quadratic_box_min_coord (fun j => by unfold sourcePenaltyWeight; positivity) hmin hc j

lemma source_perturbation_contact_interior (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u : Fin (n+1) → ℝ} (hu : u ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f p d h z t v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u) (j : Fin (n+1))
    (hsmall : 8*perturbationScale (n+1)^2 < sourcePenaltyWeight (n+1) j/16) :
    u j ∈ Ioo (5/4) (7/4) := by
  have hr := source_perturbation_contact_coord n k f p d h hh0 hh z hz hz0 hz1 t hu hmin j
  have hc : 0<sourcePenaltyWeight (n+1) j := by unfold sourcePenaltyWeight; positivity
  have hsq : (u j-3/2)^2 < (1/4:ℝ)^2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (u j-5/4),sq_nonneg (u j-7/4)]

lemma single_coordinate_box {I : Type*} [DecidableEq I]
    {u : I → ℝ} (hu : ∀ i, u i ∈ Icc 1 2) (j : I)
    (hj : u j ∈ Ioo (5/4) (7/4)) {s : ℝ} (hs : |s| ≤ 1/4) :
    ∀ i, (u+Pi.single j s : I → ℝ) i ∈ Icc 1 2 := by
  intro i
  by_cases hi : i=j
  · subst i
    simp only [Pi.add_apply,Pi.single_eq_same]
    exact ⟨by linarith [hj.1,(abs_le.mp hs).1],by linarith [hj.2,(abs_le.mp hs).2]⟩
  · simpa [Pi.single_eq_of_ne hi] using hu i

lemma source_contact_compact_gg_rate (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u : Fin (n+1) → ℝ} (hu : u ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f p d h z t v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u) (j : Fin (n+1))
    {H T : ℝ} (hH : 0 ≤ H) (hhH : h 0 ≤ H) (ht : (t:ℝ) ≤ T)
    (hsmall : 8*perturbationScale (n+1)^2 < sourcePenaltyWeight (n+1) j/16)
    (hs : (n+1:ℕ)^(-(1:ℝ)/4) ≤ (1/4:ℝ))
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    |compactGGDefect (sourceGibbsArrayLaw n k f p d h u z t) r i G (compactJointMonomial (p j) (d j))| ≤
      ‖G‖/(sourcePenaltyWeight (n+1) j)^2 *
        (Real.sqrt (2*sourcePenaltyWeight (n+1) j)*(n+1:ℕ)^(-(3:ℝ)/8)+
          (sourcePenaltyWeight (n+1) j+4*Real.sqrt (enrichedVarianceConstant k z f H T))*
            (n+1:ℕ)^(-(1:ℝ)/8)) := by
  have hj := source_perturbation_contact_interior n k f p d h hh0 hh z hz hz0 hz1 t hu hmin j hsmall
  have hui : ∀ i, u i ∈ Icc 1 2 := fun i => ⟨hu.1 i,hu.2 i⟩
  have hp := single_coordinate_box hui j hj (s := (n+1:ℕ)^(-(1:ℝ)/4))
    (by rwa [abs_of_nonneg (by positivity)])
  have hm := single_coordinate_box hui j hj (s := -((n+1:ℕ)^(-(1:ℝ)/4)))
    (by rwa [abs_neg,abs_of_nonneg (by positivity)])
  have hloc := quadratic_box_min_local_direction hu hmin j
    (show u j ∈ Ioo 1 2 from ⟨by linarith [hj.1],by linarith [hj.2]⟩)
  have hplus := quadratic_box_min_direction hmin j ((n+1:ℕ)^(-(1:ℝ)/4)) ⟨fun i => (hp i).1,fun i => (hp i).2⟩
  have hminus := quadratic_box_min_direction hmin j (-((n+1:ℕ)^(-(1:ℝ)/4))) ⟨fun i => (hm i).1,fun i => (hm i).2⟩
  have hObs : Measurable (fun x : Fin r → NormalizedSpin (n+1) × IndexedLeaf k =>
      G (fun a b => sourceJointOverlap (x a) (x b))) := by
    apply G.continuous.measurable.comp
    apply Measurable.of_eval; intro row; apply Measurable.of_eval; intro column
    exact (sourceJointOverlap_measurable (n+1) k).comp
      (show Measurable (fun replica : Fin r → NormalizedSpin (n+1) × IndexedLeaf k =>
        (replica row,replica column))
        from (measurable_pi_apply row).prodMk (measurable_pi_apply column))
  rw [source_compact_gg_defect n k f p d h hh0 hh u j z t r i G,abs_neg]
  apply source_contact_joint_gg_rate n k f p d h hh0 hh u j z hz hz0 hz1 t hH hhH ht
    (by positivity) hui hp hm hloc hplus hminus r i
    hObs (norm_nonneg _) (fun x => by
      simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm (fun a b => sourceJointOverlap (x a) (x b)))
    (by unfold sourcePenaltyWeight; positivity) rfl

end SphericalPerceptronFreeEnergy
end

end OAI
