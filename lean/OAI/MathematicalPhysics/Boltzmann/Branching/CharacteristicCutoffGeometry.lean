import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

section

/-! # Transport of collision kernels into characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def transportedKernel (e : X ≃ᵐ Y) (K : Kernel Y Y) : Kernel X X :=
  (K.comap e e.measurable).map e.symm

instance transportedKernel_sFinite (e : X ≃ᵐ Y) (K : Kernel Y Y) [IsSFiniteKernel K] :
    IsSFiniteKernel (transportedKernel e K) := by
  unfold transportedKernel
  infer_instance

theorem transportedKernel_comp (e : X ≃ᵐ Y) (K : Kernel Y Y) (μ : Measure Y) :
    transportedKernel e K ∘ₘ μ.map e.symm = (K ∘ₘ μ).map e.symm := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((transportedKernel e K).measurable_coe hA) e.symm.measurable,
    Measure.map_apply e.symm.measurable hA,
    Measure.bind_apply (e.symm.measurable hA) K.aemeasurable]
  apply lintegral_congr
  intro y
  simp only [transportedKernel,Kernel.map_apply' _ e.symm.measurable _ hA,
    Kernel.comap_apply,MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness

end

end

section

/-! # Relative entropy is invariant under torus characteristics -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem relativeEntropy_eq_lintegral {f : Density} (hf : FiniteEntropyDatum f) :
    ENNReal.ofReal (relativeEntropy f) =
      ∫⁻ p, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  have hi := hf.integrable_relativeEntropy
  have he : (fun p => f p*Real.log (f p/maxwellian p.2)-f p+maxwellian p.2) =
      (fun p => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
    funext p
    exact (scalarRelativeEntropy_eq (maxwellian_pos p.2) (f p)).symm
  change ENNReal.ofReal (∫ p, _) = _
  rw [he]
  exact ofReal_integral_eq_lintegral_ofReal (he ▸ hi)
    (hf.1.mono (fun p hp => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) hp))

theorem TorusFlight.scalar_entropy_lintegral_comp {f : Density} (hfm : Measurable f) (t : ℝ) :
    (∫⁻ p : Phase, ENNReal.ofReal
      (scalarRelativeEntropy (maxwellian p.2) (f (TorusFlight.flight t p)))) =
    ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hm : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
    unfold scalarRelativeEntropy
    exact ((hfm.mul hfm.log).sub (hfm.mul (measurable_const.add hmm.log))).add hmm
  exact (TorusFlight.flight_measurePreserving t).lintegral_comp hm.ennreal_ofReal

end BoltzmannNonuniqueness

end

end

section

/-! # Smooth phase cutoffs around a bounded physical flight cylinder -/

noncomputable section

open Set MeasureTheory Metric

namespace BoltzmannNonuniqueness.EuclideanFlight

def centeredFlightChart (t : ℝ) (x : Velocity) : (Velocity × Velocity) ≃ₜ (Velocity × Velocity) where
  toFun p := (p.1+t • p.2-x,p.2)
  invFun p := (p.1+x-t • p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_characteristic_phase_cutoff (t : ℝ) (x : Velocity) {R : ℝ} (hR : 0 < R) :
    ∃ β : (Velocity × Velocity) → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      (∀ p, 0 ≤ β p) ∧ (∀ p, β p ≤ 1) ∧
      (∀ p, ‖p.1+t • p.2-x‖ ≤ R → ‖p.2‖ ≤ 6 → β p = 1) ∧
      (∀ p ∈ tsupport β, ‖p.1+t • p.2-x‖ ≤ 2*R ∧ ‖p.2‖ ≤ 7) := by
  let bs : ContDiffBump (0 : Velocity) := ⟨R,2*R,hR,by linarith⟩
  let bv : ContDiffBump (0 : Velocity) := ⟨6,7,by norm_num,by norm_num⟩
  let g : (Velocity × Velocity) → ℝ := fun p => bs p.1*bv p.2
  let e := centeredFlightChart t x
  have hsupp : Function.support g ⊆ Metric.closedBall (0 : Velocity) (2*R) ×ˢ
      Metric.closedBall (0 : Velocity) 7 := by
    intro p hp
    have hh : bs p.1 ≠ 0 ∧ bv p.2 ≠ 0 := mul_ne_zero_iff.mp hp
    have hs : p.1 ∈ Metric.ball (0 : Velocity) (2*R) := by
      simpa only [bs.support_eq] using (show p.1 ∈ Function.support bs from hh.1)
    have hv : p.2 ∈ Metric.ball (0 : Velocity) 7 := by
      simpa only [bv.support_eq] using (show p.2 ∈ Function.support bv from hh.2)
    exact ⟨Metric.ball_subset_closedBall hs,Metric.ball_subset_closedBall hv⟩
  have htsupp : tsupport g ⊆ Metric.closedBall (0 : Velocity) (2*R) ×ˢ
      Metric.closedBall (0 : Velocity) 7 :=
    closure_minimal hsupp (isClosed_closedBall.prod isClosed_closedBall)
  have hgc : HasCompactSupport g :=
    ((isCompact_closedBall (0 : Velocity) (2*R)).prod (isCompact_closedBall (0 : Velocity) 7)).of_isClosed_subset
      isClosed_closure htsupp
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    (bs.contDiff.comp contDiff_fst).mul (bv.contDiff.comp contDiff_snd)
  have hes : ContDiff ℝ (⊤ : ℕ∞) (e : (Velocity × Velocity) → (Velocity × Velocity)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : Velocity × Velocity => (p.1+t • p.2-x,p.2))
    fun_prop
  refine ⟨g ∘ e,hgs.comp hes,hgc.comp_homeomorph e,?_,?_,?_,?_⟩
  · intro p
    exact mul_nonneg bs.nonneg bv.nonneg
  · intro p
    exact (mul_le_mul bs.le_one bv.le_one bv.nonneg (by norm_num)).trans (by norm_num)
  · intro p hp hv
    change bs (p.1+t • p.2-x)*bv p.2 = 1
    rw [bs.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp),
      bv.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv),one_mul]
  · intro p hp
    rw [tsupport_comp_eq_preimage g e] at hp
    have hh := htsupp hp
    have hh' : ‖(e p).1‖ ≤ 2*R ∧ ‖(e p).2‖ ≤ 7 := by
      simpa only [mem_prod,Metric.mem_closedBall,dist_zero_right] using hh
    exact hh'

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The phase cutoff remains in a controlled physical cylinder over a short time window -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem phase_displacement_bound {t t₀ Δ R : ℝ} {x : Velocity} {p : Velocity × Velocity}
    (ht : t ∈ Icc t₀ (t₀+Δ)) (hp : ‖p.1+t₀ • p.2-x‖ ≤ R) (hv : ‖p.2‖ ≤ 7) :
    ‖p.1+t • p.2-x‖ ≤ R+7*Δ := by
  have hd : 0 ≤ t-t₀ := sub_nonneg.mpr ht.1
  have he : p.1+t • p.2-x = (p.1+t₀ • p.2-x)+(t-t₀) • p.2 := by module
  rw [he]
  calc
    _ ≤ ‖p.1+t₀ • p.2-x‖+‖(t-t₀) • p.2‖ := norm_add_le _ _
    _ ≤ R+7*Δ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
      have hm := mul_le_mul_of_nonneg_left hv hd
      have hdt : t-t₀ ≤ Δ := by linarith [ht.2]
      nlinarith

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
