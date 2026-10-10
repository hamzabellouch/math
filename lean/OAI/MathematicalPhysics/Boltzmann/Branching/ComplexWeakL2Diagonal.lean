import OAI.MathematicalPhysics.Boltzmann.Collision.FourierL2Identification
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.Topology.Metrizable.Basic

namespace OAI

section

/-! # Weak subsequences in the complex L2 space used by the Fourier proof -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace.CountablyGenerated X] [SFinite μ]

theorem exists_weak_complex_L2_subsequence (u : ℕ → Lp ℂ 2 μ) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℂ 2 μ), StrictMono φ ∧ ‖g‖ ≤ C ∧
      ∀ h : Lp ℂ 2 μ,
        Tendsto (fun n => inner ℂ (u (φ n)) h) atTop (𝓝 (inner ℂ g h)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let v : ℕ → WeakDual ℂ (Lp ℂ 2 μ) := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ) (u n))
  have hv : ∀ n, v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    simpa [v,Metric.mem_closedBall,dist_zero_right] using hu n
  obtain ⟨l,hl,φ,hφ,hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℂ (Lp ℂ 2 μ) 0 C) hv
  let g := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm l.toStrongDual
  refine ⟨φ,g,hφ,?_,?_⟩
  · simpa [g,Metric.mem_closedBall,dist_zero_right] using hl
  · intro h
    have ht := (WeakDual.eval_continuous h).continuousAt.tendsto.comp hconv
    simpa [v,g,InnerProductSpace.toDual_symm_apply,Function.comp_def] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Closed norm bounds pass to weak complex L2 limits -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem complex_weak_norm_le {u : ℕ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 μ,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h))) : ‖g‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hu 0)
  have hb : ‖inner ℂ g g‖ ≤ C*‖g‖ := le_of_tendsto (hw g).norm
    (Eventually.of_forall (fun n => (norm_inner_le_norm (u n) g).trans
      (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg g))))
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg g)] at hb
  nlinarith [norm_nonneg g]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Restricting the complex L2 norm to a physical window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def complexL2Restriction (K : Set FourierSpace) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Lp ℂ 2 (volume.restrict K) :=
  ((Lp.memLp a).restrict K).toLp a

theorem complexL2Restriction_ae (K : Set FourierSpace) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (complexL2Restriction K a : FourierSpace → ℂ) =ᵐ[volume.restrict K] a :=
  MemLp.coeFn_toLp _

theorem complexL2Restriction_sub (K : Set FourierSpace)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    complexL2Restriction K (a-b) = complexL2Restriction K a-complexL2Restriction K b := by
  apply Lp.ext
  filter_upwards [complexL2Restriction_ae K (a-b),
    ae_restrict_of_ae (Lp.coeFn_sub a b),
    Lp.coeFn_sub (complexL2Restriction K a) (complexL2Restriction K b),
    complexL2Restriction_ae K a,complexL2Restriction_ae K b] with x h hsub hright ha hb
  simp only [Pi.sub_apply] at hsub hright
  rw [h,hsub,hright,ha,hb]

theorem complexL2Restriction_norm_le (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖complexL2Restriction K a‖ ≤ ‖a‖ := by
  rw [complexL2Restriction,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp a).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem complexL2Restriction_norm_sq (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖complexL2Restriction K a‖^2 = ∫ x in K, ‖a x‖^2 := by
  rw [L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [complexL2Restriction_ae K a] with x hx
  rw [hx]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A common complex weak subsequence for the countably many Fourier truncations -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace.CountablyGenerated X] [SFinite μ]

theorem exists_common_weak_complex_L2_subsequence (u : ℕ → ℕ → Lp ℂ 2 μ) (C : ℕ → ℝ)
    (hu : ∀ m n, ‖u m n‖ ≤ C m) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℂ 2 μ), StrictMono φ ∧
      ∀ m, ‖g m‖ ≤ C m ∧ ∀ h : Lp ℂ 2 μ,
        Tendsto (fun n => inner ℂ (u m (φ n)) h) atTop (𝓝 (inner ℂ (g m) h)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let K (m : ℕ) : Set (WeakDual ℂ (Lp ℂ 2 μ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C m)
  have hK m : IsCompact (K m) := WeakDual.isCompact_closedBall 0 (C m)
  have : ∀ m, CompactSpace (K m) := fun m => isCompact_iff_compactSpace.mp (hK m)
  have : ∀ m, TopologicalSpace.MetrizableSpace (K m) :=
    fun m => WeakDual.metrizable_of_isCompact ℂ (Lp ℂ 2 μ) (K m) (hK m)
  let v : ℕ → ∀ m, K m := fun n m =>
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ) (u m n)),by
      simpa [K,Metric.mem_closedBall,dist_zero_right] using hu m n⟩
  have hseq : IsSeqCompact (univ : Set (∀ m, K m)) := isCompact_univ.isSeqCompact
  obtain ⟨l,-,φ,hφ,hl⟩ := hseq (fun n => mem_univ (v n))
  let g : ℕ → Lp ℂ 2 μ := fun m =>
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm (l m).val.toStrongDual
  refine ⟨φ,g,hφ,fun m => ⟨?_,fun h => ?_⟩⟩
  · have hnorm : ‖(l m).val.toStrongDual‖ ≤ C m := by
      have hp := (l m).property
      change dist (l m).val.toStrongDual 0 ≤ C m at hp
      simpa only [dist_zero_right] using hp
    simpa only [g,LinearIsometryEquiv.norm_map] using hnorm
  · have ht := ((WeakDual.eval_continuous h).comp
        (continuous_subtype_val.comp (continuous_apply m))).continuousAt.tendsto.comp hl
    simpa [v,g,InnerProductSpace.toDual_symm_apply,Function.comp_def] using ht

end BoltzmannNonuniqueness.Published

end

end

end OAI
