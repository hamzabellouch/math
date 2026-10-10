import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.TranslatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedCoreSelection

namespace OAI

section

/-! # Actual selected-kernel velocity tails and large-scale truncation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_velocity_tail {K α γ q a V ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {r s₀ η d₀ : ℝ}, 0 < r → 0 < s₀ → s₀ ≤ 1/8 →
      0 < η → η ≤ Real.log 2 → 0 < d₀ → d₀ ≤ 1 → ∀ (N : ℕ) (z : Published.KineticPhase),
      a ≤ z.1.1 → ‖z.2‖ ≤ V →
      selectedFreeKernel r s₀ η K α γ d₀ q N z {w | R < ‖w‖} ≤ ENNReal.ofReal ε := by
  obtain ⟨R,hR,hb⟩ := JetCoreSheet.rescaled_velocity_tail hK hα hγ hq₁ hq₂ ha hV hε
  refine ⟨R,hR,?_⟩
  intro r s₀ η d₀ hr hs₀ hsmax hη hηmax hd₀ hdmax N z ht hv
  rcases selectedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hz | ⟨i,_,hi⟩
  · rw [hz]
    simp
  · rw [hi,copyFreeKernel_eq_rescaled hr]
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    exact hb hr (div_pos hs hr) (by positivity)
      (JetEnvelopeGain.thermal_width_le hdmax hs.le
        ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax)) ht η i.positive _ _ hv

def retainedScaleRegion (s₀ η r M : ℝ) (N : ℕ) : Set Published.SpaceTime :=
  ⋃ (i : Label) (_h : JetGeometry.jetScale s₀ η i.annulus/r ≤ M), mainCoreRegion s₀ η r N i

theorem measurableSet_retainedScaleRegion (s₀ η r M : ℝ) (N : ℕ) :
    MeasurableSet (retainedScaleRegion s₀ η r M N) := by
  apply MeasurableSet.iUnion
  intro i
  exact MeasurableSet.iUnion (fun _ => measurableSet_mainCoreRegion s₀ η r N i)

def retainedFreeKernel (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((measurableSet_retainedScaleRegion s₀ η r M N).preimage measurable_fst)
    (selectedFreeKernel r s₀ η K α γ d₀ q N) 0

def discardedFreeKernel (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((measurableSet_retainedScaleRegion s₀ η r M N).preimage measurable_fst)
    0 (selectedFreeKernel r s₀ η K α γ d₀ q N)

instance retainedFreeKernel_sFinite (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    IsSFiniteKernel (retainedFreeKernel r s₀ η K α γ d₀ q M N) := by
  unfold retainedFreeKernel
  infer_instance

instance discardedFreeKernel_sFinite (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    IsSFiniteKernel (discardedFreeKernel r s₀ η K α γ d₀ q M N) := by
  unfold discardedFreeKernel
  infer_instance

theorem selectedFreeKernel_decomposition (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    selectedFreeKernel r s₀ η K α γ d₀ q N =
      retainedFreeKernel r s₀ η K α γ d₀ q M N+discardedFreeKernel r s₀ η K α γ d₀ q M N := by
  classical
  ext z E hE
  by_cases hz : z.1 ∈ retainedScaleRegion s₀ η r M N <;>
    simp [retainedFreeKernel,discardedFreeKernel,Kernel.piecewise_apply,hz]

theorem discardedFreeKernel_bound {r s₀ η K α γ d₀ q M : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hM : 0 < M) (N : ℕ) (z : Published.KineticPhase)
    (ht : 0 ≤ z.1.1) :
    discardedFreeKernel r s₀ η K α γ d₀ q M N z univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M) := by
  classical
  by_cases hz : z.1 ∈ retainedScaleRegion s₀ η r M N
  · simp [discardedFreeKernel,Kernel.piecewise_apply,hz]
  simp only [discardedFreeKernel,Kernel.piecewise_apply,mem_preimage,hz,ite_false]
  rcases selectedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with he | ⟨i,hi,he⟩
  · rw [he]
    simp
  rw [he]
  have hscale : M < JetGeometry.jetScale s₀ η i.annulus/r := by
    by_contra h
    apply hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨le_of_not_gt h,hi⟩⟩
  apply (copyFreeKernel_scale_time_bound hr hs₀ hsmax hη.le hK hα hγ hd₀ hdmax hq₁ hq₂ i z ht).trans
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
    (JetCoreSheet.growthConstant_nonneg hK α γ q) hM (by linarith))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Outgoing-velocity decay for the selected positive kernel -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_large_output {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {r s₀ η d₀ : ℝ}, 0 < r → 0 < s₀ → s₀ ≤ 1/8 →
      0 < η → η ≤ Real.log 2 → 0 < d₀ → d₀ ≤ 1 → ∀ (N : ℕ) (z : Published.KineticPhase),
      a ≤ z.1.1 → R < ‖z.2‖ →
      selectedFreeKernel r s₀ η K α γ d₀ q N z univ ≤ ENNReal.ofReal ε := by
  obtain ⟨R,hR,hb⟩ := JetCoreSheet.rescaled_large_output hK hα hγ hq₁ hq₂ ha hε
  refine ⟨R,hR,?_⟩
  intro r s₀ η d₀ hr hs₀ hsmax hη hηmax hd₀ hdmax N z ht hv
  rcases selectedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hz | ⟨i,_,hi⟩
  · rw [hz]
    simp
  · rw [hi,copyFreeKernel_eq_rescaled hr]
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    exact hb hr (div_pos hs hr) (by positivity)
      (JetEnvelopeGain.thermal_width_le hdmax hs.le
        ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax)) ht η i.positive _ _ hv

theorem positive_large_output {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {r s₀ η d₀ : ℝ}, 0 < r → 0 < s₀ → s₀ ≤ 1/8 →
      0 < η → η ≤ Real.log 2 → 0 < d₀ → d₀ ≤ 1 → ∀ (N : ℕ) (z : Published.KineticPhase),
      a ≤ z.1.1 → R < ‖z.2‖ →
      positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤ ENNReal.ofReal ε := by
  obtain ⟨R,hR,hb⟩ := selected_large_output hK hα hγ hq₁ hq₂ ha (half_pos hε)
  refine ⟨R,hR,?_⟩
  intro r s₀ η d₀ hr hs₀ hsmax hη hηmax hd₀ hdmax N z ht hv
  have h := hb hr hs₀ hsmax hη hηmax hd₀ hdmax N z ht hv
  change ((selectedFreeKernel r s₀ η K α γ d₀ q N z)+
    (selectedFreeKernel r s₀ η K α γ d₀ q N z)) univ ≤ _
  rw [Measure.add_apply]
  apply (add_le_add h h).trans_eq
  rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
  congr 1
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
