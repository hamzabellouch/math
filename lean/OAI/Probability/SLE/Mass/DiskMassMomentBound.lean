import OAI.Probability.SLE.Gauge.DiskCanonicalMoments
import OAI.Probability.SLE.Geometry.CanonicalDiskPotential

namespace OAI

/-! Uniform moments of the exact quarter-disk terminal mass, retaining
the small centered-target factor before the change of law. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Target

local instance : LocallyCompactSpace (ball (0:ℂ) 1) := isOpen_ball.locallyCompactSpace

lemma exists_diskMass_cutoff :
    ∃ f : C_c((ball (0:ℂ) 1),ℝ), (∀ x, 0≤f x) ∧ (∀ x, f x≤1) ∧
      (∀ x : (ball (0:ℂ) 1), (x:ℂ)∈diskK → 1≤f x) ∧
      (∀ x : (ball (0:ℂ) 1), (x:ℂ)∉closedBall 0 (1/2:ℝ) → f x=0) := by
  let K : Set (ball (0:ℂ) 1) := Subtype.val ⁻¹' diskK
  let V : Set (ball (0:ℂ) 1) := Subtype.val ⁻¹' ball 0 (1/2:ℝ)
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' K = diskK := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,diskK_subset_unit hx⟩,hx,rfl⟩
    rw [he]
    exact isCompact_closedBall _ _
  have hV : IsOpen V := isOpen_ball.preimage continuous_subtype_val
  have hKV : K⊆V := by
    intro x hx
    have hn : ‖(x:ℂ)‖≤(1/4:ℝ) := mem_closedBall_zero_iff.mp hx
    exact mem_ball_zero_iff.mpr (hn.trans_lt (by norm_num))
  obtain ⟨f,hf,hfc,hfs,h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  refine ⟨⟨f,hfc⟩,fun x => (h01 x).1,fun x => (h01 x).2,?_,?_⟩
  · intro x hx
    change 1≤f x
    rw [hf hx]
    rfl
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hx (mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp (hfs hs)).le)

end SLEExactGauge.Target

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma diskTerminalScalar_le_test
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi)
    (f : C_c((ball (0:ℂ) 1),ℝ)) (hf : ∀ x, 0≤f x)
    (hKf : ∀ x : (ball (0:ℂ) 1), (x:ℂ)∈Target.diskK → 1≤f x) (ω : Ω) :
    C.diskTerminalScalar θ hθ ω ≤
      ∫ x, f x ∂conformalMass (Target.diskHomeomorph θ hθ)
        (Target.diskMassWeight κ θ hθ) (C.rational.terminal ω) := by
  let : IsFiniteMeasureOnCompacts (C.rational.terminal ω) := (C.rational.terminal_radon ω).2
  let w := Target.diskMassWeight κ θ hθ
  let g := conformalMassTest (Target.diskHomeomorph θ hθ) w f
  have hK := Target.diskSourceHalfPlane_compact hθ
  rw [conformalMass_integral]
  change (∫ z in Target.diskSourceHalfPlane θ, (w z:ℝ) ∂C.rational.terminal ω) ≤
    ∫ z, g z ∂C.rational.terminal ω
  rw [← integral_indicator hK.measurableSet]
  apply integral_mono ((integrable_indicator_iff hK.measurableSet).mpr
    (compact_weight_integrable w _ hK _)) g.integrable
  intro z
  by_cases hz : z∈Target.diskSourceHalfPlane θ
  · rw [indicator_of_mem hz]
    have hmap : ((Target.diskHomeomorph θ hθ z):ℂ)∈Target.diskK := by
      obtain ⟨x,hx,he⟩ := hz
      have heq := congrArg (Target.diskMap θ) he
      have heq' : x=Target.diskMap θ z := by
        simpa only [Target.diskMap_diskMapInv hθ (Target.diskK_subset_unit hx)] using heq
      change Target.diskMap θ z∈Target.diskK
      rw [← heq']
      exact hx
    change (w z:ℝ)≤(w z:ℝ)*f (Target.diskHomeomorph θ hθ z)
    exact le_mul_of_one_le_right (NNReal.coe_nonneg _) (hKf _ hmap)
  · rw [indicator_of_notMem hz]
    exact mul_nonneg (NNReal.coe_nonneg _) (hf _)

theorem uniform_diskTerminalScalar_centered_moments
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (m : ℕ) :
    ∃ M : ℝ≥0∞, M<∞ ∧ ∀ (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi), ∀ e : ℝ, 0<e → e≤1 →
      (∫⁻ ω in diskCenterHit γ G θ e, ENNReal.ofReal (C.diskTerminalScalar θ hθ ω)^m ∂P) ≤
        M*ENNReal.ofReal (e^codimension κ) := by
  have hKd : closedBall (0:ℂ) (1/2:ℝ)⊆ball 0 1 := closedBall_subset_ball (by norm_num)
  have hbK : ∀ x∈closedBall (0:ℂ) (1/2:ℝ), (1/2:ℝ)≤1-‖x‖^2 := by
    intro x hx
    have hn := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  obtain ⟨M,hM,hbound⟩ := C.uniform_disk_terminal_test_centered_moments hB hc h0 hκ hκ8 F hw
    hgrowth (closedBall 0 (1/2:ℝ)) (isCompact_closedBall _ _) hKd (1/2:ℝ)
    (by norm_num) (by norm_num) hbK m
  obtain ⟨f,hf,hf1,hKf,hfs⟩ := Target.exists_diskMass_cutoff
  refine ⟨M,hM,?_⟩
  intro θ hθ e he he1
  apply (lintegral_mono (fun ω => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (C.diskTerminalScalar_le_test θ hθ f hf hKf ω)) m)).trans
  exact hbound θ hθ f hf hf1 hfs e he he1

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
