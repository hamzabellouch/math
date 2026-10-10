import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.MainPositiveRemainderBound
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedLargeOutput

namespace OAI

section

/-! # Pointwise labels and mass bounds for the retained actual kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem retainedFreeKernel_zero_or_copy {s₀ η r K α γ d₀ q M : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (z : Published.KineticPhase) :
    retainedFreeKernel r s₀ η K α γ d₀ q M N z = 0 ∨
      ∃ i : Label, z.1 ∈ mainCoreRegion s₀ η r N i ∧
        JetGeometry.jetScale s₀ η i.annulus/r ≤ M ∧
        retainedFreeKernel r s₀ η K α γ d₀ q M N z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  classical
  by_cases hz : z.1 ∈ retainedScaleRegion s₀ η r M N
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨hscale,hi⟩ := mem_iUnion.mp hi
    refine Or.inr ⟨i,hi,hscale,?_⟩
    simp only [retainedFreeKernel,Kernel.piecewise_apply,mem_preimage,hz,ite_true]
    exact selectedFreeKernel_eq_copy hs₀ hsmax hη hηmax hi
  · exact Or.inl (by simp [retainedFreeKernel,Kernel.piecewise_apply,hz])

theorem retainedFreeKernel_le (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) (z : Published.KineticPhase) :
    retainedFreeKernel r s₀ η K α γ d₀ q M N z ≤ selectedFreeKernel r s₀ η K α γ d₀ q N z := by
  classical
  by_cases hz : z.1 ∈ retainedScaleRegion s₀ η r M N
  · simp [retainedFreeKernel,Kernel.piecewise_apply,hz]
  · simp only [retainedFreeKernel,Kernel.piecewise_apply,mem_preimage,hz,ite_false]
    exact bot_le

theorem retainedFreeKernel_bound {r s₀ η K α γ d₀ q M : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : Published.KineticPhase) (ht : 0 < z.1.1) :
    retainedFreeKernel r s₀ η K α γ d₀ q M N z univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/z.1.1) :=
  (retainedFreeKernel_le _ _ _ _ _ _ _ _ _ _ z univ).trans
    (selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N z ht)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Near-axis input deletion for retained actual selected kernels -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] retainedFreeKernel selectedFreeKernel

theorem retained_small_input {K α γ q a b ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ ∀ {r s₀ η d₀ M : ℝ},
      0 < r → 0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < d₀ → d₀ ≤ 1 → d₀*(r*M)^10 ≤ θ →
      ∀ (N : ℕ) (z : Published.KineticPhase), a ≤ z.1.1 → b ≤ ‖transverse z.2‖ →
      retainedFreeKernel r s₀ η K α γ d₀ q M N z
        {w | ‖transverse w‖ < δ} ≤ ENNReal.ofReal ε := by
  obtain ⟨δ,θ,hδ,hθ,hsmall⟩ := JetCoreSheet.rescaled_small_input hK hα hγ hq₁ hq₂ ha hb hε
  refine ⟨δ,θ,hδ,hθ,?_⟩
  intro r s₀ η d₀ M hr hs₀ hsmax hη hηmax hd₀ hdmax hthin N z ht hv
  rcases retainedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hz | ⟨i,_,hscale,hi⟩
  · rw [hz]
    simp
  rw [hi,copyFreeKernel_eq_rescaled hr]
  have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
  exact hsmall hr (div_pos hs hr) (by positivity)
    (JetEnvelopeGain.thermal_width_le hdmax hs.le
      ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax))
    ((GeometricMesh.retained_thermal_width_le hr hd₀.le hs₀ hscale).trans hthin)
    ht η i.positive _ _ hv

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Small second retained gain outside the actual exceptional-speed list -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem retained_second_small_off_bands {K α γ q a δ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ {r s₀ η d₀ M L T t₁ t₂ : ℝ} {N : ℕ},
      0 < r → 0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < d₀ → d₀ ≤ 1 → d₀*(r*M)^10 ≤ min δ b/4 → r*T*L < 1/4 →
      a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T →
      ∀ (i : Label) (x w : Velocity) (S : Finset ℝ),
      (t₁,x) ∈ mainCoreRegion s₀ η r N i → ‖w‖ ≤ L → ‖transverse w‖ ≤ ρ →
      (∀ j < N, μ₀ ≤ JetGeometry.jetScale s₀ η j/r →
        JetGeometry.jetScale s₀ η j/r ≤ M → JetGeometry.jetScale s₀ η j/r ∈ S) →
      axial w ∉ bands (collapsedCenters α t₁ (axial (x-r⁻¹ • latticeVector i.lattice))) δ →
      axial w ∉ bands (profileCenters α γ t₁ (axial (x-r⁻¹ • latticeVector i.lattice)) S) b →
      retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ ≤
        ENNReal.ofReal ε := by
  obtain ⟨μ₀,hμ₀,hsecond⟩ := JetCoreSheet.rescaled_second_core_small_off_bands
    hα hγ hq₁ hq₂ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro b hb ε hε
  let A := JetCoreSheet.slabAmplitude K α γ a
  have hA : 0 ≤ A := JetCoreSheet.slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨ρ,hρ,hgood⟩ := hsecond b hb (ε/(A+1)) he
  refine ⟨ρ,hρ,?_⟩
  intro r s₀ η d₀ M L T t₁ t₂ N hr hs₀ hsmax hη hηmax hd₀ hdmax hwidth hnear
    ht₂ htt ht₁ i x w S hi hw htrans hmesh hcollapsed hprofile
  rcases retainedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax ((t₂,x-(t₁-t₂) • w),w)
    with hz | ⟨j,hj,hjM,hjK⟩
  · rw [hz]
    simp
  rw [hjK,copyFreeKernel_eq_rescaled hr]
  have hlat : j.lattice = i.lattice :=
    (main_collision_same_origin hs₀ hsmax hη hr.le (ha.le.trans ht₂) htt ht₁ hnear hw hi hj).symm
  rw [hlat]
  have hs : 0 < JetGeometry.jetScale s₀ η j.annulus/r :=
    div_pos (DatumBounds.scale_pos hs₀ _) hr
  have hd : 0 < d₀*JetGeometry.jetScale s₀ η j.annulus^10 := by
    have := DatumBounds.scale_pos (η := η) hs₀ (j.annulus+1)
    positivity
  have hsmall : d₀*JetGeometry.jetScale s₀ η j.annulus^10 ≤ min δ b/4 :=
    (GeometricMesh.retained_thermal_width_le hr hd₀.le hs₀ hjM).trans hwidth
  have hmax : d₀*JetGeometry.jetScale s₀ η j.annulus^10 ≤ 1/16 :=
    JetEnvelopeGain.thermal_width_le hdmax (DatumBounds.scale_pos hs₀ _).le
      ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax)
  have hpos : JetPeriodicDatum.spatialMap (x-(t₁-t₂) • w-r⁻¹ • latticeVector i.lattice) =
      (transverse (x-(t₁-t₂) • w-r⁻¹ • latticeVector i.lattice),
        axial (x-r⁻¹ • latticeVector i.lattice)-(t₁-t₂)*axial w) := by
    apply Prod.ext
    · rfl
    · exact axial_flight_translation _ _ _ _
  rw [hpos]
  apply (hgood hr hK hs hd hmax hsmall ht₂ htt η j.positive
    (transverse (x-(t₁-t₂) • w-r⁻¹ • latticeVector i.lattice)) w S
    (fun hμ => hmesh _ hj.1 hμ hjM) htrans hcollapsed hprofile).trans
  rw [← ENNReal.ofReal_mul
    (JetCoreSheet.amplitude_nonneg hK hs (ha.le.trans ht₂) α γ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
      ((JetCoreSheet.amplitude_le_slab hK ha hs ht₂ α γ).trans
        (by change A ≤ A+1; linarith)) he.le
    _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Three-region bound for the actual selected/retained pair of gains -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel JetCoreSheet.rescaledCoreMeasure

theorem selected_retained_pair_small {K α γ q a s₀ η d₀ M V ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ L d ρ : ℝ, 0 < L ∧ 0 < d ∧ 0 < ρ ∧ ∀ {r T t₁ t₂ : ℝ} {N : ℕ},
      0 < r → d₀*(r*M)^10 ≤ d → r*T*L < 1/4 → a ≤ t₂ → t₂ ≤ t₁ → t₁ ≤ T →
      ∀ (x v : Velocity), ‖v‖ ≤ V → ‖transverse v‖ ≤ ρ →
      (∫⁻ w, retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ
        ∂selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)) ≤
        ENNReal.ofReal (3*(JetCoreSheet.growthConstant K α γ q/a)*ε) := by
  have he : 0 < ε/3 := div_pos hε (by norm_num)
  obtain ⟨δ,hδ,hcollapsed⟩ := JetCoreSheet.rescaled_bands_small_of_card
    hK hα hγ hq₁ hq₂ ha he 5
  obtain ⟨μ,hμ,hsecond⟩ := retained_second_small_off_bands hK hα hγ hq₁ hq₂ ha hδ
  let J := (Finset.Icc (GeometricMesh.index (μ/Real.exp η) η) (GeometricMesh.index M η)).card
  obtain ⟨b,hb,hprofile⟩ := JetCoreSheet.rescaled_bands_small_of_card
    hK hα hγ hq₁ hq₂ ha he (2*J)
  obtain ⟨θ,hθ,hgood⟩ := hsecond b hb ε hε
  obtain ⟨ρ,hρ,haway⟩ := JetCoreSheet.rescaled_away_small_of_transverse
    hK hα hγ hq₁ hq₂ ha hθ hε
  obtain ⟨L,hL,htail⟩ := selected_velocity_tail hK hα hγ hq₁ hq₂ ha hV he
  refine ⟨L,min δ b/4,ρ,hL,div_pos (lt_min hδ hb) (by norm_num),hρ,?_⟩
  intro r T t₁ t₂ N hr hd hnear ht₂ htt ht₁ x v hv htrans
  let κ : Measure Velocity := selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)
  let f : Velocity → ℝ≥0∞ := fun w =>
    retainedFreeKernel r s₀ η K α γ d₀ q M N ((t₂,x-(t₁-t₂) • w),w) univ
  let C := JetCoreSheet.growthConstant K α γ q/a
  have hC : 0 ≤ C := div_nonneg (JetCoreSheet.growthConstant_nonneg hK α γ q) ha.le
  rcases selectedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax ((t₁,x),v) with hz | ⟨i,hi,hiK⟩
  · rw [hz]
    simp
  obtain ⟨S,hS,hmem⟩ := GeometricMesh.exists_retained_scale_list hs₀ hη hr hμ N
  let X := JetPeriodicDatum.spatialMap (x-r⁻¹ • latticeVector i.lattice)
  let E₁ := axial ⁻¹' bands (collapsedCenters α t₁ X.2) δ
  let E₂ := axial ⁻¹' bands (profileCenters α γ t₁ X.2 S) b
  let U := {w : Velocity | L < ‖w‖}
  let E := (E₁ ∪ E₂) ∪ U
  let F := {w : Velocity | θ ≤ ‖transverse w‖}
  have hE₁ : MeasurableSet E₁ := (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  have hE₂ : MeasurableSet E₂ := (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_norm
  have hF : MeasurableSet F := measurableSet_le measurable_const ChartKernel.measurable_transverse.norm
  have hfirst : κ = JetCoreSheet.rescaledCoreMeasure r η K α γ
      (JetGeometry.jetScale s₀ η i.annulus/r) (d₀*JetGeometry.jetScale s₀ η i.annulus^10)
      q i.positive t₁ X v := hiK.trans (copyFreeKernel_eq_rescaled hr _ _ _ _ _ _ _ _ _)
  have his : 0 < JetGeometry.jetScale s₀ η i.annulus/r := div_pos (DatumBounds.scale_pos hs₀ _) hr
  have hid : 0 < d₀*JetGeometry.jetScale s₀ η i.annulus^10 := by
    have := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
    positivity
  have hidmax : d₀*JetGeometry.jetScale s₀ η i.annulus^10 ≤ 1/16 :=
    JetEnvelopeGain.thermal_width_le hdmax (DatumBounds.scale_pos hs₀ _).le
      ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax)
  have he₁ : κ E₁ ≤ ENNReal.ofReal (ε/3) := by
    rw [hfirst]
    exact hcollapsed hr his hid hidmax (ht₂.trans htt) η i.positive X v _
      (collapsedCenters_card_le _ _ _)
  have he₂ : κ E₂ ≤ ENNReal.ofReal (ε/3) := by
    rw [hfirst]
    exact hprofile hr his hid hidmax (ht₂.trans htt) η i.positive X v _
      ((profileCenters_card_le _ _ _ _ _).trans (Nat.mul_le_mul_left 2 hS))
  have hu : κ U ≤ ENNReal.ofReal (ε/3) :=
    htail hr hs₀ hsmax hη hηmax hd₀ hdmax N ((t₁,x),v) (ht₂.trans htt) hv
  have heall : κ E ≤ ENNReal.ofReal ε := by
    calc
      _ ≤ κ (E₁ ∪ E₂)+κ U := measure_union_le (μ := κ) (E₁ ∪ E₂) U
      _ ≤ (κ E₁+κ E₂)+κ U := add_le_add (measure_union_le (μ := κ) E₁ E₂) le_rfl
      _ ≤ (ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3))+ENNReal.ofReal (ε/3) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_add he.le he.le,
          ← ENNReal.ofReal_add (add_nonneg he.le he.le) he.le]
        congr 1
        ring
  have hfall : κ F ≤ ENNReal.ofReal ε := by
    rw [hfirst]
    exact haway hr his hid hidmax (ht₂.trans htt) η i.positive X v htrans
  have hfb (w : Velocity) : f w ≤ ENNReal.ofReal C := by
    apply (retainedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N
      ((t₂,x-(t₁-t₂) • w),w) (ha.trans_le ht₂)).trans
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (JetCoreSheet.growthConstant_nonneg hK α γ q) ha ht₂)
  have hmass : κ univ ≤ ENNReal.ofReal C := by
    apply (selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N
      ((t₁,x),v) (ha.trans_le (ht₂.trans htt))).trans
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (JetCoreSheet.growthConstant_nonneg hK α γ q) ha (ht₂.trans htt))
  have hg (w : Velocity) (hwE : w ∉ E) (hwF : w ∉ F) : f w ≤ ENNReal.ofReal ε := by
    apply hgood hr hs₀ hsmax hη hηmax hd₀ hdmax hd hnear ht₂ htt ht₁ i x w S hi
      (le_of_not_gt (fun h => hwE (Or.inr h))) (le_of_not_ge hwF) hmem
    · exact fun h => hwE (Or.inl (Or.inl h))
    · exact fun h => hwE (Or.inl (Or.inr h))
  change (∫⁻ w, f w ∂κ) ≤ _
  calc
    _ ≤ ENNReal.ofReal C*κ E+ENNReal.ofReal C*κ F+ENNReal.ofReal ε*κ univ :=
      GainPullback.integral_three_regions_le κ ((hE₁.union hE₂).union hU) hF hfb hg
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal ε+ENNReal.ofReal C*ENNReal.ofReal ε+
        ENNReal.ofReal ε*ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (3*C*ε) := by
      rw [← ENNReal.ofReal_mul hC,← ENNReal.ofReal_mul hε.le,
        ← ENNReal.ofReal_add (mul_nonneg hC hε.le) (mul_nonneg hC hε.le),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hC hε.le) (mul_nonneg hC hε.le))
          (mul_nonneg hε.le hC)]
      congr 1
      ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Vanishing of the actual selected/retained pair at axial endpoints -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_retained_pair_tendsto {K α γ q a s₀ η d₀ M V T : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
    (r t₁ t₂ : ℕ → ℝ) (N : ℕ → ℕ) (x v : ℕ → Velocity)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n) (ht₁ : ∀ n, t₁ n ≤ T)
    (hv : ∀ n, ‖v n‖ ≤ V)
    (htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ w,
      retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n)
        ((t₂ n,x n-(t₁ n-t₂ n) • w),w) univ
      ∂selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) ((t₁ n,x n),v n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  let C := 3*(JetCoreSheet.growthConstant K α γ q/a)
  have hC : 0 ≤ C := by
    have := JetCoreSheet.growthConstant_nonneg hK α γ q
    dsimp [C]
    positivity
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (show ENNReal.ofReal C ≠ ∞ from ENNReal.ofReal_ne_top) hε.ne'
  have he' : (0 : ℝ) < e := he
  obtain ⟨L,d,ρ,hL,hd,hρ,hsmall⟩ := selected_retained_pair_small
    hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax hd₀ hdmax hV he' (M := M)
  have hD := GeometricMesh.retained_thermal_width_tendsto d₀ M hrlim
  have hflight : Tendsto (fun n => r n*T*L) atTop (𝓝 0) := by
    simpa using (hrlim.mul_const T).mul_const L
  filter_upwards [hD.eventually (gt_mem_nhds hd),
    hflight.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)),
    htrans.eventually (gt_mem_nhds hρ)] with n hnD hnF hnV
  apply (hsmall (hr n) hnD.le hnF (ht₂ n) (htt n) (ht₁ n) (x n) (v n) (hv n) hnV.le).trans
  have heq : ENNReal.ofReal (C*(e : ℝ)) = (e : ℝ≥0∞)*ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul hC,ENNReal.ofReal_coe_nnreal,mul_comm]
  exact heq.le.trans heε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform axial decay of the retained selected core in periodic coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem retained_axial_decay {r s₀ η K α γ d₀ q M Z T : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hZ : 0 < Z) (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : Published.KineticPhase)
    (ht : z.1.1 ∈ Icc 0 T)
    (hx : ∀ k : Lattice, Z+T*(α+2) ≤ |axial (z.1.2-r⁻¹ • latticeVector k)|) :
    retainedFreeKernel r s₀ η K α γ d₀ q M N z univ ≤
      ENNReal.ofReal ((4*K*M/(γ^2*Z^2))*JetGaussianProduct.coefficient)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2)) := by
  rcases retainedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hz | ⟨i,_,hi,he⟩
  · rw [hz]
    simp
  · rw [he,copyFreeKernel_eq_rescaled hr]
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    exact JetCoreSheet.rescaled_axial_decay hr hK hα.le hγ (div_pos hs hr) (by positivity)
      (JetEnvelopeGain.thermal_width_le hdmax hs.le
        ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax))
      ht.1 ht.2 hi hZ hq₁ hq₂ η i.positive _ (hx i.lattice) z.2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
