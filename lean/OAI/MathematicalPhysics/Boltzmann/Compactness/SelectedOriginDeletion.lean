import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveRestrictedChain
import OAI.MathematicalPhysics.Boltzmann.Branching.RetainedAxialDecay
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialDecayLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedLargeOutput
import OAI.MathematicalPhysics.Boltzmann.Jets.OriginMeshLimit

namespace OAI

section

/-! # Uniform first-gain decay along axially escaping bounded-speed flights -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_axial_escape_small {K α γ q a T V s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 ≤ a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
    (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
      R ≤ |axial ((z n).1.2-(r n)⁻¹ • latticeVector k)|)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc a (z n).1.1,
      selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s) univ ≤ ENNReal.ofReal ε := by
  let G := JetCoreSheet.growthConstant K α γ q
  let M := (G+1)/(ε/2)
  have hG : 0 ≤ G := JetCoreSheet.growthConstant_nonneg hK α γ q
  have hM : 0 < M := div_pos (by linarith) (half_pos hε)
  have hGM : G/M ≤ ε/2 := by
    apply (div_le_iff₀ hM).mpr
    have he : (ε/2)*M = G+1 := by dsimp [M]; field_simp
    linarith
  have hsmall := ENNReal.tendsto_nhds_zero.mp (axial_decay_bound_tendsto K γ M α q)
    (ENNReal.ofReal (ε/2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨j,hj⟩ := hsmall.exists
  let Z : ℝ := (j:ℝ)+1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hT : 0 ≤ T := ha.trans (ht 0).1 |>.trans (ht 0).2
  filter_upwards [hx (Z+T*(α+2)+T*V)] with n hn
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨ha.trans hs.1,hs.2.trans (ht n).2⟩
  have hflight (k : Lattice) : Z+T*(α+2) ≤
      |axial ((flight (z n) s).1.2-(r n)⁻¹ • latticeVector k)| := by
    have hlen : 0 ≤ (z n).1.1-s := sub_nonneg.mpr hs.2
    have hlenT : (z n).1.1-s ≤ T := by linarith [hsT.1,(ht n).2]
    have hv' : |axial (z n).2| ≤ V := (SmallInputGeometry.abs_axial_le_norm _).trans (hv n)
    have hp : |((z n).1.1-s)*axial (z n).2| ≤ T*V := by
      rw [abs_mul,abs_of_nonneg hlen]
      exact mul_le_mul hlenT hv' (abs_nonneg _) hT
    change Z+T*(α+2) ≤ |axial ((z n).1.2-((z n).1.1-s) • (z n).2-(r n)⁻¹ • latticeVector k)|
    rw [axial_flight_translation]
    linarith [hn k,abs_sub_abs_le_abs_sub
      (axial ((z n).1.2-(r n)⁻¹ • latticeVector k)) (((z n).1.1-s)*axial (z n).2)]
  have hret := retained_axial_decay (M := M) (Z := Z) (hr n) hs₀ hsmax hη hηmax
    hK hα hγ hd₀ hdmax hZ hq₁ hq₂ (N n) (flight (z n) s) hsT hflight
  have hdisc := discardedFreeKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ hM (N n) (flight (z n) s) hsT.1
  rw [selectedFreeKernel_decomposition (r n) s₀ η K α γ d₀ q M (N n)]
  change retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n) (flight (z n) s) univ+
      discardedFreeKernel (r n) s₀ η K α γ d₀ q M (N n) (flight (z n) s) univ ≤ _
  apply (add_le_add (hret.trans hj) (hdisc.trans (ENNReal.ofReal_le_ofReal hGM))).trans_eq
  rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
  congr 1
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform near-axis deletion for the full selected kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel discardedFreeKernel

theorem selected_small_input_bound {K α γ q a b ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ ∀ {r s₀ η d₀ M : ℝ},
      0 < r → 0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < d₀ → d₀ ≤ 1 → 0 < M → d₀*(r*M)^10 ≤ θ →
      ∀ (N : ℕ) (z : Published.KineticPhase), a ≤ z.1.1 → b ≤ ‖transverse z.2‖ →
      selectedFreeKernel r s₀ η K α γ d₀ q N z {w | ‖transverse w‖ < δ} ≤
        ENNReal.ofReal ε+ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M) := by
  obtain ⟨δ,θ,hδ,hθ,hsmall⟩ := retained_small_input hK hα hγ hq₁ hq₂ ha hb hε
  refine ⟨δ,θ,hδ,hθ,?_⟩
  intro r s₀ η d₀ M hr hs₀ hsmax hη hηmax hd₀ hdmax hM hthin N z ht hv
  have he := congrArg (fun κ : Kernel Published.KineticPhase Velocity =>
    κ z {w | ‖transverse w‖ < δ}) (selectedFreeKernel_decomposition r s₀ η K α γ d₀ q M N)
  change selectedFreeKernel r s₀ η K α γ d₀ q N z {w | ‖transverse w‖ < δ} =
    retainedFreeKernel r s₀ η K α γ d₀ q M N z {w | ‖transverse w‖ < δ}+
      discardedFreeKernel r s₀ η K α γ d₀ q M N z {w | ‖transverse w‖ < δ} at he
  rw [he]
  apply add_le_add (hsmall hr hs₀ hsmax hη hηmax hd₀ hdmax hthin N z ht hv)
  exact (measure_mono (subset_univ _)).trans
    (discardedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ hM N z
      (ha.le.trans ht))

theorem selected_small_input_eventually {K α γ q a b ε s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (z : Published.KineticPhase),
      a ≤ z.1.1 → b ≤ ‖transverse z.2‖ →
      selectedFreeKernel (r n) s₀ η K α γ d₀ q N z {w | ‖transverse w‖ < δ} ≤
        ENNReal.ofReal ε := by
  let G := JetCoreSheet.growthConstant K α γ q
  have hG : 0 ≤ G := JetCoreSheet.growthConstant_nonneg hK α γ q
  let M := 2*(G+1)/ε
  have hM : 0 < M := by dsimp [M]; positivity
  have herr : G/M ≤ ε/2 := by
    apply (div_le_iff₀ hM).mpr
    dsimp [M]
    field_simp
    linarith
  obtain ⟨δ,θ,hδ,hθ,hsmall⟩ := selected_small_input_bound hK hα hγ hq₁ hq₂ ha hb
    (half_pos hε)
  refine ⟨δ,hδ,?_⟩
  have hthin := (GeometricMesh.retained_thermal_width_tendsto d₀ M hrlim).eventually
    (gt_mem_nhds hθ)
  filter_upwards [hthin] with n hn N z ht hv
  apply (hsmall (hr n) hs₀ hsmax hη hηmax hd₀ hdmax hM hn.le N z ht hv).trans
  apply (add_le_add le_rfl (ENNReal.ofReal_le_ofReal herr)).trans_eq
  rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
  congr 1
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Fixed products for selected physical collision words -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev CollisionWord : ℕ → Type
  | 0 => PUnit
  | n+1 => EventParameter × CollisionWord n

abbrev collisionWordMeasurable : (n : ℕ) → MeasurableSpace (CollisionWord n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := collisionWordMeasurable n
    exact inferInstanceAs (MeasurableSpace (EventParameter × CollisionWord n))

attribute [instance] collisionWordMeasurable

def collisionWordMeasure : (n : ℕ) → Measure (CollisionWord n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => physicalEventMeasure.prod (collisionWordMeasure n)

instance collisionWordMeasure_sFinite (n : ℕ) : SFinite (collisionWordMeasure n) := by
  induction n with
  | zero => change SFinite (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    let := ih
    change SFinite (physicalEventMeasure.prod (collisionWordMeasure n))
    infer_instance

def selectedWordState (b : BeamCoefficients) (endTime : ℝ) :
    (ms : List HistoryMark) → PhysicalFlightState → CollisionWord ms.length → PhysicalFlightState
  | [],p,_ => p
  | m::ms,p,a => selectedWordState b endTime ms (mediumParameterState b endTime p (m,a.1)) a.2

def selectedWordDensity (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    (ms : List HistoryMark) → PhysicalFlightState → CollisionWord ms.length → ℝ≥0∞
  | [],_,_ => 1
  | m::ms,p,a => physicalParameterWeight b endTime C m p a.1 *
      selectedWordDensity b endTime C ms (mediumParameterState b endTime p (m,a.1)) a.2

theorem selectedWordState_measurable (b : BeamCoefficients) (endTime : ℝ)
    (ms : List HistoryMark) : Measurable (fun q : PhysicalFlightState × CollisionWord ms.length =>
      selectedWordState b endTime ms q.1 q.2) := by
  induction ms with
  | nil => exact measurable_fst
  | cons m ms ih =>
    have hs : Measurable (fun q : PhysicalFlightState × CollisionWord (m::ms).length =>
        (mediumParameterState b endTime q.1 (m,q.2.1),q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))).prodMk
          measurable_snd.snd
    exact ih.comp hs

theorem selectedWordDensity_measurable (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) : Measurable (fun q : PhysicalFlightState × CollisionWord ms.length =>
      selectedWordDensity b endTime C ms q.1 q.2) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    have hs : Measurable (fun q : PhysicalFlightState × CollisionWord (m::ms).length =>
        (mediumParameterState b endTime q.1 (m,q.2.1),q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))).prodMk
          measurable_snd.snd
    exact ((physicalParameterWeight_measurable b endTime C m).comp
      (measurable_fst.prodMk measurable_snd.fst)).mul (ih.comp hs)

theorem selectedWord_integral (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a, selectedWordDensity b endTime C ms p a * F (selectedWordState b endTime ms p a)
      ∂collisionWordMeasure ms.length) = ∫⁻ q, F q ∂physicalMarkedWord b endTime C ms p := by
  induction ms generalizing p with
  | nil =>
    change (∫⁻ _ : PUnit, 1 * F p ∂Measure.dirac PUnit.unit) = ∫⁻ q, F q ∂Kernel.id p
    simp [Kernel.id_apply]
  | cons m ms ih =>
    have hm : Measurable (fun a : CollisionWord (m::ms).length =>
        selectedWordDensity b endTime C (m::ms) p a *
          F (selectedWordState b endTime (m::ms) p a)) :=
      ((selectedWordDensity_measurable b endTime C (m::ms)).comp
        (measurable_const.prodMk measurable_id)).mul
      (hF.comp ((selectedWordState_measurable b endTime (m::ms)).comp
        (measurable_const.prodMk measurable_id)))
    simp only [List.length_cons]
    rw [collisionWordMeasure,lintegral_prod _ hm.aemeasurable,physicalMarkedWord,
      Kernel.lintegral_comp _ _ _ hF,
      physicalMarkedEvent_parameters b endTime C m p hF.lintegral_kernel]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (physicalParameterWeight b endTime C m p a *
      selectedWordDensity b endTime C ms (mediumParameterState b endTime p (m,a)) w) *
      F (selectedWordState b endTime ms (mediumParameterState b endTime p (m,a)) w)
        ∂collisionWordMeasure ms.length) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (physicalParameterWeight_ne_top b endTime C m p a),ih]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The propagated error from discarding the large geometric scales -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_scale_deletion {r s₀ η K α γ d₀ q a T M : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hM : 0 < M) (N : ℕ)
    {f : Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (m : ℕ)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    iterate a (selectedFreeKernel r s₀ η K α γ d₀ q N) f m z ≤
      iterate a (retainedFreeKernel r s₀ η K α γ d₀ q M N) f m z+
        (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M)*ENNReal.ofReal (T-a))*
          deletionCoefficient B
            (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a)*ENNReal.ofReal (T-a)) m := by
  have he := selectedFreeKernel_decomposition r s₀ η K α γ d₀ q M N
  have hmass : ∀ y, y.1.1 ∈ Icc a T →
      (retainedFreeKernel r s₀ η K α γ d₀ q M N+
        discardedFreeKernel r s₀ η K α γ d₀ q M N) y univ ≤
          ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
    rw [← he]
    intro y hy
    apply (selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      N y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (JetCoreSheet.growthConstant_nonneg hK α γ q) ha hy.1)
  have hsmall : ∀ y, y.1.1 ∈ Icc a T →
      discardedFreeKernel r s₀ η K α γ d₀ q M N y univ ≤
        ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/M) := by
    intro y hy
    exact discardedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ hM N y
      (ha.le.trans hy.1)
  rw [he]
  exact iterate_deletion_bound _ _ hmass hsmall hfm hf m z hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Successively chosen nonaxial thresholds for the actual selected kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel

def transverseRetained (b : ℝ) : Set Velocity := {v | b ≤ ‖transverse v‖}

theorem transverseRetained_measurable (b : ℝ) : MeasurableSet (transverseRetained b) :=
  measurableSet_le measurable_const (by fun_prop)

theorem selected_successive_thresholds {K α γ q a ε b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) (m : ℕ) :
    ∃ b : ℕ → ℝ, b 0 = b₀ ∧ (∀ i, 0 < b i) ∧
      ∀ᶠ n in atTop, ∀ i < m, ∀ (N : ℕ) (z : Published.KineticPhase),
        a ≤ z.1.1 → z.2 ∈ transverseRetained (b i) →
        selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
          (transverseRetained (b (i+1)))ᶜ ≤ ENNReal.ofReal ε := by
  classical
  have hc : ∀ b : {b : ℝ // 0 < b}, ∃ d : {d : ℝ // 0 < d},
      ∀ᶠ n in atTop, ∀ (N : ℕ) (z : Published.KineticPhase),
        a ≤ z.1.1 → z.2 ∈ transverseRetained b.val →
        selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
          (transverseRetained d.val)ᶜ ≤ ENNReal.ofReal ε := by
    intro b
    obtain ⟨d,hd,he⟩ := selected_small_input_eventually hK hα hγ hq₁ hq₂ ha b.property
      hε hs₀ hsmax hη hηmax hd₀ hdmax hr hrlim
    refine ⟨⟨d,hd⟩,?_⟩
    have hset : (transverseRetained d)ᶜ = {w | ‖transverse w‖ < d} := by
      ext w
      simp only [transverseRetained,mem_compl_iff,mem_ofPred_eq,not_le]
    filter_upwards [he] with n hn N z ht hv
    rw [hset]
    exact hn N z ht hv
  choose next hn using hc
  let bs : ℕ → {b : ℝ // 0 < b} := fun i => Nat.recOn i ⟨b₀,hb₀⟩ (fun _ b => next b)
  refine ⟨fun i => (bs i).val,rfl,fun i => (bs i).property,?_⟩
  have hall : ∀ i ∈ Finset.range m, ∀ᶠ n in atTop, ∀ (N : ℕ) (z : Published.KineticPhase),
      a ≤ z.1.1 → z.2 ∈ transverseRetained (bs i).val →
      selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
        (transverseRetained (bs (i+1)).val)ᶜ ≤ ENNReal.ofReal ε := by
    intro i _
    exact hn (bs i)
  filter_upwards [(Finset.eventually_all (Finset.range m)).mpr hall] with n h i hi
  exact h i (Finset.mem_range.mpr hi)

theorem selected_successive_deletion {K α γ q a T ε b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (m : ℕ) {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n z, z.1.1 ∈ Icc a T → f n z ≤ B) :
    ∃ b : ℕ → ℝ, b 0 = b₀ ∧ (∀ i, 0 < b i) ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ) (z : Published.KineticPhase),
        z.1.1 ∈ Icc a T → z.2 ∈ transverseRetained b₀ →
        PositiveIteration.iterate a (selectedFreeKernel (r n) s₀ η K α γ d₀ q N) (f n) m z ≤
          PositiveIteration.restrictedChain a (selectedFreeKernel (r n) s₀ η K α γ d₀ q N)
            (fun i => transverseRetained (b i)) (fun i => transverseRetained_measurable (b i))
            (f n) 0 m z+
          (ENNReal.ofReal ε*ENNReal.ofReal (T-a))*PositiveIteration.deletionCoefficient B
            (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a)*ENNReal.ofReal (T-a)) m := by
  obtain ⟨b,hb,hpos,hsmall⟩ := selected_successive_thresholds hK hα hγ hq₁ hq₂ ha hε hb₀
    hs₀ hsmax hη hηmax hd₀ hdmax hr hrlim m
  refine ⟨b,hb,hpos,?_⟩
  filter_upwards [hsmall] with n hn N z hz hzv
  have hmass : ∀ y, y.1.1 ∈ Icc a T →
      selectedFreeKernel (r n) s₀ η K α γ d₀ q N y univ ≤
        ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
    intro y hy
    apply (selectedFreeKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      N y (ha.trans_le hy.1)).trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left (JetCoreSheet.growthConstant_nonneg hK α γ q) ha hy.1
  apply PositiveIteration.restrictedChain_deletion_bound _ (fun i => transverseRetained (b i))
    (fun i => transverseRetained_measurable (b i)) hmass (hfm n) (hf n) 0 m ?_ z hz
      (by simpa only [hb] using hzv)
  intro j _ hj y hy hyv
  exact hn j (by simpa only [zero_add] using hj) N y hy.1 hyv

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Successive bounded nonaxial velocity windows for the actual selected kernel -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def velocityWindow (R b : ℝ) : Set Velocity := {v | ‖v‖ ≤ R ∧ b ≤ ‖transverse v‖}

theorem velocityWindow_measurable (R b : ℝ) : MeasurableSet (velocityWindow R b) :=
  (measurableSet_le measurable_norm measurable_const).inter (transverseRetained_measurable b)

theorem selected_velocity_radii {K α γ q a ε R₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hR₀ : 0 < R₀) :
    ∃ R : ℕ → ℝ, R 0 = R₀ ∧ (∀ i, 0 < R i) ∧
      ∀ {r s₀ η d₀ : ℝ}, 0 < r → 0 < s₀ → s₀ ≤ 1/8 →
      0 < η → η ≤ Real.log 2 → 0 < d₀ → d₀ ≤ 1 →
      ∀ (i N : ℕ) (z : Published.KineticPhase), a ≤ z.1.1 → ‖z.2‖ ≤ R i →
        selectedFreeKernel r s₀ η K α γ d₀ q N z {v | R (i+1) < ‖v‖} ≤ ENNReal.ofReal ε := by
  classical
  have hc : ∀ R : {R : ℝ // 0 < R}, ∃ R' : {R : ℝ // 0 < R},
      ∀ {r s₀ η d₀ : ℝ}, 0 < r → 0 < s₀ → s₀ ≤ 1/8 →
      0 < η → η ≤ Real.log 2 → 0 < d₀ → d₀ ≤ 1 →
      ∀ (N : ℕ) (z : Published.KineticPhase), a ≤ z.1.1 → ‖z.2‖ ≤ R.val →
        selectedFreeKernel r s₀ η K α γ d₀ q N z {v | R'.val < ‖v‖} ≤ ENNReal.ofReal ε := by
    intro R
    obtain ⟨R',hR',he⟩ := selected_velocity_tail hK hα hγ hq₁ hq₂ ha R.property.le hε
    exact ⟨⟨R',hR'⟩,he⟩
  choose next hn using hc
  let radii : ℕ → {R : ℝ // 0 < R} := fun i =>
    Nat.recOn i ⟨R₀,hR₀⟩ (fun _ R => next R)
  refine ⟨fun i => (radii i).val,rfl,fun i => (radii i).property,?_⟩
  intro r s₀ η d₀ hr hs₀ hsmax hη hηmax hd₀ hdmax i N z ht hv
  exact hn (radii i) hr hs₀ hsmax hη hηmax hd₀ hdmax N z ht hv

theorem selected_velocity_windows {K α γ q a ε R₀ b₀ s₀ η d₀ : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) (m : ℕ) :
    ∃ R b : ℕ → ℝ, R 0 = R₀ ∧ b 0 = b₀ ∧ (∀ i, 0 < R i) ∧ (∀ i, 0 < b i) ∧
      ∀ᶠ n in atTop, ∀ i < m, ∀ (N : ℕ) (z : Published.KineticPhase),
        a ≤ z.1.1 → z.2 ∈ velocityWindow (R i) (b i) →
        selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
          (velocityWindow (R (i+1)) (b (i+1)))ᶜ ≤
          ENNReal.ofReal ε+ENNReal.ofReal ε := by
  obtain ⟨R,hR,hRpos,htail⟩ := selected_velocity_radii hK hα hγ hq₁ hq₂ ha hε hR₀
  obtain ⟨b,hb,hbpos,hsmall⟩ := selected_successive_thresholds hK hα hγ hq₁ hq₂ ha hε hb₀
    hs₀ hsmax hη hηmax hd₀ hdmax hr hrlim m
  refine ⟨R,b,hR,hb,hRpos,hbpos,?_⟩
  filter_upwards [hsmall] with n hn i hi N z ht hz
  have hsubset : (velocityWindow (R (i+1)) (b (i+1)))ᶜ ⊆
      {v | R (i+1) < ‖v‖} ∪ (transverseRetained (b (i+1)))ᶜ := by
    intro v hv
    by_cases h : ‖v‖ ≤ R (i+1)
    · right
      intro hvb
      exact hv ⟨h,hvb⟩
    · exact Or.inl (lt_of_not_ge h)
  calc
    _ ≤ selectedFreeKernel (r n) s₀ η K α γ d₀ q N z
        ({v | R (i+1) < ‖v‖} ∪ (transverseRetained (b (i+1)))ᶜ) := measure_mono hsubset
    _ ≤ selectedFreeKernel (r n) s₀ η K α γ d₀ q N z {v | R (i+1) < ‖v‖}+
        selectedFreeKernel (r n) s₀ η K α γ d₀ q N z (transverseRetained (b (i+1)))ᶜ :=
      measure_union_le _ _
    _ ≤ _ := add_le_add
      (htail (hr n) hs₀ hsmax hη hηmax hd₀ hdmax i N z ht hz.1)
      (hn i hi N z ht hz.2)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The small-origin error for the actual selected hard-sphere kernel -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selected_origin_deletion {r s₀ η K α γ d₀ q a T ρ b : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hb : 0 < b) (N : ℕ) (c : Transverse)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hspeed : ∀ i v, v ∈ S i → b ≤ ‖transverse v‖)
    {f : Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (i n : ℕ)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) (hzS : z.2 ∈ S i) :
    restrictedChain a (selectedFreeKernel r s₀ η K α γ d₀ q N) S hS f i n z ≤
      restrictedChain a (awayOriginKernel c ρ (selectedFreeKernel r s₀ η K α γ d₀ q N))
        S hS f i n z+
      (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a)*ENNReal.ofReal (2*ρ/b))*
        deletionCoefficient B
          (ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a)*ENNReal.ofReal (T-a)) n := by
  have hmass (y : Published.KineticPhase) (hy : y.1.1 ∈ Icc a T) :
      selectedFreeKernel r s₀ η K α γ d₀ q N y univ ≤
        ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/a) := by
    apply (selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      N y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (JetCoreSheet.growthConstant_nonneg hK α γ q) ha hy.1)
  exact restrictedChain_origin_deletion hρ hb c _ S hS hspeed hmass hfm hf i n z hz hzS

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
