import OAI.Geometry.QuadricBundles.TraceExtraction

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
noncomputable section
local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

lemma upperSemicontinuousOn_aestronglyMeasurable {E : Type u1}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} (hΩ : MeasurableSet Ω) {q : E → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (μ : Measure E) :
    AEStronglyMeasurable q (μ.restrict Ω) :=
  (aemeasurable_restrict_of_measurable_subtype hΩ
    (upperSemicontinuousOn_iff_restrict.mpr hq).measurable).aestronglyMeasurable

lemma DiskPshOn.le_of_ae {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q)
    (hr : UpperSemicontinuousOn r Ω) (hpos : ∀ x∈Ω, 0≤q x)
    (hae : q ≤ᵐ[volume.restrict Ω] r) : ∀ x∈Ω, q x≤r x := by
  intro x hx
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hrx : UpperSemicontinuousAt r x := by
    intro b hb
    simpa only [hΩ.nhdsWithin_eq hx] using hr x hx b hb
  have hevent : {y | r y<c} ∩ Ω ∈ 𝓝 x :=
    inter_mem (hrx c hc) (hΩ.mem_nhds hx)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hcb : closedBall x (R/2) ⊆ Ω := by
    intro y hy
    exact (hball (lt_of_le_of_lt (show dist y x≤R/2 from hy) (by linarith))).2
  have hbc : ∀ y∈ball x (R/2), r y≤c := by
    intro y hy
    exact (hball (lt_trans (show dist y x<R/2 from hy) (by linarith))).1.le
  have hBΩ : ball x (R/2) ⊆ Ω := ball_subset_closedBall.trans hcb
  have hmeas : AEStronglyMeasurable q (volume.restrict (ball x (R/2))) :=
    (upperSemicontinuousOn_aestronglyMeasurable hΩ.measurableSet hq.1 volume).mono_measure
      (Measure.restrict_mono hBΩ le_rfl)
  have hle : q ≤ᵐ[volume.restrict (ball x (R/2))] fun _ ↦ c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBΩ hae,
      ae_restrict_mem measurableSet_ball] with y he hy
    exact he.trans (hbc y hy)
  have hnorm : ∀ᵐ y ∂volume.restrict (ball x (R/2)), ‖q y‖≤c := by
    filter_upwards [hle,ae_restrict_mem measurableSet_ball] with y he hy
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos y (hBΩ hy))] using he
  have hconst : IntegrableOn (fun _ : ℂ × ℂ ↦ c) (ball x (R/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hi : IntegrableOn q (ball x (R/2)) := hconst.mono' hmeas hnorm
  have hm : 0 < (volume (ball x (R/2))).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x (by linarith)).ne' measure_ball_lt_top.ne
  have hsub := hq.base_submean hΩ hx (show 0<R/2 by linarith) hcb hi
  have hu := integral_mono_ae hi hconst hle
  simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at hu
  exact (mul_le_mul_iff_right₀ hm).mp (hsub.trans hu)

lemma DiskPshOn.eqOn_of_ae {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (hae : q =ᵐ[volume.restrict Ω] r) : EqOn q r Ω := by
  intro x hx
  exact le_antisymm (hq.le_of_ae hΩ hr.1 hqpos (hae.mono fun _ h ↦ h.le) x hx)
    (hr.le_of_ae hΩ hq.1 hrpos (hae.mono fun _ h ↦ h.ge) x hx)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section
local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

lemma UpperSemicontinuousOn.integrableOn_compact_nonneg {E : Type u2}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {Ω K : Set E} (hΩ : MeasurableSet Ω) {q : E → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (hK : IsCompact K) (hKmeas : MeasurableSet K)
    (hKΩ : K ⊆ Ω) (hpos : ∀ x∈K, 0≤q x) : IntegrableOn q K μ := by
  obtain ⟨C,hC⟩ := (hq.mono hKΩ).bddAbove_of_isCompact hK
  have hm := (upperSemicontinuousOn_aestronglyMeasurable hΩ hq μ).mono_measure
    (Measure.restrict_mono hKΩ le_rfl)
  have hc : IntegrableOn (fun _ : E ↦ C) K μ := integrableOn_const hK.measure_ne_top
  apply hc.mono' hm
  filter_upwards [ae_restrict_mem hKmeas] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos x hx)] using hC (mem_image_of_mem q hx)

lemma DiskPshOn.integrableOn_ball_nonneg {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hpos : ∀ x∈Ω, 0≤q x)
    {x : ℂ × ℂ} {r : ℝ} (hb : closedBall x r ⊆ Ω) : IntegrableOn q (ball x r) :=
  (UpperSemicontinuousOn.integrableOn_compact_nonneg hΩ.measurableSet hq.1 (isCompact_closedBall _ _) measurableSet_closedBall
    hb (fun x hx ↦ hpos x (hb hx))).mono_set ball_subset_closedBall

lemma DiskPshOn.le_of_averages {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (havg : ∀ x ρ, 0<ρ → closedBall x ρ ⊆ Ω →
      (⨍ y in ball x ρ, q y) ≤ ⨍ y in ball x ρ, r y) : ∀ x∈Ω, q x≤r x := by
  intro x hx
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hrx : UpperSemicontinuousAt r x := by
    intro b hb
    simpa only [hΩ.nhdsWithin_eq hx] using hr.1 x hx b hb
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hrx c hc) (hΩ.mem_nhds hx))
  have hcb : closedBall x (R/2) ⊆ Ω := by
    intro y hy
    exact (hball (lt_of_le_of_lt (show dist y x≤R/2 from hy) (by linarith))).2
  have hbc : ∀ y∈ball x (R/2), r y≤c := by
    intro y hy
    exact (hball (lt_trans (show dist y x<R/2 from hy) (by linarith))).1.le
  have hi := hr.integrableOn_ball_nonneg hΩ hrpos hcb
  have hconst : IntegrableOn (fun _ : ℂ × ℂ ↦ c) (ball x (R/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hu := integral_mono_ae hi hconst ((ae_restrict_mem measurableSet_ball).mono hbc)
  have hm : 0 < (volume (ball x (R/2))).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x (by linarith)).ne' measure_ball_lt_top.ne
  have hsub := hq.base_average_submean hΩ hx (show 0<R/2 by linarith) hcb
    (hq.integrableOn_ball_nonneg hΩ hqpos hcb)
  have hav := havg x (R/2) (by linarith) hcb
  apply (hsub.trans hav).trans
  rw [setAverage_eq,smul_eq_mul,measureReal_def,← div_eq_inv_mul,div_le_iff₀ hm]
  simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hu

lemma DiskPshOn.eqOn_of_averages {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q r : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) (hr : DiskPshOn Ω r)
    (hqpos : ∀ x∈Ω, 0≤q x) (hrpos : ∀ x∈Ω, 0≤r x)
    (havg : ∀ x ρ, 0<ρ → closedBall x ρ ⊆ Ω →
      (⨍ y in ball x ρ, q y) = ⨍ y in ball x ρ, r y) : EqOn q r Ω := by
  intro x hx
  exact le_antisymm
    (hq.le_of_averages hΩ hr hqpos hrpos (fun x r hr hb ↦ (havg x r hr hb).le) x hx)
    (hr.le_of_averages hΩ hq hrpos hqpos (fun x r hr hb ↦ (havg x r hr hb).ge) x hx)

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
  (X : ExtractedTrace ex P)
def value (a : TraceIndex) (p : BaseCoordinates × FiberCoordinates) : ℝ :=
  quadraticValue (X.matrix a p.1) p.2
lemma base_psh (a : TraceIndex) (v : FiberCoordinates) :
    DiskPshOn (traceInterior a) (fun x ↦ X.value a (x,v)) :=
  (X.psh a).comp (by fun_prop) (fun _ hx ↦ ⟨hx,mem_univ _⟩)
lemma value_nonneg (a : TraceIndex) {x : BaseCoordinates} (hx : x∈traceInterior a) (v : FiberCoordinates) :
    0≤X.value a (x,v) := quadraticValue_nonneg (X.positive a x hx) v

lemma exhaustion_value_eq (i : StandardChart) (n n' : ℕ) {x : BaseCoordinates}
    (hx : x∈traceInterior (i,n)) (hx' : x∈traceInterior (i,n')) (v : FiberCoordinates) :
    X.value (i,n) (x,v)=X.value (i,n') (x,v) := by
  let Ω := traceInterior (i,n) ∩ traceInterior (i,n')
  have havg : ∀ y r, 0<r → closedBall y r ⊆ Ω →
      (⨍ z in ball y r, X.value (i,n) (z,v)) = ⨍ z in ball y r, X.value (i,n') (z,v) := by
    intro y r _ hb
    have hbn := (ball_subset_closedBall.trans hb).trans inter_subset_left
    have hbn' := (ball_subset_closedBall.trans hb).trans inter_subset_right
    have h1 := X.averages (i,n) y r v hbn
    have h2 := X.averages (i,n') y r v hbn'
    have he (k : ℕ) : (⨍ z in ball y r,
        quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n) z) v) =
        ⨍ z in ball y r, quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n') z) v := by
      apply average_congr
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [cutoffTrace_eq _ _ (traceDomain_subset_support _ (traceInterior_subset_domain _ (hbn hz))),
        cutoffTrace_eq _ _ (traceDomain_subset_support _ (traceInterior_subset_domain _ (hbn' hz)))]
    simpa only [value] using tendsto_nhds_unique (h1.congr he) h2
  exact ((X.base_psh (i,n) v).mono inter_subset_left).eqOn_of_averages
    (isOpen_ball.inter isOpen_ball) ((X.base_psh (i,n') v).mono inter_subset_right)
    (fun y hy ↦ X.value_nonneg _ hy.1 v) (fun y hy ↦ X.value_nonneg _ hy.2 v) havg ⟨hx,hx'⟩
end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def traceLevel (z : BaseCoordinates) : ℕ := Nat.ceil ‖z‖
lemma mem_traceInterior_level (i : StandardChart) (z : BaseCoordinates) :
    z∈traceInterior (i,traceLevel z) := by
  change dist z 0 < _
  rw [dist_zero_right]
  have h : ‖z‖≤(traceLevel z : ℝ) := Nat.le_ceil _
  dsimp
  linarith

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
  (X : ExtractedTrace ex P)
def globalMatrix (i : StandardChart) (z : BaseCoordinates) : TwoMatrix :=
  X.matrix (i,traceLevel z) z
def globalValue (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) : ℝ :=
  quadraticValue (X.globalMatrix i p.1) p.2
lemma globalValue_eq_value (i : StandardChart) (n : ℕ)
    {p : BaseCoordinates × FiberCoordinates} (hp : p.1∈traceInterior (i,n)) :
    X.globalValue i p=X.value (i,n) p :=
  X.exhaustion_value_eq i _ n (mem_traceInterior_level i p.1) hp p.2
lemma globalMatrix_positive (i : StandardChart) (z : BaseCoordinates) : (X.globalMatrix i z).PosSemidef :=
  X.positive _ _ (mem_traceInterior_level i z)
lemma globalValue_nonneg (i : StandardChart) (p : BaseCoordinates × FiberCoordinates) :
    0≤X.globalValue i p := quadraticValue_nonneg (X.globalMatrix_positive i p.1) p.2

lemma globalValue_upperSemicontinuous (i : StandardChart) : UpperSemicontinuous (X.globalValue i) := by
  intro p c hc
  let n := traceLevel p.1
  have hp : p∈traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates) :=
    ⟨mem_traceInterior_level i p.1,mem_univ _⟩
  have hU : IsOpen (traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates)) := isOpen_ball.prod isOpen_univ
  have hsc := (X.psh (i,n)).1 p hp c (by
    change X.value (i,n) p < c
    rwa [← X.globalValue_eq_value i n hp.1])
  rw [hU.nhdsWithin_eq hp] at hsc
  filter_upwards [hsc,hU.mem_nhds hp] with y hy hyU
  change X.value (i,n) y < c at hy
  rwa [X.globalValue_eq_value i n hyU.1]

lemma exists_traceInterior_of_compact (i : StandardChart) {K : Set BaseCoordinates} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ traceInterior (i,n) := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image continuous_norm.continuousOn
  obtain ⟨n,hn⟩ := exists_nat_gt C
  refine ⟨n,fun x hx ↦ ?_⟩
  have h := hC (mem_image_of_mem _ hx)
  change dist x 0 < (n:ℝ)+2
  rw [dist_zero_right]
  linarith

lemma globalValue_psh (i : StandardChart) : DiskPshOn univ (X.globalValue i) := by
  refine ⟨(X.globalValue_upperSemicontinuous i).upperSemicontinuousOn univ,?_⟩
  intro U hU γ hγ _
  have hsc : UpperSemicontinuousOn (X.globalValue i ∘ γ) U :=
    ((X.globalValue_upperSemicontinuous i).upperSemicontinuousOn univ).comp hγ.continuousOn (mapsTo_univ _ _)
  refine ⟨hsc,?_⟩
  intro z hz r hr hball
  have hcompact : IsCompact ((fun w ↦ (γ w).1) '' closedBall z r) :=
    (isCompact_closedBall z r).image_of_continuousOn (hγ.continuousOn.fst.mono hball)
  obtain ⟨n,hn⟩ := exists_traceInterior_of_compact i hcompact
  let V := U ∩ γ ⁻¹' (traceInterior (i,n) ×ˢ (univ : Set FiberCoordinates))
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (isOpen_ball.prod isOpen_univ)
  have hB : closedBall z r ⊆ V := by
    intro w hw
    exact ⟨hball hw,hn (mem_image_of_mem _ hw),mem_univ _⟩
  have hp := (X.psh (i,n)).2 V hV γ (hγ.mono inter_subset_left) (fun _ h ↦ h.2)
  have he : EqOn (X.globalValue i ∘ γ) (X.value (i,n) ∘ γ) V :=
    fun w hw ↦ X.globalValue_eq_value i n hw.2.1
  have he' : EqOn (X.globalValue i ∘ γ) (X.value (i,n) ∘ γ) (ball z r) :=
    he.mono (ball_subset_closedBall.trans hB)
  have hs := hp.2 z (hB (mem_closedBall_self hr.le)) r hr hB
  refine ⟨hs.1.congr_fun he'.symm measurableSet_ball,?_⟩
  rw [he (hB (mem_closedBall_self hr.le))]
  have hint : (∫ w in ball z r, (X.globalValue i ∘ γ) w)=
      ∫ w in ball z r, (X.value (i,n) ∘ γ) w := integral_congr_ae
    ((ae_restrict_mem measurableSet_ball).mono fun w hw ↦ he' hw)
  rw [hint]
  exact hs.2
end ExtractedTrace
end
end QuadricCounterexample

end

end OAI
