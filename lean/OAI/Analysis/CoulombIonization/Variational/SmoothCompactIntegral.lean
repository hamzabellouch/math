import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoherentHilbert

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SmoothCompactIntegral_scope

open MeasureTheory Filter Metric
open scoped ContDiff Topology

universe u v
variable {X : Type u} {A : Type v} {E : Type u}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [SMulCommClass ℝ ℂ E]

def firstPartial (F : X × A → E) (p : X × A) : X →L[ℝ] E :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X A)

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ A] [MeasurableSpace A]
  [BorelSpace A] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] in
lemma firstPartial_hasFDerivAt {F : X × A → E} (hF : Differentiable ℝ F) (x : X) (a : A) :
    HasFDerivAt (fun y => F (y,a)) (firstPartial F (x,a)) x := by
  simpa only [firstPartial, Function.comp_def] using (hF (x,a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const a x))

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ A] [MeasurableSpace A]
  [BorelSpace A] [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E] in
lemma firstPartial_contDiff {F : X × A → E} {n : ℕ∞ω} (hF : ContDiff ℝ (n+1) F) :
    ContDiff ℝ n (firstPartial F) := by
  exact (contDiff_succ_iff_fderiv.mp hF).2.2.clm_comp contDiff_const

lemma weightedSetIntegral_hasFDerivAt (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) {F : X × A → E} (hF : ContDiff ℝ 1 F)
    {w : A → ℂ} (hw : Continuous w) (x : X) :
    HasFDerivAt (fun y => ∫ a in K, w a • F (y,a) ∂μ)
      (∫ a in K, w a • firstPartial F (x,a) ∂μ) x := by
  have hD : Continuous (firstPartial F) := by
    exact (firstPartial_contDiff (n := 0) (by simpa using hF)).continuous
  have hcont : Continuous (fun p : X × A => w p.2 • firstPartial F p) :=
    (hw.comp continuous_snd).smul hD
  obtain ⟨M,hM⟩ := ((isCompact_closedBall x 1).prod hK).exists_bound_of_continuousOn
    hcont.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall x 1) (bound := fun _ => M) (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => ((hw.smul
      (hF.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable))
  · exact ((hw.smul (hF.continuous.comp (continuous_const.prodMk continuous_id))).continuousOn).integrableOn_compact hK
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro y hy
    exact hM (y,a) ⟨hy,ha⟩
  · exact integrable_const _
  · exact Eventually.of_forall (fun a y _ =>
      (firstPartial_hasFDerivAt (hF.differentiable (by norm_num)) y a).const_smul (w a))

lemma weightedSetIntegral_contDiff_nat (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) (n : ℕ) {F : X × A → E}
    (hF : ContDiff ℝ (n : ℕ∞ω) F) {w : A → ℂ} (hw : Continuous w) :
    ContDiff ℝ (n : ℕ∞ω) (fun y => ∫ a in K, w a • F (y,a) ∂μ) := by
  induction n generalizing E with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_parametric_integral_of_continuous
      ((hw.comp continuous_snd).smul hF.continuous) hK
  | succ n ih =>
    have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hd (x : X) := weightedSetIntegral_hasFDerivAt μ K hK h1 hw x
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, ?_, ?_⟩
    · intro h
      simp at h
    · have he : (fderiv ℝ (fun y => ∫ a in K, w a • F (y,a) ∂μ)) =
          (fun y => ∫ a in K, w a • firstPartial F (y,a) ∂μ) :=
        funext (fun x => (hd x).fderiv)
      rw [he]
      exact ih (firstPartial_contDiff (by simpa only [Nat.cast_add, Nat.cast_one] using hF))

lemma weightedSetIntegral_contDiff (μ : Measure A) [IsFiniteMeasure μ]
    (K : Set A) (hK : IsCompact K) {F : X × A → E}
    (hF : ContDiff ℝ ∞ F) {w : A → ℂ} (hw : Continuous w) :
    ContDiff ℝ ∞ (fun y => ∫ a in K, w a • F (y,a) ∂μ) := by
  apply contDiff_infty.mpr
  intro n
  exact weightedSetIntegral_contDiff_nat μ K hK n (contDiff_infty.mp hF n) hw

end Work_SmoothCompactIntegral_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

def coherentSpatialSupport (g : Space → ℂ) (K : Set (Space × Space)) : Set Space :=
  (fun r : (Space × Space) × Space => r.2 + r.1.1) '' (K ×ˢ tsupport g)

lemma coherentSpatialSupport_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) : IsCompact (coherentSpatialSupport g K) :=
  (hK.prod hcg).image (by fun_prop)

lemma coherentPacket_zero_outside {g : Space → ℂ} {K : Set (Space × Space)}
    {q : Space × Space} (hq : q ∈ K) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    coherentPacket g q.1 q.2 x = 0 := by
  have hg : g (x-q.1) = 0 := by
    by_contra h
    apply hx
    exact ⟨(q,x-q.1), ⟨hq,subset_tsupport g h⟩, by simp⟩
  simp [coherentPacket,hg]

lemma coherentPacket_joint_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun r : Space × (Space × Space) => coherentPacket g r.2.1 r.2.2 r.1) := by
  unfold coherentPacket
  apply (hg.comp (contDiff_fst.sub contDiff_snd.fst)).mul
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_snd.snd.inner ℝ contDiff_fst)).mul contDiff_const)

def packetSynthesis (g : Space → ℂ) (μ : Measure (Space × Space))
    (w : Space × Space → ℂ) (x : Space) : ℂ :=
  ∫ q, w q * coherentPacket g q.1 q.2 x ∂μ

lemma packetSynthesis_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    ContDiff ℝ ∞ (packetSynthesis g μ w) := by
  have h := weightedSetIntegral_contDiff μ K hK (coherentPacket_joint_smooth hg) hw
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact h

lemma packetSynthesis_zero_outside {g : Space → ℂ}
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (w : Space × Space → ℂ) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    packetSynthesis g μ w x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with q hq
  simp only [coherentPacket_zero_outside hq hx,mul_zero,Pi.zero_apply]

lemma packetSynthesis_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hK : IsCompact K)
    (hμ : ∀ᵐ q ∂μ, q ∈ K) (w : Space × Space → ℂ) :
    HasCompactSupport (packetSynthesis g μ w) := by
  apply HasCompactSupport.of_support_subset_isCompact (coherentSpatialSupport_compact hcg hK)
  intro x hx
  by_contra hn
  exact hx (packetSynthesis_zero_outside μ hμ w hn)

lemma coherent_test_integrable {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) {v : Space → ℂ} (hv : Continuous v) :
    Integrable (fun r : (Space × Space) × Space =>
      conj (v r.2) * (w r.1 * coherentPacket g r.1.1 r.1.2 r.2)) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      conj (v r.2) * (w r.1 * coherentPacket g r.1.1 r.1.2 r.2)) := by
    unfold coherentPacket
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  rw [coherentPacket_zero_outside hr hx,mul_zero,mul_zero]

lemma coherentVector_inner_schwartz_left {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q : Space × Space) (v : SchwartzMap Space ℂ) :
    inner ℂ (v.toLp 2) (coherentVector hg hcg q) =
      ∫ x : Space, conj (v x) * coherentPacket g q.1 q.2 x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [v.coeFn_toLp 2 volume,coherentVector_coe hg hcg q] with x hv hq
  rw [hv,hq]
  simp only [RCLike.inner_apply,mul_comm]

lemma packetSynthesis_test {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) (v : SchwartzMap Space ℂ) :
    (∫ x : Space, conj (v x) * packetSynthesis g μ w x) =
      ∫ q, w q * inner ℂ (v.toLp 2) (coherentVector hg hcg q) ∂μ := by
  simp only [packetSynthesis,← integral_const_mul]
  have hi : Integrable (fun r : Space × (Space × Space) =>
      conj (v r.1) * (w r.2 * coherentPacket g r.2.1 r.2.2 r.1)) (volume.prod μ) :=
    (coherent_test_integrable hg hcg μ hK hμ hw v.continuous).swap
  rw [integral_integral_swap (f := fun x q =>
    conj (v x) * (w q * coherentPacket g q.1 q.2 x)) hi]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [coherentVector_inner_schwartz_left,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma packetSynthesis_memLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) : MemLp (packetSynthesis g μ w) 2 :=
  (packetSynthesis_smooth hg μ hK hμ hw).continuous.memLp_of_hasCompactSupport
    (packetSynthesis_compact hcg μ hK hμ w)

lemma coherentVector_weight_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    Integrable (fun q => w q • coherentVector hg hcg q) μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact (hw.smul (coherentVector_continuous hg hcg)).continuousOn.integrableOn_compact hK

lemma packetSynthesis_toLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    (packetSynthesis_memLp hg hcg μ hK hμ hw).toLp (packetSynthesis g μ w) =
      ∫ q, w q • coherentVector hg.continuous hcg q ∂μ := by
  apply ext_inner_left ℂ
  intro u
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure Space))
    ENNReal.ofNat_ne_top).induction_on u ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro v
    change inner ℂ (v.toLp 2) _ = inner ℂ (v.toLp 2) _
    rw [← integral_inner (𝕜 := ℂ) (coherentVector_weight_integrable hg.continuous hcg μ hK hμ hw)]
    simp only [inner_smul_right]
    rw [← packetSynthesis_test hg.continuous hcg μ hK hμ hw v,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume,
      (packetSynthesis_memLp hg hcg μ hK hμ hw).coeFn_toLp] with x hv hs
    rw [hv,hs]
    simp only [RCLike.inner_apply,mul_comm]

end CoulombAtom

end

end OAI
