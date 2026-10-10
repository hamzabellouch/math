import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppedLimits

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
namespace SLEExactGauge.RationalStop
lemma measurableSet_safe {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ → ℝ)
    (hf : ∀ u, Measurable (fun b => f b u)) (R s : ℝ) :
    MeasurableSet {b | Safe (f b) R s} := by
  simp only [Safe,ofPred_exists,ofPred_forall]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun r =>
    measurableSet_le (hf _) measurable_const

lemma safe_past {f : (ℝ≥0 → ℝ) → ℝ → ℝ}
    (hp : ∀ s ≥ 0, ∀ b c, (∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) → f b s = f c s)
    {R s : ℝ} (hs : 0 ≤ s) {b c : ℝ≥0 → ℝ}
    (hbc : ∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) : Safe (f b) R s ↔ Safe (f c) R s := by
  have he : ∀ r : ℚ, f b (sample s r) = f c (sample s r) := by
    intro r
    exact hp _ (sample_mem hs r).1 b c (fun u hu => hbc u (hu.trans (sample_mem hs r).2))
  unfold Safe
  simp only [he]

 

def Exit (f : ℝ → ℝ) (R H : ℝ) : ℝ :=
  sInf ({u | u ∈ Icc 0 H ∧ R ≤ f u} ∪ {H})

lemma exit_mem {f : ℝ → ℝ} {R H : ℝ} (hH : 0 ≤ H)
    (hf : ContinuousOn f (Icc 0 H)) :
    Exit f R H ∈ {u | u ∈ Icc 0 H ∧ R ≤ f u} ∪ {H} := by
  have hc : IsClosed {u | u ∈ Icc 0 H ∧ R ≤ f u} :=
    (hf.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc R).isClosed
  exact (hc.union isClosed_singleton).csInf_mem ⟨H,Or.inr rfl⟩
    ⟨0,by intro u hu; rcases hu with hu|hu; exact hu.1.1; simpa only [show u = H from hu] using hH⟩

lemma exit_bounds {f : ℝ → ℝ} {R H : ℝ} (hH : 0 ≤ H)
    (hf : ContinuousOn f (Icc 0 H)) : Exit f R H ∈ Icc 0 H := by
  rcases exit_mem hH hf with ⟨hu,_⟩ | hu
  · exact hu
  · change Exit f R H = H at hu
    rw [hu]
    exact ⟨hH,le_rfl⟩

lemma exit_le {f : ℝ → ℝ} {R H u : ℝ} (hH : 0 ≤ H)
    (hu : u ∈ Icc 0 H) (huR : R ≤ f u) : Exit f R H ≤ u := by
  exact csInf_le ⟨0,by intro v hv; rcases hv with hv|hv; exact hv.1.1; simpa only [show v = H from hv] using hH⟩
    (Or.inl ⟨hu,huR⟩)

lemma lt_exit_iff {f : ℝ → ℝ} {R H s : ℝ} (hH : 0 ≤ H)
    (hf : ContinuousOn f (Icc 0 H)) (hs : 0 ≤ s) :
    s < Exit f R H ↔ s < H ∧ Safe f R s := by
  constructor
  · intro h
    have hsH := h.trans_le (exit_bounds hH hf).2
    refine ⟨hsH,(safe_iff hs (hf.mono (Icc_subset_Icc_right hsH.le))).mpr ?_⟩
    intro u hu
    by_contra! hn
    have he := exit_le hH ⟨hu.1,hu.2.trans hsH.le⟩ hn
    linarith [hu.2]
  · rintro ⟨hsH,hS⟩
    have h := (safe_iff hs (hf.mono (Icc_subset_Icc_right hsH.le))).mp hS
    by_contra! hn
    rcases exit_mem hH hf with he|he
    · exact (h _ ⟨he.1.1,hn⟩).not_ge he.2
    · have he' : Exit f R H = H := he
      linarith

 

lemma bound_until_exit {f : ℝ → ℝ} {R H : ℝ} (hH : 0 ≤ H)
    (hf : ContinuousOn f (Icc 0 H)) (h0 : f 0 < R) :
    ∀ u ∈ Icc 0 (Exit f R H), f u ≤ R := by
  intro u hu
  have huH := hu.2.trans (exit_bounds hH hf).2
  by_cases h : u = 0
  · simpa only [h] using h0.le
  have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h)
  have hd : ∀ t ∈ Ico 0 u, f t ≤ R := by
    intro t ht
    have htE := ht.2.trans_le hu.2
    exact ((safe_iff ht.1 (hf.mono (Icc_subset_Icc_right (ht.2.le.trans huH)))).mp
      ((lt_exit_iff hH hf ht.1).mp htE).2 t ⟨ht.1,le_rfl⟩).le
  have hc : IsClosed {t ∈ Icc 0 H | f t ≤ R} :=
    (hf.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc R).isClosed
  have hsub : Ico 0 u ⊆ {t ∈ Icc 0 H | f t ≤ R} :=
    fun t ht => ⟨⟨ht.1,ht.2.le.trans huH⟩,hd t ht⟩
  have he := closure_minimal hsub hc
  rw [closure_Ico hu0.ne] at he
  exact (he ⟨hu0.le,le_rfl⟩).2

end SLEExactGauge.RationalStop

namespace SLEExactGauge.RationalStop
open Set MeasureTheory

lemma measurable_exit {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    {H R : ℝ} (hH : 0 ≤ H) (hf : ∀ u, Measurable (fun b => f b u))
    (hc : ∀ b, ContinuousOn (f b) (Icc 0 H)) :
    Measurable (fun b => Exit (f b) R H) := by
  apply measurable_of_Ioi
  intro s
  by_cases hs : 0 ≤ s
  · have he : (fun b => Exit (f b) R H) ⁻¹' Ioi s = {b | s < H ∧ Safe (f b) R s} := by
      ext b
      exact lt_exit_iff hH (hc b) hs
    rw [he]
    exact (MeasurableSet.const _).inter (measurableSet_safe f hf R s)
  · have he : (fun b => Exit (f b) R H) ⁻¹' Ioi s = univ := by
      ext b
      simp only [mem_preimage,mem_Ioi,mem_univ,iff_true]
      exact (lt_of_not_ge hs).trans_le (exit_bounds hH (hc b)).1
    rw [he]
    exact MeasurableSet.univ

 

lemma measurable_stopped_eval {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
    {f : Ω → ℝ → E} {τ : Ω → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hf : ∀ u, Measurable (fun b => f b u)) (hc : ∀ b, ContinuousOn (f b) (Icc 0 H))
    (hτ : Measurable τ) (hτH : ∀ b, τ b ∈ Icc 0 H) :
    Measurable (fun b => f b (τ b)) := by
  have hm := measurable_uncurry_of_continuous_of_measurable
    (u := fun t b => f b (sample H t))
    (fun b => (hc b).comp_continuous (continuous_sample H) (sample_mem hH))
    (fun t => hf (sample H t))
  have he : (fun b => f b (τ b)) = (fun q : ℝ × Ω => f q.2 (sample H q.1)) ∘ (fun b => (τ b,b)) := by
    funext b
    exact congrArg (f b) (sample_self (hτH b)).symm
  rw [he]
  exact hm.comp (hτ.prodMk measurable_id)
end SLEExactGauge.RationalStop

namespace SLEExactGauge.AngleCalculus
open scoped ContDiff
lemma contDiffAt_V {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ ∞ V z := by
  have hd : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact Complex.imCLM.contDiff.contDiffAt.div hd.contDiffAt (Complex.normSq_pos.mpr hz).ne'
end SLEExactGauge.AngleCalculus
namespace SLEExactGauge.OnePoint
open _root_.OAI.SLEExactGauge.Localization AngleCalculus BrownianCalculus ODEPath RationalStop
open scoped ContDiff

lemma contDiffOn_field (P : Parameter) : ContDiffOn ℝ ∞ (Function.uncurry (field P)) domain := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hz : ContDiffAt ℝ ∞ (fun q : State × ℝ => q.1.2-(q.2:ℂ)) q :=
    (contDiffAt_snd.comp q contDiffAt_fst).sub (Complex.ofRealCLM.contDiff.contDiffAt.comp q contDiffAt_snd)
  have hn : q.1.2-(q.2:ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    have hh : 0 < q.1.2.im := hq
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    linarith
  exact (((contDiffAt_V hn).comp q hz).pow 2).prodMk
    (by
      simpa only [div_eq_mul_inv] using (contDiffAt_const (c := (P.a:ℂ))).mul
        (hz.inv hn))

lemma exists_cutoff_field (P : Parameter) {K : Set (State × ℝ)}
    (hK : IsCompact K) (hKO : K ⊆ domain) :
    ∃ v : State → ℝ → State, ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      ContDiff ℝ ∞ (Function.uncurry v) ∧
      (∀ x b, ‖v x b‖ ≤ M) ∧
      (∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖) ∧
      (∀ q ∈ K, v q.1 q.2 = field P q.1 q.2) := by
  obtain ⟨V,hV,hVK,hVe⟩ := compact_extension hK isOpen_domain hKO
    (Function.uncurry (field P)) (contDiffOn_field P)
  obtain ⟨M,hM⟩ := hVK.exists_bound_of_continuous hV.continuous
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVK hV (by simp)
  refine ⟨fun x b => V (x,b),max M 0,L,le_max_right _ _,L.coe_nonneg,hV,?_,?_,?_⟩
  · intro x b
    exact (hM (x,b)).trans (le_max_left _ _)
  · intro b x y
    have H := hL.dist_le_mul (x,b) (y,b)
    simpa [dist_eq_norm,Prod.norm_def] using H
  · intro q hq
    exact (hVe q hq).self_of_nhds

 

theorem exists_stopped_green (P : Parameter) {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    {H : ℝ} (hH : 0 ≤ H) (φ : State × ℝ → ℝ) (hφ : Continuous φ)
    (hK : IsCompact {q | φ q ≤ 2}) (hKO : {q | φ q ≤ 2} ⊆ domain)
    (z : State) (hz : φ (z,0) < 1) :
    ∃ v : State → ℝ → State, ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      ContDiff ℝ ∞ (Function.uncurry v) ∧
      (∀ x b, ‖v x b‖ ≤ M) ∧
      (∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖) ∧
      (∀ q, φ q ≤ 2 → v q.1 q.2 = field P q.1 q.2) ∧
      let g := fun b : Driver => ODEPath.flow v z b
      let τ := fun b : Driver => Exit (fun u => φ (g b u,b u.toNNReal)) 1 H
      (∀ b u, u ∈ Icc 0 (τ b) → φ (g b u,b u.toNNReal) ≤ 1) ∧
      ∀ t ≥ 0, (∫ b : Driver, green P
        (g b (min t (τ b)),b (min t (τ b)).toNNReal) ∂W) = green P (z,0) := by
  obtain ⟨v,M,L,hM,hL,hv,hbound,hlip,hveq⟩ := exists_cutoff_field P hK hKO
  let g := fun b : Driver => ODEPath.flow v z b
  let f := fun (b : ℝ≥0 → ℝ) u => φ (ODEPath.flow v z b u,b u.toNNReal)
  let τ := fun b : Driver => Exit (f b) 1 H
  have hg (b : Driver) := ODEPath.flow_solution v hv.continuous z b b.continuous
    hM hL (by linarith : 0 ≤ H+1) hbound hlip
  have hgc (b : Driver) : ContinuousOn (g b) (Icc 0 (H+1)) :=
    ODEPath.continuousOn_flow v hv.continuous z b b.continuous hM hL (by linarith) hbound hlip
  have hfc (b : Driver) : ContinuousOn (f b) (Icc 0 (H+1)) :=
    hφ.comp_continuousOn ((hgc b).prodMk ((b.continuous.comp continuous_real_toNNReal).continuousOn))
  have hfcH (b : Driver) : ContinuousOn (f b) (Icc 0 H) :=
    (hfc b).mono (Icc_subset_Icc_right (by linarith))
  have hf0 (b : Driver) : f b 0 < 1 := by
    simpa only [f,(hg b).1,Real.toNNReal_zero,map_zero] using hz
  have hτ (b : Driver) : 0 ≤ τ b ∧ τ b < H+1 := by
    have hb := exit_bounds hH (hfcH b) (R := 1)
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by linarith)⟩
  have hsafe (b : Driver) : ∀ u ∈ Icc 0 (τ b), f b u ≤ 1 :=
    bound_until_exit hH (hfcH b) (hf0 b)
  refine ⟨v,M,L,hM,hL,hv,hbound,hlip,hveq,hsafe,?_⟩
  intro t ht
  let K : Set (State × ℝ) := {q | φ q ≤ 2}
  have hDo : IsOpen {q | φ q < 2} := isOpen_lt hφ continuous_const
  have hK1 : IsCompact {q | φ q ≤ 1} :=
    hK.of_isClosed_subset (isClosed_le hφ continuous_const) (fun q hq => by dsimp at *; linarith)
  obtain ⟨δ,hδ,hδD⟩ := hK1.exists_thickening_subset_open hDo (fun q hq => by dsimp at *; linarith)
  have hD (b : Driver) : ∃ δ > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < δ → (x,b u.toNNReal) ∈ K := by
    refine ⟨δ,hδ,?_⟩
    intro u hu x hx
    have hi : φ (x,b u.toNNReal) < 2 := hδD (by
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(g b u,b u.toNNReal),hsafe b u hu,?_⟩
      rw [dist_eq_norm]
      change max ‖x-g b u‖ ‖b u.toNNReal-b u.toNNReal‖ < δ
      simpa using hx)
    exact hi.le
  have mf (u : ℝ) : Measurable (fun b : ℝ≥0 → ℝ => f b u) :=
    hφ.measurable.comp ((ODEPath.measurable_flow v hv.continuous.measurable z u).prodMk (measurable_pi_apply _))
  have hfpast : ∀ s ≥ 0, ∀ b c : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) → f b s = f c s := by
    intro s hs b c hbc
    have hb := hbc s.toNNReal (by simpa only [Real.coe_toNNReal',max_eq_left hs] using le_refl s)
    simp only [f,ODEPath.flow_past v z hs hbc,hb]
  let S : ℝ≥0 → Set ((ℝ≥0 → ℝ) × (State × ℝ)) := fun r =>
    {q | (r:ℝ) < H ∧ Safe (f q.1) 1 r ∧ q.2 ∈ K}
  have mS : ∀ r, MeasurableSet (S r) := by
    intro r
    exact (MeasurableSet.const _).inter
      (((measurableSet_safe f mf 1 _).preimage measurable_fst).inter (hK.measurableSet.preimage measurable_snd))
  have hSpast : ∀ r b c, (∀ u ≤ r, b u = c u) → ∀ x, ((b,x) ∈ S r ↔ (c,x) ∈ S r) := by
    intro r b c hbc x
    have he : Safe (f b) 1 r ↔ Safe (f c) 1 r := safe_past hfpast r.coe_nonneg
      (fun u hu => hbc u hu)
    exact and_congr_right fun _ => and_congr_left fun _ => he
  have hSeq : ∀ (b : Driver) r x, (((b:ℝ≥0 → ℝ),x) ∈ S r ↔ (r:ℝ) < τ b ∧ x ∈ K) := by
    intro b r x
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
    rw [lt_exit_iff hH (hfcH b) r.coe_nonneg]
    exact and_assoc.symm
  apply expected_stopped_local_grid_eq hW (green P) K domain hK isOpen_domain hKO (contDiffOn_green P)
    v hv.continuous.measurable g z hL hM hbound hlip (fun b => (hg b).1) (fun b => (hg b).2)
    (fun b => hv.continuous.comp_continuousOn ((hgc b).prodMk
      ((b.continuous.comp continuous_real_toNNReal).continuousOn))) τ hτ hD
    (fun q hq => by rw [hveq q hq]; exact green_generator P (hKO hq))
    S mS hSpast hSeq (fun r q hq => hq.2.2) (by change φ (z,0) ≤ 2; linarith) ht
end SLEExactGauge.OnePoint

 

noncomputable section
open Set Filter Real
open scoped Topology
namespace SLEExactGauge.ReverseDerivative

def r (a : ℝ) : ℝ := 2*a+1/2
def zeta (a : ℝ) : ℝ := a-1/(16*a)
def lambda (a : ℝ) : ℝ := a+1+3/(16*a)
def R (x y : ℝ) : ℝ := x^2+y^2
def D (u x y : ℝ) : ℝ := R x y+u/2

def H (a u x y l : ℝ) : ℝ :=
  lambda a*l+r a/2*Real.log (R x y)+(zeta a-r a)*Real.log y-
    zeta a/2*Real.log (D u x y)
def F (a u x y l : ℝ) : ℝ := Real.exp (H a u x y l)
def Hx (a u x y : ℝ) : ℝ := r a*x/R x y-zeta a*x/D u x y
def Hxx (a u x y : ℝ) : ℝ :=
  r a*(y^2-x^2)/(R x y)^2-zeta a/D u x y+2*zeta a*x^2/(D u x y)^2
def Hy (a u x y : ℝ) : ℝ :=
  r a*y/R x y+(zeta a-r a)/y-zeta a*y/D u x y

def residual (a u x y : ℝ) : ℝ :=
  R x y*((a-1/2+1/(16*a))*x^2+(2*a+1/2)*y^2)+
    u/2*((2*a+3/2)*x^2+(2*a+1/2)*y^2)

lemma R_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < R x y := by
  unfold R
  positivity

lemma D_pos {u y : ℝ} (hu : 0 ≤ u) (hy : 0 < y) (x : ℝ) : 0 < D u x y := by
  exact add_pos_of_pos_of_nonneg (R_pos x hy) (div_nonneg hu (by norm_num))

lemma parameters {a : ℝ} (ha : 1/4 < a) :
    0 < zeta a ∧ 0 < lambda a ∧ 2 < zeta a+lambda a ∧ 1 < r a ∧ r a < 4*a := by
  have ha0 : 0 < a := by linarith
  have h16 : 0 < 16*a := by positivity
  have hz : 0 < zeta a := by
    unfold zeta
    have hsq : 1 < 16*a^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ h16).2
    nlinarith
  have hl : 0 < lambda a := by unfold lambda; positivity
  have he : zeta a+lambda a-2 = (4*a-1)^2/(8*a) := by
    unfold zeta lambda
    field_simp
    ring
  have hsum : 2 < zeta a+lambda a := by
    have : 0 < (4*a-1)^2/(8*a) := div_pos (sq_pos_of_pos (by linarith)) (by positivity)
    linarith
  exact ⟨hz,hl,hsum,by unfold r; linarith,by unfold r; linarith⟩

lemma residual_nonneg {a u y : ℝ} (ha : 1/4 < a) (hu : 0 ≤ u)
    (hy : 0 < y) (x : ℝ) : 0 ≤ residual a u x y := by
  have ha0 : 0 < a := by linarith
  have hc : 0 ≤ a-1/2+1/(16*a) := by
    have he : a-1/2+1/(16*a) = (4*a-1)^2/(16*a) := by field_simp; ring
    rw [he]
    positivity
  unfold residual
  have hR := (R_pos x hy).le
  positivity

lemma hasDerivAt_Hx {a u x y l : ℝ} (hu : 0 ≤ u) (hy : 0 < y) :
    HasDerivAt (fun w => H a u w y l) (Hx a u x y) x := by
  have hR : HasDerivAt (fun w : ℝ => R w y) (2*x) x := by
    convert! ((hasDerivAt_id x).pow 2).add_const (y^2) using 1
    simp
  have hD : HasDerivAt (fun w : ℝ => D u w y) (2*x) x := hR.add_const (u/2)
  have hd := (((hR.log (R_pos x hy).ne').const_mul (r a/2)).const_add (lambda a*l)
    |>.add_const ((zeta a-r a)*Real.log y)).sub
      ((hD.log (D_pos hu hy x).ne').const_mul (zeta a/2))
  convert! hd using 1
  · dsimp [Hx]; ring

lemma hasDerivAt_Hxx {a u x y : ℝ} (hu : 0 ≤ u) (hy : 0 < y) :
    HasDerivAt (fun w => Hx a u w y) (Hxx a u x y) x := by
  have hR : HasDerivAt (fun w : ℝ => R w y) (2*x) x := by
    convert! ((hasDerivAt_id x).pow 2).add_const (y^2) using 1
    simp
  have hD : HasDerivAt (fun w : ℝ => D u w y) (2*x) x := hR.add_const (u/2)
  have hd := (((hasDerivAt_id x).const_mul (r a)).div hR (R_pos x hy).ne').sub
    (((hasDerivAt_id x).const_mul (zeta a)).div hD (D_pos hu hy x).ne')
  convert! hd using 1
  dsimp [Hxx]
  have hnR := (R_pos x hy).ne'
  have hnD := (D_pos hu hy x).ne'
  field_simp
  simp only [R]
  ring

lemma deriv_Fx {a u y l : ℝ} (hu : 0 ≤ u) (hy : 0 < y) :
    deriv (fun x => F a u x y l) = fun x => F a u x y l * Hx a u x y := by
  funext x
  exact (hasDerivAt_Hx hu hy).exp.deriv

lemma deriv_Fxx {a u x y l : ℝ} (hu : 0 ≤ u) (hy : 0 < y) :
    deriv (deriv (fun w => F a u w y l)) x =
      F a u x y l * ((Hx a u x y)^2+Hxx a u x y) := by
  rw [deriv_Fx hu hy]
  have hd := ((hasDerivAt_Hx (a := a) (x := x) (l := l) hu hy).exp).mul
    (hasDerivAt_Hxx (a := a) (x := x) hu hy)
  convert! hd.deriv using 1
  dsimp [F]
  ring

lemma generator_identity {a u x y : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hy : 0 < y) :
    ((Hx a u x y)^2+Hxx a u x y)/2 +
      (-a*x/R x y)*Hx a u x y+(a*y/R x y)*Hy a u x y+
      (a*(x^2-y^2)/(R x y)^2)*lambda a+zeta a/(4*D u x y) =
      -zeta a*residual a u x y/(2*R x y*(D u x y)^2) := by
  have ha' := ha.ne'
  have hR := (R_pos x hy).ne'
  have hD := (D_pos hu hy x).ne'
  have hy' := hy.ne'
  simp only [Hx,Hxx,Hy,lambda,zeta,r,residual]
  field_simp
  simp only [D,R]
  ring

lemma generator_nonpos {a u x y : ℝ} (ha : 1/4 < a) (hu : 0 ≤ u) (hy : 0 < y) :
    ((Hx a u x y)^2+Hxx a u x y)/2 +
      (-a*x/R x y)*Hx a u x y+(a*y/R x y)*Hy a u x y+
      (a*(x^2-y^2)/(R x y)^2)*lambda a+zeta a/(4*D u x y) ≤ 0 := by
  rw [generator_identity (by linarith) hu hy]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (parameters ha).1.le)
      (residual_nonneg ha hu hy x)
  · exact mul_nonneg (mul_nonneg (by norm_num) (R_pos x hy).le) (sq_nonneg _)

end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative

abbrev State := ℝ × ℂ × ℝ

def test (a : ℝ) (q : State) (b : ℝ) : ℝ :=
  F a q.1 (q.2.1.re-b) q.2.1.im q.2.2

def vector (a : ℝ) (q : State) (b : ℝ) : State :=
  (-1, (-(a:ℂ)/(q.2.1-b),a*((q.2.1-b)⁻¹^2).re))

lemma differentiableAt_test (a b : ℝ) {q : State} (hu : 0 ≤ q.1) (hy : 0 < q.2.1.im) :
    DifferentiableAt ℝ (fun q => test a q b) q := by
  have hR := (R_pos (q.2.1.re-b) hy).ne'
  have hD := (D_pos hu hy (q.2.1.re-b)).ne'
  have hy' := hy.ne'
  have hre : DifferentiableAt ℝ (fun q : State => q.2.1.re) q :=
    Complex.reCLM.differentiableAt.comp _ (differentiableAt_fst.comp _ differentiableAt_snd)
  have him : DifferentiableAt ℝ (fun q : State => q.2.1.im) q :=
    Complex.imCLM.differentiableAt.comp _ (differentiableAt_fst.comp _ differentiableAt_snd)
  dsimp [test, F, H, D, R] at *
  fun_prop

end SLEExactGauge.ReverseDerivative
end
end
end
end
end
end
end
end
end
end
end

end OAI
