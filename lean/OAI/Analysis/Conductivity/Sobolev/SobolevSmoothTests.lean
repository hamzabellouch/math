import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevTraceChain

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma continuous_gradient_of_smooth {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
    (hf.continuous_fderiv (by simp))

lemma smoothJet_continuous {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (smoothJet f) := by
  have he : smoothJet f = fun x => jetLiftValue (f x)+jetLiftGradient (gradient f x) := by
    ext x i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [smoothJet,jetLiftValue,jetLiftGradient]
  rw [he]
  exact (jetLiftValue.continuous.comp hf.continuous).add
    (jetLiftGradient.continuous.comp (continuous_gradient_of_smooth hf))

lemma continuous_bound_ball {E : Type*} [NormedAddCommGroup E] {f : R3 → E}
    (hf : Continuous f) : ∃ M : ℝ, 0≤M ∧ ∀ᵐ x ∂ballMeasure, ‖f x‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:R3) 3).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  filter_upwards [ae_restrict_mem (s := ball) measurableSet_ball] with x hx
  exact (hM x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)

lemma smoothJet_memLp {f : R3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    MemLp (smoothJet f) 2 ballMeasure := by
  obtain ⟨M,_,hM⟩ := continuous_bound_ball (smoothJet_continuous hf)
  exact MemLp.of_bound (smoothJet_continuous hf).aestronglyMeasurable M hM

def smoothH1 (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : H1 :=
  ⟨(smoothJet_memLp hf).toLp _, (Submodule.le_topologicalClosure _)
    (Submodule.subset_span ⟨f,hf,smoothJet_memLp hf,rfl⟩)⟩

lemma smoothH1_value (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    weakValue (smoothH1 f hf) =ᵐ[ballMeasure] f := by
  filter_upwards [(smoothJet_memLp hf).coeFn_toLp] with x hx
  exact congrArg jetValue hx

lemma smoothH1_gradient (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    weakGradient (smoothH1 f hf) =ᵐ[ballMeasure] gradient f := by
  filter_upwards [(smoothJet_memLp hf).coeFn_toLp] with x hx
  exact congrArg jetGradient hx

lemma smoothH1_bounded (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ∃ M : ℝ, 0≤M ∧ ∀ᵐ x ∂ballMeasure, |weakValue (smoothH1 f hf) x|≤M := by
  obtain ⟨M,hM,hb⟩ := continuous_bound_ball hf.continuous
  refine ⟨M,hM,?_⟩
  filter_upwards [hb,smoothH1_value f hf] with x hx hy
  simpa only [hy,Real.norm_eq_abs] using hx

lemma smoothH1_mem_H10 (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hs : tsupport f⊆ball) : smoothH1 f hf∈H10 :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span
    ⟨f,hf,hc,hs,smoothJet_memLp hf,rfl⟩)

lemma smoothH1_dense : Dense {u : H1 | u.val∈smoothJets} := by
  intro u
  rw [closure_subtype]
  have he : Subtype.val '' {u : H1 | u.val∈smoothJets}=smoothJets := by
    apply Set.ext; intro z; constructor
    · rintro ⟨u,hu,rfl⟩; exact hu
    · intro hz
      exact ⟨⟨z,(Submodule.le_topologicalClosure _) (Submodule.subset_span hz)⟩,hz,rfl⟩
  rw [he,←H1Space_eq_closure]
  exact u.property

lemma compactH1_dense_H10 {u : H1} (hu : u∈H10) :
    u∈closure {v : H1 | v.val∈compactSmoothJets} := by
  rw [closure_subtype]
  have he : Subtype.val '' {v : H1 | v.val∈compactSmoothJets}=compactSmoothJets := by
    apply Set.ext; intro z; constructor
    · rintro ⟨v,hv,rfl⟩; exact hv
    · intro hz
      rcases hz with ⟨f,hf,hc,hs,hm,rfl⟩
      exact ⟨⟨hm.toLp _, (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨f,hf,hm,rfl⟩)⟩,⟨f,hf,hc,hs,hm,rfl⟩,rfl⟩
  rw [he,←zeroTraceAmbient_eq_closure]
  exact hu

lemma harmonic_of_compact_tests (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C) (u : H1)
    (h : ∀ (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f),
      HasCompactSupport f → tsupport f⊆ball → energy a u (smoothH1 f hf)=0) :
    Harmonic a u := by
  intro v hv
  have hs : {v : H1 | v.val∈compactSmoothJets} ⊆ {v | energyForm a ha C hC hb u v=0} := by
    rintro v ⟨f,hf,hc,hs,hm,he⟩
    have hev : v=smoothH1 f hf := Subtype.ext he
    change energyForm a ha C hC hb u v=0
    rw [hev,energyForm_apply]
    exact h f hf hc hs
  have hc : IsClosed {v | energyForm a ha C hC hb u v=0} :=
    isClosed_eq (energyForm a ha C hC hb u).continuous continuous_const
  rw [←energyForm_apply a ha C hC hb]
  exact (closure_minimal hs hc) (compactH1_dense_H10 hv)

open Set MeasureTheory Filter Topology Real

def inverseBump : ContDiffBump (0:ℝ) := ⟨3/5,3/4,by norm_num,by norm_num⟩
def inverseClip (r : ℝ) : ℝ := inverseBump r*r

def inverseCorrection (r : ℝ) : ℝ := (1+inverseClip r)⁻¹-1

lemma inverseClip_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) inverseClip :=
  inverseBump.contDiff.mul contDiff_id

lemma inverseClip_bound (r : ℝ) : |inverseClip r|≤3/4 := by
  by_cases hr : |r|<3/4
  · calc
      |inverseClip r|=inverseBump r*|r| := by
        rw [inverseClip,abs_mul,abs_of_nonneg inverseBump.nonneg]
      _ ≤ 1*|r| := mul_le_mul_of_nonneg_right inverseBump.le_one (abs_nonneg _)
      _ ≤ 3/4 := by simpa only [one_mul] using hr.le
  · have hb : inverseBump r=0 := inverseBump.zero_of_le_dist (by
      change (3/4:ℝ)≤dist r 0; simpa only [dist_zero_right,Real.norm_eq_abs] using le_of_not_gt hr)
    norm_num [inverseClip,hb]

lemma inverseClip_denominator_pos (r : ℝ) : 0<1+inverseClip r := by
  have h := (abs_le.mp (inverseClip_bound r)).1
  linarith

lemma inverseCorrection_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) inverseCorrection :=
  ((contDiff_const.add inverseClip_smooth).inv (fun r => (inverseClip_denominator_pos r).ne')).sub contDiff_const

lemma inverseCorrection_compact : HasCompactSupport inverseCorrection := by
  apply inverseBump.hasCompactSupport.mono
  intro r hr
  contrapose! hr
  simp only [Function.mem_support,not_not] at hr ⊢
  simp [inverseCorrection,inverseClip,hr]

lemma inverseCorrection_zero : inverseCorrection 0=0 := by
  simp [inverseCorrection,inverseClip]

def inverseOperation : SmoothLipZero := SmoothLipZero.ofCompact inverseCorrection
  inverseCorrection_smooth inverseCorrection_compact inverseCorrection_zero

lemma inverseCorrection_eventually {r : ℝ} (hr : |r|≤1/2) :
    inverseCorrection =ᶠ[𝓝 r] fun s => (1+s)⁻¹-1 := by
  have hb : r ∈ Metric.ball 0 inverseBump.rIn := by
    change dist r 0 < (3/5:ℝ)
    rw [dist_zero_right,Real.norm_eq_abs]
    linarith
  filter_upwards [inverseBump.eventuallyEq_one_of_mem_ball hb] with s hs
  simp only [inverseCorrection,inverseClip,hs,Pi.one_apply,one_mul]

lemma inverseCorrection_eq {r : ℝ} (hr : |r|≤1/2) : inverseCorrection r=(1+r)⁻¹-1 :=
  (inverseCorrection_eventually hr).eq_of_nhds

lemma inverseCorrection_deriv {r : ℝ} (hr : |r|≤1/2) :
    deriv inverseCorrection r= -((1+r)^2)⁻¹ := by
  rw [(inverseCorrection_eventually hr).deriv_eq]
  have hn : (1:ℝ)+r≠0 := by have := (abs_le.mp hr).1; linarith
  simpa only [one_div,neg_div,pow_two,id_eq,Pi.inv_apply] using
    ((((hasDerivAt_id r).const_add 1).inv hn).sub_const 1).deriv

lemma inverseCorrection_bound {r : ℝ} (hr : |r|≤1/2) : |inverseCorrection r|≤1 := by
  rw [inverseCorrection_eq hr]
  have hlo := (abs_le.mp hr).1
  have hpos : 0<1+r := by linarith
  rw [abs_le]
  constructor
  · have h := inv_pos.mpr hpos; linarith
  · have hle : (1+r)⁻¹≤2 := (inv_le_comm₀ hpos (by norm_num)).mpr (by norm_num; linarith)
    linarith

theorem inverseOperation_spec {w : H1} (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    (∀ᵐ x ∂ballMeasure, weakValue (inverseOperation.onH1 w) x=(1+weakValue w x)⁻¹-1) ∧
    (∀ᵐ x ∂ballMeasure, weakGradient (inverseOperation.onH1 w) x=
      (-((1+weakValue w x)^2)⁻¹) • weakGradient w x) ∧
    (∀ᵐ x ∂ballMeasure, |weakValue (inverseOperation.onH1 w) x|≤1) ∧
    (w∈H10 → inverseOperation.onH1 w∈H10) := by
  refine ⟨?_,?_,?_,fun h => inverseOperation.preserves_H10 h⟩
  · filter_upwards [inverseOperation.onH1_value w,hw] with x hx h
    exact hx.trans (inverseCorrection_eq h)
  · filter_upwards [inverseOperation.onH1_gradient w,hw] with x hx h
    exact hx.trans (by rw [show deriv inverseOperation (weakValue w x)= -((1+weakValue w x)^2)⁻¹ from
      inverseCorrection_deriv h])
  · filter_upwards [inverseOperation.onH1_value w,hw] with x hx h
    change |jetValue ((inverseOperation.onH1 w).val x)|≤1
    rw [hx]; exact inverseCorrection_bound h

end ScalarConductivity

end

end OAI
