import Mathlib
import OAI.Geometry.CubicTorus.Curvature.NormalCurvatureScalar

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def smoothScalarSeparatedTrunc (f : smoothPeriodicScalars) (n : ℕ) : smoothPeriodicScalars :=
  ⟨separatedPositiveTrunc n ∘ f.val,(separatedPositiveTrunc_contDiff n).comp f.property.1,
    fun m x ↦ by simp only [Function.comp_apply,f.property.2]⟩

lemma gradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (x : Cover) :
    gradient (smoothScalarSeparatedTrunc f n).val x=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val x-nodalEpsilon n)) • gradient f.val x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  have h := (positiveTrunc_hasDerivAt n (f.val x-nodalEpsilon n)).hasFDerivAt.comp x
    ((f.property.1.differentiable (by simp) x).hasFDerivAt.sub_const (nodalEpsilon n))
  change (fderiv ℝ (positiveTrunc n ∘ fun y ↦ f.val y-nodalEpsilon n) x) v=_
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma smoothScalarGradient_separatedPositiveTrunc (f : smoothPeriodicScalars) (n : ℕ) (z : NormalBundle) :
    smoothScalarGradient (smoothScalarSeparatedTrunc f n) z=
      positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z := by
  change gradient (smoothScalarSeparatedTrunc f n).val z.1-
    ⟪(z.2 : Cover),gradient (smoothScalarSeparatedTrunc f n).val z.1⟫ • (z.2 : Cover)=_
  rw [gradient_separatedPositiveTrunc,real_inner_smul_right]
  change _=positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) •
    (gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover))
  rw [smul_sub,smul_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nodalSurfaceValue (f : smoothPeriodicScalars) (D : Set Torus) : NormalBundle → ℝ :=
  (normalProjection ⁻¹' D).indicator (smoothScalarValue f)
def nodalSurfaceGradient (f : smoothPeriodicScalars) (D : Set Torus) : NormalBundle → Cover :=
  (normalProjection ⁻¹' D).indicator (smoothScalarGradient f)

lemma nodalSurfaceValue_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : MemLp (nodalSurfaceValue f D) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarValue f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator (hD.preimage normalProjection_continuous.measurable)
lemma nodalSurfaceGradient_memLp (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : MemLp (nodalSurfaceGradient f D) 2 (μ : Measure NormalBundle) :=
  ((smoothScalarGradient f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).indicator (hD.preimage normalProjection_continuous.measurable)

def nodalSurfaceJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) : SurfaceJet μ :=
  ((nodalSurfaceValue_memLp μ f D hD).toLp (nodalSurfaceValue f D),
    (nodalSurfaceGradient_memLp μ f D hD).toLp (nodalSurfaceGradient f D))

lemma smoothScalarGradient_of_constant_germ (f : smoothPeriodicScalars) {x : Cover} {c : ℝ}
    (hf : ∀ᶠ y in 𝓝 x,f.val y=c) (ν : NormalSphere) :
    gradient f.val x-⟪(ν : Cover),gradient f.val x⟫ • (ν : Cover)=0 := by
  have he : f.val=ᶠ[𝓝 x] fun _ ↦ c := hf
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hg : gradient f.val x=0 := by simp [gradient,hd]
  simp [hg]

theorem nodal_restriction_smooth_approximants (f : smoothPeriodicScalars)
    (S D : Set Torus)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    ∃ g : ℕ → smoothPeriodicScalars,∀ n (z : NormalBundle),normalProjection z∈S →
      (smoothScalarValue (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z) ∧
      (smoothScalarGradient (g n) z=
        (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦
          positiveTruncCoeff (((n:ℝ)+1)*(f.val w.1-nodalEpsilon n)) • smoothScalarGradient f w) z) := by
  classical
  have hsep (n : ℕ) := exists_periodic_smooth_separator (hA n) (hB n)
    (show Disjoint {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}
      {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)} from
        Set.disjoint_left.mpr (fun a ha hb ↦ hb.2.1 ha.2.1))
  choose φ hφ hp hb hone hzero using hsep
  let φs (n : ℕ) : smoothPeriodicScalars := ⟨φ n,hφ n,hp n⟩
  let g (n : ℕ) := smoothScalarMul (φs n) (smoothScalarSeparatedTrunc f n)
  refine ⟨g,?_⟩
  intro n z hz
  have hv : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hgrad : smoothScalarGradient (g n) z=
      separatedPositiveTrunc n (f.val z.1) • smoothScalarGradient (φs n) z+
      φ n z.1 • (positiveTruncCoeff (((n:ℝ)+1)*(f.val z.1-nodalEpsilon n)) • smoothScalarGradient f z) := by
    rw [smoothScalarGradient_mul,smoothScalarGradient_separatedPositiveTrunc]
    rfl
  have hval : smoothScalarValue (g n) z=φ n z.1*separatedPositiveTrunc n (f.val z.1) := rfl
  by_cases hl : f.val z.1≤nodalEpsilon n
  · obtain ⟨ht,hc⟩ := separatedPositiveTrunc_zero n hl
    rw [hval,hgrad,ht,hc]
    constructor <;> by_cases hd : normalProjection z∈D <;> simp [hd,ht,hc]
  · have ha : nodalEpsilon n≤f.val (representative (normalProjection z)) := by rw [hv]; exact (not_le.mp hl).le
    by_cases hd : normalProjection z∈D
    · have hh := hone n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=1 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]
    · have hh := hzero n (z.1 : Cover) ⟨hz,hd,ha⟩
      have hφv : φ n z.1=0 := hh.self_of_nhds
      have hφg : smoothScalarGradient (φs n) z=0 :=
        smoothScalarGradient_of_constant_germ (φs n) hh z.2
      rw [hval,hgrad,hφv,hφg]
      constructor <;> simp [hd]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceL2_continuous_bounded_convergence_ae {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : FiniteMeasure NormalBundle) (f : ℕ → C(NormalBundle,F))
    (g : NormalBundle → F) (hg : MemLp g 2 (μ : Measure NormalBundle))
    {M : ℝ} (hM : 0≤M) (hfb : ∀ n,∀ᵐ z ∂(μ : Measure NormalBundle),‖f n z‖≤M)
    (hgb : ∀ᵐ z ∂(μ : Measure NormalBundle),‖g z‖≤M)
    (ht : ∀ᵐ z ∂(μ : Measure NormalBundle),Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n))
      atTop (𝓝 (hg.toLp g)) := by
  have hf (n : ℕ) : MemLp (f n) 2 (μ : Measure NormalBundle) :=
    (f n).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (n : ℕ) : ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ (f n)=
      (hf n).toLp (f n) := by
    apply Lp.ext
    exact (f n).coeFn_toLp (μ : Measure NormalBundle) |>.trans (hf n).coeFn_toLp.symm
  simpa only [he] using surfaceL2_bounded_convergence μ (fun n ↦ f n) g hf hg hM hfb hgb ht

theorem nodalSurfaceJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (S D : Set Torus) (hD : MeasurableSet D)
    (hpos : ∀ a∈D,0<f.val (representative a))
    (hμ : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈S)
    (hA : ∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)})
    (hB : ∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) :
    nodalSurfaceJet μ f D hD∈surfaceH1 μ := by
  classical
  obtain ⟨g,hg⟩ := nodal_restriction_smooth_approximants f S D hA hB
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have htval : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).1) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).1) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarValue (g n))
      (nodalSurfaceValue f D) (nodalSurfaceValue_memLp μ f D hD)
      (norm_nonneg (smoothScalarValue f))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).1]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact (separatedPositiveTrunc_bound n (f.val z.1)).trans ((smoothScalarValue f).norm_coe_le_norm z)
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simpa only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false] using
          (smoothScalarValue f).norm_coe_le_norm z
      · simp only [nodalSurfaceValue,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        exact norm_nonneg _
    · filter_upwards [hμ] with z hz
      have he : (fun n ↦ smoothScalarValue (g n) z)=
          fun n ↦ (normalProjection ⁻¹' D).indicator (fun w : NormalBundle ↦ separatedPositiveTrunc n (f.val w.1)) z :=
        funext (fun n ↦ (hg n z hz).1)
      rw [he]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,nodalSurfaceValue]
        change Tendsto (fun n ↦ separatedPositiveTrunc n (f.val z.1)) atTop (𝓝 (f.val z.1))
        simpa only [max_eq_left hp.le] using
          (separatedPositiveTrunc_tendsto (f.val z.1)).1
      · simpa only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,ite_false,nodalSurfaceValue] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  obtain ⟨K,hK,hKb⟩ := positiveTruncCoeff_bounded
  have htgrad : Tendsto (fun n ↦ (surfaceSmoothJet μ (g n)).2) atTop
      (𝓝 (nodalSurfaceJet μ f D hD).2) := by
    apply surfaceL2_continuous_bounded_convergence_ae μ (fun n ↦ smoothScalarGradient (g n))
      (nodalSurfaceGradient f D) (nodalSurfaceGradient_memLp μ f D hD)
      (mul_nonneg (show 0≤K+1 by linarith) (norm_nonneg (smoothScalarGradient f)))
    · intro n
      filter_upwards [hμ] with z hz
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,norm_smul]
        exact (mul_le_mul (hKb _) ((smoothScalarGradient f).norm_coe_le_norm z)
          (norm_nonneg _) hK).trans (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · apply ae_of_all
      intro z
      by_cases hd : normalProjection z∈D
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_true]
        exact ((smoothScalarGradient f).norm_coe_le_norm z).trans
          (by nlinarith [norm_nonneg (smoothScalarGradient f)])
      · simp only [nodalSurfaceGradient,Set.indicator_apply,Set.mem_preimage,hd,ite_false,norm_zero]
        positivity
    · filter_upwards [hμ] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [(separatedPositiveTrunc_tendsto (f.val z.1)).2] with n hn
      rw [(hg n z hz).2]
      by_cases hd : normalProjection z∈D
      · have hp : 0<f.val z.1 := by rw [← hv z]; exact hpos _ hd
        simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_true,hn,ite_eq_left hp,one_smul,nodalSurfaceGradient]
      · simp only [Set.indicator_apply,Set.mem_preimage,hd,ite_false,nodalSurfaceGradient]
  apply (surfaceSmoothJet μ).range.isClosed_topologicalClosure.mem_of_tendsto
    (htval.prodMk_nhds htgrad)
  filter_upwards [] with n
  exact subset_closure ⟨g n,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def IsPositiveNodalPiece (f : smoothPeriodicScalars) (S D : Set Torus) : Prop :=
  (∃ U : Set Torus,IsOpen U ∧ D={a | a∈S ∧ 0<f.val (representative a)}∩U) ∧
  (∃ C : Set Torus,IsClosed C ∧ D={a | a∈S ∧ 0<f.val (representative a)}∩C)

lemma positiveNodalPiece_superlevels (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsClosed S) (hD : IsPositiveNodalPiece f S D) :
    MeasurableSet D ∧ (∀ a∈D,0<f.val (representative a)) ∧
    (∀ n : ℕ,IsCompact {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}) ∧
    (∀ n : ℕ,IsClosed {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  have hP : MeasurableSet {a : Torus | a∈S ∧ 0<f.val (representative a)} :=
    hS.measurableSet.inter (isOpen_lt continuous_const hf).measurableSet
  refine ⟨by rw [hDU]; exact hP.inter hU.measurableSet,?_,?_,?_⟩
  · intro a ha
    rw [hDU] at ha
    exact ha.1.2
  · intro n
    have he : {a | a∈S ∧ a∈D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩C∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        rw [hDC] at hd
        exact ⟨⟨ha,hd.2⟩,hv⟩
      · rintro ⟨⟨ha,hc⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        rw [hDC]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hc⟩
    rw [he]
    exact ((hS.inter hC).inter (isClosed_le continuous_const hf)).isCompact
  · intro n
    have he : {a | a∈S ∧ a∉D ∧ nodalEpsilon n≤f.val (representative a)}=
        S∩Uᶜ∩{a | nodalEpsilon n≤f.val (representative a)} := by
      ext a
      constructor
      · rintro ⟨ha,hd,hv⟩
        refine ⟨⟨ha,?_⟩,hv⟩
        intro hu
        apply hd
        rw [hDU]
        exact ⟨⟨ha,(nodalEpsilon_pos n).trans_le hv⟩,hu⟩
      · rintro ⟨⟨ha,hu⟩,hv⟩
        refine ⟨ha,?_,hv⟩
        intro hd
        rw [hDU] at hd
        exact hu hd.2
    rw [he]
    exact (hS.inter hU.isClosed_compl).inter (isClosed_le continuous_const hf)

theorem isMinimizerAt_positive_nodal_piece_H1 {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) :
    ∃ hDm : MeasurableSet D,nodalSurfaceJet μ f D hDm∈surfaceH1 μ := by
  obtain ⟨hDm,hpos,hA,hB⟩ := positiveNodalPiece_superlevels f isClosed_frontier hD
  refine ⟨hDm,nodalSurfaceJet_mem_surfaceH1 μ f (frontier (openRepresentative E)) D hDm hpos ?_ hA hB⟩
  exact normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_nodal_restriction (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceJacobiB μ q (surfaceSmoothJet μ f) (nodalSurfaceJet μ f D hD)=
      surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD) := by
  classical
  have hv := (smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hpv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hpg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  unfold surfaceJacobiB
  congr 1
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg,hpg] with z hgz hpgz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hgz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hpgz
    rw [hgz,hpgz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceGradient,hd]
  · rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    have hmf := Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ f).1
    have hmp := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
    filter_upwards [hv,hpv,hmf,hmp] with z hvz hpvz hmfz hmpz
    change (surfaceSmoothJet μ f).1 z=f.val z.1 at hvz
    change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hpvz
    change (surfaceMultiplier μ q (surfaceSmoothJet μ f).1) z=_ at hmfz
    change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmpz
    rw [hmfz,hmpz]
    simp only [smul_eq_mul,Pi.mul_apply,hvz,hpvz]
    by_cases hd : normalProjection z∈D <;> simp [nodalSurfaceValue,smoothScalarValue,hd]

lemma surfaceJacobiB_disjoint_nodal (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f g : smoothPeriodicScalars)
    (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) (hDA : Disjoint D A) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ g A hA)=0 := by
  classical
  have hdv := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  have hdg := (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp
  have hav := (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp
  have hag := (nodalSurfaceGradient_memLp μ g A hA).coeFn_toLp
  unfold surfaceJacobiB
  have hx : ⟪(nodalSurfaceJet μ f D hD).2,(nodalSurfaceJet μ g A hA).2⟫=0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hdg,hag] with z hdz haz
    change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hdz
    change (nodalSurfaceJet μ g A hA).2 z=nodalSurfaceGradient g A z at haz
    rw [hdz,haz]
    by_cases hd : normalProjection z∈D
    · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
      simp [nodalSurfaceGradient,ha]
    · simp [nodalSurfaceGradient,hd]
  rw [hx,zero_sub,neg_eq_zero]
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hm := Lp.coeFn_lpSMul (r := 2) q (nodalSurfaceJet μ f D hD).1
  filter_upwards [hdv,hav,hm] with z hdz haz hmz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  change (nodalSurfaceJet μ g A hA).1 z=nodalSurfaceValue g A z at haz
  change (surfaceMultiplier μ q (nodalSurfaceJet μ f D hD).1) z=_ at hmz
  rw [hmz]
  simp only [smul_eq_mul,Pi.mul_apply,hdz,haz]
  by_cases hd : normalProjection z∈D
  · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
    simp [nodalSurfaceValue,ha]
  · simp [nodalSurfaceValue,hd]

lemma nodalSurfaceJet_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) (hm : nodalSurfaceJet μ f D hD∈surfaceH1 μ)
    (hj : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) w=0) :
    surfaceJacobiB μ q (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ f D hD)=0 := by
  rw [← surfaceJacobiB_nodal_restriction]
  exact hj _ hm

namespace Periodic

theorem isMinimizerAt_translation_selected_nodal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      ∀ (v : Cover) (D : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        ∃ hD : MeasurableSet D,
          nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD∈surfaceH1 μ ∧
          surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD)
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD)=0 := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,hj,_⟩ := isMinimizerAt_H1_translation_jacobi hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,hs,?_⟩
  intro v D hD
  obtain ⟨hDm,hm⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ
    (directionalNormalScalar N hN hp v) hD
  refine ⟨hDm,hm,nodalSurfaceJet_null μ _ _ D hDm hm ?_⟩
  exact directionalNormalScalar_global_jacobi μ N hN hp (fun i ↦ (hj i).2) v

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceMean_nodal (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    surfaceMean μ (nodalSurfaceJet μ f D hD)=∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle) := by
  change ⟪(surfaceOne μ).1,(nodalSurfaceJet μ f D hD).1⟫=_
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv := (smoothScalarValue smoothScalarOne).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hd := (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp
  filter_upwards [hv,hd] with z hvz hdz
  change (surfaceOne μ).1 z=1 at hvz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  rw [hvz,hdz]
  simp

theorem isMinimizerAt_nodal_mean_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    0<surfaceMean μ (nodalSurfaceJet μ f D hDm) := by
  classical
  have hv (z : NormalBundle) : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 z.1
  have hpos := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1
  have hp (z : NormalBundle) : 0≤nodalSurfaceValue f D z := by
    by_cases hd : normalProjection z∈D
    · have hh := hpos _ hd
      rw [hv z] at hh
      simpa [nodalSurfaceValue,hd,smoothScalarValue] using hh.le
    · simp [nodalSurfaceValue,hd]
  rw [surfaceMean_nodal]
  by_contra! h
  have hz : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle))=0 :=
    le_antisymm h (integral_nonneg hp)
  have hae := (integral_eq_zero_iff_of_nonneg hp
    ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))).mp hz
  obtain ⟨U,hU,hDU⟩ := hD.1
  obtain ⟨a,ha⟩ := hDn
  have ha' := ha
  rw [hDU] at ha'
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  let W : Set Torus := U∩{a : Torus | 0<f.val (representative a)}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_const hf)
  have haW : a∈W := ⟨ha'.2,ha'.1.2⟩
  obtain ⟨φ,hφ,hper,hb,⟨T,hT,haT,hone⟩,hzero⟩ := exists_periodic_local_cutoff a hW haW
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hφae : ∀ᵐ z ∂(μ : Measure NormalBundle),φ z.1=0 := by
    filter_upwards [hbd,hae] with z hzbd hz0
    by_cases hzW : normalProjection z∈W
    · have hzD : normalProjection z∈D := by
        rw [hDU]
        exact ⟨⟨hzbd,hzW.2⟩,hzW.1⟩
      have hfz : 0<f.val z.1 := by
        have hh : 0<f.val (representative (normalProjection z)) := hzW.2
        rw [hv z] at hh
        exact hh
      have hf0 : f.val z.1=0 := by simpa [nodalSurfaceValue,hzD,smoothScalarValue] using hz0
      exact False.elim (hfz.ne' hf0)
    · exact (hzero z.1 hzW).self_of_nhds
  have he := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ hφ.continuous
    (continuous_const (y := (0 : ℝ))) hper (fun _ _ ↦ rfl) hφae (representative a)
    (by simpa only [quotientMap_representative] using ha'.1.1)
  have hh := (hone (representative a) (by simpa only [quotientMap_representative] using haT)).self_of_nhds
  change φ (representative a)=(0 : ℝ) at he
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceNodalBalance (μ : FiniteMeasure NormalBundle) (u v : SurfaceJet μ) : SurfaceJet μ :=
  surfaceMean μ v • u+(-surfaceMean μ u) • v

lemma surfaceNodalBalance_mean (μ : FiniteMeasure NormalBundle) (u v : SurfaceJet μ) :
    surfaceMean μ (surfaceNodalBalance μ u v)=0 := by
  simp only [surfaceNodalBalance,map_add,map_smul,smul_eq_mul]
  ring

lemma surfaceNodalBalance_mem (μ : FiniteMeasure NormalBundle) {u v : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hv : v∈surfaceH1 μ) : surfaceNodalBalance μ u v∈surfaceH1 μ :=
  (surfaceH1 μ).add_mem ((surfaceH1 μ).smul_mem _ hu) ((surfaceH1 μ).smul_mem _ hv)

lemma surfaceNodalBalance_null (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u v : SurfaceJet μ}
    (hu : surfaceJacobiB μ q u u=0) (hv : surfaceJacobiB μ q v v=0)
    (huv : surfaceJacobiB μ q u v=0) :
    surfaceJacobiB μ q (surfaceNodalBalance μ u v) (surfaceNodalBalance μ u v)=0 := by
  have hvu : surfaceJacobiB μ q v u=0 := by rw [surfaceJacobiB_symm]; exact huv
  unfold surfaceNodalBalance
  rw [surfaceJacobiB_add_left,surfaceJacobiB_smul_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_symm μ q u,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,hu,hvu,
    surfaceJacobiB_symm μ q v,surfaceJacobiB_add_left,surfaceJacobiB_smul_left,
    surfaceJacobiB_smul_left,huv,hv]
  ring

lemma nodalSurfaceJet_value_orthogonal (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hDA : Disjoint D A) :
    ⟪(nodalSurfaceJet μ f D hD).1,(nodalSurfaceJet μ g A hA).1⟫=0 := by
  classical
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp] with z hdz haz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hdz
  change (nodalSurfaceJet μ g A hA).1 z=nodalSurfaceValue g A z at haz
  rw [hdz,haz]
  by_cases hd : normalProjection z∈D
  · have ha : normalProjection z∉A := fun ha ↦ Set.disjoint_left.mp hDA hd ha
    simp [nodalSurfaceValue,ha]
  · simp [nodalSurfaceValue,hd]

lemma surfaceNodalBalance_ne_zero (μ : FiniteMeasure NormalBundle) {u v : SurfaceJet μ}
    (hu : surfaceMean μ u≠0) (hv : surfaceMean μ v≠0) (huv : ⟪u.1,v.1⟫=0) :
    surfaceNodalBalance μ u v≠0 := by
  intro he
  have hval : (surfaceNodalBalance μ u v).1=0 := congrArg Prod.fst he
  have hx : ⟪(surfaceNodalBalance μ u v).1,u.1⟫=0 := by rw [hval]; simp
  change ⟪surfaceMean μ v • u.1+(-surfaceMean μ u) • v.1,u.1⟫=0 at hx
  have hvu : ⟪v.1,u.1⟫=0 := (real_inner_comm u.1 v.1).trans huv
  simp only [inner_add_left,real_inner_smul_left,hvu,mul_zero,add_zero] at hx
  have hz : ⟪u.1,u.1⟫=0 := (mul_eq_zero.mp (by simpa using hx)).resolve_left hv
  have hu1 : u.1=0 := inner_self_eq_zero.mp hz
  apply hu
  change ⟪(surfaceOne μ).1,u.1⟫=0
  rw [hu1]
  simp

lemma nodalSurfaceJet_zero_outside (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) (D U : Set Torus) (hD : MeasurableSet D) (hUD : Disjoint U D) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (nodalSurfaceJet μ f D hD).1 z=0 ∧ (nodalSurfaceJet μ f D hD).2 z=0 := by
  classical
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceGradient_memLp μ f D hD).coeFn_toLp] with z hvz hgz hz
  have hd : normalProjection z∉D := fun hd ↦ Set.disjoint_left.mp hUD hz hd
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hvz
  change (nodalSurfaceJet μ f D hD).2 z=nodalSurfaceGradient f D z at hgz
  rw [hvz,hgz]
  simp [nodalSurfaceValue,nodalSurfaceGradient,hd]

lemma surfaceNodalBalance_zero_patch (μ : FiniteMeasure NormalBundle)
    {u v : SurfaceJet μ} {U : Set Torus}
    (hu : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0)
    (hv : ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → v.1 z=0 ∧ v.2 z=0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U →
      (surfaceNodalBalance μ u v).1 z=0 ∧ (surfaceNodalBalance μ u v).2 z=0 := by
  have h1 := Lp.coeFn_add (surfaceMean μ v • u.1) ((-surfaceMean μ u) • v.1)
  have h2 := Lp.coeFn_add (surfaceMean μ v • u.2) ((-surfaceMean μ u) • v.2)
  filter_upwards [hu,hv,h1,h2,Lp.coeFn_smul (surfaceMean μ v) u.1,
    Lp.coeFn_smul (-surfaceMean μ u) v.1,Lp.coeFn_smul (surfaceMean μ v) u.2,
    Lp.coeFn_smul (-surfaceMean μ u) v.2] with z huz hvz h1z h2z h3z h4z h5z h6z hz
  obtain ⟨huv,hug⟩ := huz hz
  obtain ⟨hvv,hvg⟩ := hvz hz
  constructor
  · change (surfaceMean μ v • u.1+(-surfaceMean μ u) • v.1) z=0
    rw [h1z]
    simp only [Pi.add_apply,h3z,h4z,Pi.smul_apply,huv,hvv,smul_zero,add_zero]
  · change (surfaceMean μ v • u.2+(-surfaceMean μ u) • v.2) z=0
    rw [h2z]
    simp only [Pi.add_apply,h5z,h6z,Pi.smul_apply,hug,hvg,smul_zero,add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_two_nodal_balance {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ (v w : Cover) (D A : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp w) (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → Disjoint D A →
        ∃ (hD : MeasurableSet D) (hA : MeasurableSet A),
          let u := surfaceNodalBalance μ
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD)
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp w) A hA)
          u∈surfaceH1 μ ∧ u≠0 ∧ surfaceMean μ u=0 ∧
          surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 ∧
          ∀ U : Set Torus,IsOpen U → (U∩frontier (openRepresentative E)).Nonempty →
            Disjoint U D → Disjoint U A →
            ∀ t∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u t=0 := by
  obtain ⟨μ,N,hN,hp,hμ,hae,hs,hpiece⟩ := isMinimizerAt_translation_selected_nodal hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,?_⟩
  intro v w D A hD hA hDn hAn hDA
  obtain ⟨hDm,hdmem,hdnull⟩ := hpiece v D hD
  obtain ⟨hAm,hamem,hanull⟩ := hpiece w A hA
  let d := nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hDm
  let a := nodalSurfaceJet μ (directionalNormalScalar N hN hp w) A hAm
  have hdpos : 0<surfaceMean μ d :=
    isMinimizerAt_nodal_mean_pos hV hE hmin hμ _ hDm hD hDn
  have hapos : 0<surfaceMean μ a :=
    isMinimizerAt_nodal_mean_pos hV hE hmin hμ _ hAm hA hAn
  have horth : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) d a=0 :=
    surfaceJacobiB_disjoint_nodal μ _ _ _ D A hDm hAm hDA
  have hmem : surfaceNodalBalance μ d a∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hmean : surfaceMean μ (surfaceNodalBalance μ d a)=0 := surfaceNodalBalance_mean μ d a
  have hnull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceNodalBalance μ d a) (surfaceNodalBalance μ d a)=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull horth
  refine ⟨hDm,hAm,hmem,?_,hmean,hnull,?_⟩
  · exact surfaceNodalBalance_ne_zero μ hdpos.ne' hapos.ne'
      (nodalSurfaceJet_value_orthogonal μ _ _ D A hDm hAm hDA)
  · intro U hU hUn hUD hUA
    exact isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ _ hs
      hmem hmean hnull hU hUn (surfaceNodalBalance_zero_patch μ
        (nodalSurfaceJet_zero_outside μ _ D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ _ A U hAm hUA))

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def positiveBoundaryLocus (f : smoothPeriodicScalars) (S : Set Torus) : Set S :=
  {a | 0<f.val (representative a.val)}

def positiveBoundaryDomain (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : Set Torus :=
  (fun b : positiveBoundaryLocus f S ↦ b.val.val) '' connectedComponent a

lemma isOpen_positiveBoundaryLocus (f : smoothPeriodicScalars) (S : Set Torus) :
    IsOpen (positiveBoundaryLocus f S) := by
  apply isOpen_lt continuous_const
  exact (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val

lemma positiveBoundaryDomain_nonempty (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : (positiveBoundaryDomain f S a).Nonempty :=
  ⟨a.val.val,a,mem_connectedComponent,rfl⟩

lemma positiveBoundaryDomain_isPositiveNodalPiece (f : smoothPeriodicScalars) (S : Set Torus)
    [LocallyConnectedSpace S] (a : positiveBoundaryLocus f S) :
    IsPositiveNodalPiece f S (positiveBoundaryDomain f S a) := by
  let : LocallyConnectedSpace (positiveBoundaryLocus f S) :=
    (isOpen_positiveBoundaryLocus f S).locallyConnectedSpace
  let g : positiveBoundaryLocus f S → Torus := fun b ↦ b.val.val
  have hg : Topology.IsInducing g :=
    (Topology.IsInducing.subtypeVal (t := S)).comp
      (Topology.IsInducing.subtypeVal (t := positiveBoundaryLocus f S))
  have hr : Set.range g={b : Torus | b∈S ∧ 0<f.val (representative b)} := by
    ext b
    constructor
    · rintro ⟨c,rfl⟩; exact ⟨c.val.property,c.property⟩
    · rintro ⟨hS,hp⟩; exact ⟨⟨⟨b,hS⟩,hp⟩,rfl⟩
  obtain ⟨U,hU,hUeq⟩ := hg.isOpen_iff.mp (isOpen_connectedComponent (x := a))
  obtain ⟨C,hC,hCeq⟩ := hg.isClosed_iff.mp (isClosed_connectedComponent (x := a))
  constructor
  · refine ⟨U,hU,?_⟩
    change g '' connectedComponent a=_
    rw [← hUeq,image_preimage_eq_inter_range,hr,inter_comm]
  · refine ⟨C,hC,?_⟩
    change g '' connectedComponent a=_
    rw [← hCeq,image_preimage_eq_inter_range,hr,inter_comm]

theorem isMinimizerAt_actual_nodal_piece {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (f : smoothPeriodicScalars)
    (a : positiveBoundaryLocus f (frontier (openRepresentative E))) :
    IsPositiveNodalPiece f (frontier (openRepresentative E))
      (positiveBoundaryDomain f (frontier (openRepresentative E)) a) := by
  let := isMinimizerAt_boundary_locallyConnected hV hE hmin
  exact positiveBoundaryDomain_isPositiveNodalPiece f _ a

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_actual_translation_nodal_domains {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      ∀ (v : Cover) (a : positiveBoundaryLocus (directionalNormalScalar N hN hp v)
        (frontier (openRepresentative E))),
        let D := positiveBoundaryDomain (directionalNormalScalar N hN hp v)
          (frontier (openRepresentative E)) a
        ∃ hD : MeasurableSet D,
          nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD∈surfaceH1 μ ∧
          0<surfaceMean μ (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD) ∧
          surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD)
            (nodalSurfaceJet μ (directionalNormalScalar N hN hp v) D hD)=0 := by
  obtain ⟨μ,N,hN,hp,hμ,hae,hs,hpiece⟩ := isMinimizerAt_translation_selected_nodal hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,hs,?_⟩
  intro v a
  have hd := isMinimizerAt_actual_nodal_piece hV hE hmin (directionalNormalScalar N hN hp v) a
  obtain ⟨hD,hm,hnull⟩ := hpiece v _ hd
  refine ⟨hD,hm,?_,hnull⟩
  exact isMinimizerAt_nodal_mean_pos hV hE hmin hμ _ hD hd
    (positiveBoundaryDomain_nonempty _ _ a)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_open_patch (f : smoothPeriodicScalars) (S C : Set Torus)
    (hC : IsPositiveNodalPiece f S C) (hCn : C.Nonempty) :
    ∃ U : Set Torus,IsOpen U ∧ U∩S=C ∧ (U∩S).Nonempty := by
  obtain ⟨U,hU,hCU⟩ := hC.1
  have hf : Continuous (fun a : Torus ↦ f.val (representative a)) :=
    continuous_periodic_descent f.property.1.continuous f.property.2
  refine ⟨U∩{a | 0<f.val (representative a)},hU.inter (isOpen_lt continuous_const hf),?_,?_⟩
  · rw [hCU]
    ext a
    simp only [mem_inter_iff,mem_ofPred_eq]
    tauto
  · obtain ⟨a,ha⟩ := hCn
    rw [hCU] at ha
    exact ⟨a,⟨ha.2,ha.1.2⟩,ha.1.1⟩

lemma positiveNodalPiece_unused_patch (f : smoothPeriodicScalars) (S C D A : Set Torus)
    (hC : IsPositiveNodalPiece f S C) (hCn : C.Nonempty)
    (hD : D⊆S) (hA : A⊆S) (hCD : Disjoint C D) (hCA : Disjoint C A) :
    ∃ U : Set Torus,IsOpen U ∧ (U∩S).Nonempty ∧ Disjoint U D ∧ Disjoint U A := by
  obtain ⟨U,hU,hUS,hUn⟩ := positiveNodalPiece_open_patch f S C hC hCn
  refine ⟨U,hU,hUn,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro a ha hd
    have hc : a∈C := by rw [← hUS]; exact ⟨ha,hD hd⟩
    exact Set.disjoint_left.mp hCD hc hd
  · apply Set.disjoint_left.mpr
    intro a ha hd
    have hc : a∈C := by rw [← hUS]; exact ⟨ha,hA hd⟩
    exact Set.disjoint_left.mp hCA hc hd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_three_nodal_weak_obstruction {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ (v w t : Cover) (D A C : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp w) (frontier (openRepresentative E)) A →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp t) (frontier (openRepresentative E)) C →
        D.Nonempty → A.Nonempty → C.Nonempty →
        Disjoint D A → Disjoint C D → Disjoint C A →
        ∃ (u : SurfaceJet μ) (U : Set Torus),
          u∈surfaceH1 μ ∧ u≠0 ∧ surfaceMean μ u=0 ∧
          surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 ∧
          IsOpen U ∧ (U∩frontier (openRepresentative E)).Nonempty ∧
          (∀ᵐ z ∂(μ : Measure NormalBundle),normalProjection z∈U → u.1 z=0 ∧ u.2 z=0) ∧
          ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0 := by
  obtain ⟨μ,N,hN,hp,hμ,hae,hbalance⟩ := isMinimizerAt_two_nodal_balance hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,?_⟩
  intro v w t D A C hD hA hC hDn hAn hCn hDA hCD hCA
  obtain ⟨hDm,hAm,hmem,hne,hmean,hnull,hhom⟩ := hbalance v w D A hD hA hDn hAn hDA
  have hdsub : D⊆frontier (openRepresentative E) := by
    obtain ⟨W,hW,he⟩ := hD.1
    intro a ha
    rw [he] at ha
    exact ha.1.1
  have hasub : A⊆frontier (openRepresentative E) := by
    obtain ⟨W,hW,he⟩ := hA.1
    intro a ha
    rw [he] at ha
    exact ha.1.1
  obtain ⟨U,hU,hUn,hUD,hUA⟩ := positiveNodalPiece_unused_patch
    (directionalNormalScalar N hN hp t) _ C D A hC hCn hdsub hasub hCD hCA
  refine ⟨_,U,hmem,hne,hmean,hnull,hU,hUn,?_,hhom U hU hUn hUD hUA⟩
  exact surfaceNodalBalance_zero_patch μ
    (nodalSurfaceJet_zero_outside μ _ D U hDm hUD)
    (nodalSurfaceJet_zero_outside μ _ A U hAm hUA)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceVectorMultiplier (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) :
    Lp Cover 2 (μ : Measure NormalBundle) →L[ℝ] Lp Cover 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ q • f
      map_add' := fun f g ↦ Lp.add_smul q f g
      map_smul' := fun c f ↦ (Lp.smul_comm c q f).symm }
    ‖q‖ (fun f ↦ Lp.norm_smul_le q f)

def surfaceGradientMultiplier (μ : FiniteMeasure NormalBundle)
    (g : Lp Cover ∞ (μ : Measure NormalBundle)) :
    Lp ℝ 2 (μ : Measure NormalBundle) →L[ℝ] Lp Cover 2 (μ : Measure NormalBundle) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f • g
      map_add' := fun f h ↦ Lp.smul_add f h g
      map_smul' := fun c f ↦ Lp.smul_assoc c f g }
    ‖g‖ (fun f ↦ (Lp.norm_smul_le f g).trans_eq (mul_comm _ _))

def surfaceCutoffJet (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) : SurfaceJet μ :=
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let g := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  (surfaceMultiplier μ q u.1,surfaceVectorMultiplier μ q u.2+surfaceGradientMultiplier μ g u.1)

lemma surfaceCutoffJet_continuous (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    Continuous (surfaceCutoffJet μ f) := by
  unfold surfaceCutoffJet
  fun_prop

lemma surfaceCutoffJet_smooth (μ : FiniteMeasure NormalBundle) (f g : smoothPeriodicScalars) :
    surfaceCutoffJet μ f (surfaceSmoothJet μ g)=surfaceSmoothJet μ (smoothScalarMul f g) := by
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let df := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  have hq := (smoothScalarValue f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdf := (smoothScalarGradient f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hg := (smoothScalarValue g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdg := (smoothScalarGradient g).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hfg := (smoothScalarValue (smoothScalarMul f g)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hdfg := (smoothScalarGradient (smoothScalarMul f g)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ g).1,hq,hg,hfg] with z hz hqz hgz hfgz
    change (q • (surfaceSmoothJet μ g).1 : Lp ℝ 2 (μ : Measure NormalBundle)) z=_
    rw [hz]
    change q z * (surfaceSmoothJet μ g).1 z=_
    change q z=f.val z.1 at hqz
    change (surfaceSmoothJet μ g).1 z=g.val z.1 at hgz
    change (surfaceSmoothJet μ (smoothScalarMul f g)).1 z=f.val z.1*g.val z.1 at hfgz
    rw [hqz,hgz,hfgz]
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add (q • (surfaceSmoothJet μ g).2 : Lp Cover 2 (μ : Measure NormalBundle))
        ((surfaceSmoothJet μ g).1 • df),Lp.coeFn_lpSMul (r := 2) q (surfaceSmoothJet μ g).2,
      Lp.coeFn_lpSMul (r := 2) (surfaceSmoothJet μ g).1 df,hq,hdf,hg,hdg,hdfg] with
      z hadd hfirst hsecond hqz hdfz hgz hdgz hdfgz
    change ((q • (surfaceSmoothJet μ g).2 : Lp Cover 2 (μ : Measure NormalBundle))+
      ((surfaceSmoothJet μ g).1 • df)) z=_
    rw [hadd,Pi.add_apply,hfirst,hsecond]
    change q z • (surfaceSmoothJet μ g).2 z+(surfaceSmoothJet μ g).1 z • df z=_
    change q z=f.val z.1 at hqz
    change df z=smoothScalarGradient f z at hdfz
    change (surfaceSmoothJet μ g).1 z=g.val z.1 at hgz
    change (surfaceSmoothJet μ g).2 z=smoothScalarGradient g z at hdgz
    change (surfaceSmoothJet μ (smoothScalarMul f g)).2 z=_ at hdfgz
    rw [hqz,hdfz,hgz,hdgz,hdfgz,smoothScalarGradient_mul,add_comm]

lemma surfaceCutoffJet_ae (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (surfaceCutoffJet μ f u).1 z=f.val z.1*u.1 z ∧
      (surfaceCutoffJet μ f u).2 z=f.val z.1 • u.2 z+u.1 z • smoothScalarGradient f z := by
  let q := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)
  let df := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  filter_upwards [(smoothScalarValue f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q u.2,
    Lp.coeFn_lpSMul (r := 2) u.1 df,
    Lp.coeFn_add (q • u.2 : Lp Cover 2 (μ : Measure NormalBundle)) (u.1 • df)] with
    z hq hdf hv hw hd ha
  change q z=f.val z.1 at hq
  change df z=smoothScalarGradient f z at hdf
  constructor
  · change (q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z=_
    rw [hv]
    change q z*u.1 z=_
    rw [hq]
  · change ((q • u.2 : Lp Cover 2 (μ : Measure NormalBundle))+u.1 • df) z=_
    rw [ha,Pi.add_apply,hw,hd]
    change q z • u.2 z+u.1 z • df z=_
    rw [hq,hdf]

theorem surfaceCutoffJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    surfaceCutoffJet μ f u∈surfaceH1 μ := by
  apply map_mem_closure (surfaceCutoffJet_continuous μ f) hu
  rintro _ ⟨g,rfl⟩
  rw [surfaceCutoffJet_smooth]
  exact ⟨smoothScalarMul f g,rfl⟩

end CubicTorus

end
end

end

end OAI
