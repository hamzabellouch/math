import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open MeasureTheory

namespace ConvexProximal
variable [FiniteDimensional ℝ E]
section Measurable
open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E]

lemma exists_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) (x : E) :
    ∃ p, IsSubgradientOn f univ x p := by
  let μ : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hdense : Dense {z | DifferentiableAt ℝ f z} :=
    μ.dense_of_ae (hlip.ae_differentiableAt (μ := μ))
  let P := Metric.closedBall (0:E) (L:ℝ)
  have hP : IsCompact P := isCompact_closedBall _ _
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let C : Set (E × P) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hfc := hlip.continuous
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have hsub : {z | DifferentiableAt ℝ f z} ⊆ Prod.fst '' C := by
    intro z hz
    let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)
    have hp : IsSubgradientOn f univ z p := gradient_subgradient hc hz.hasFDerivAt
    have hpn : p ∈ P := by
      simpa only [P, Metric.mem_closedBall, dist_zero_right] using subgradient_norm_le hlip hp
    exact ⟨(z, ⟨p, hpn⟩), hp, rfl⟩
  have hx : x ∈ Prod.fst '' C := by
    rw [← hproj.closure_eq]
    exact (Dense.mono hsub hdense) x
  obtain ⟨⟨z,p⟩, hz, rfl⟩ := hx
  exact ⟨p.1, hz⟩

lemma prox_surjective {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) : Function.Surjective (prox f L hlip) := by
  intro x
  obtain ⟨p,hp⟩ := exists_subgradient hlip hc x
  exact ⟨x+p, prox_of_subgradient hlip hc hp⟩

lemma ae_exists_regular_proximal_inverse {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ y : E, prox f L hlip y = x ∧
      DifferentiableAt ℝ (prox f L hlip) y ∧
      (fderiv ℝ (prox f L hlip) y).det ≠ 0 := by
  let P := prox f L hlip
  let ν : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hP : LipschitzWith 1 P := prox_lipschitz hlip hc
  let N : Set E := {y | ¬DifferentiableAt ℝ P y}
  let Z : Set E := {y | DifferentiableAt ℝ P y ∧ (fderiv ℝ P y).det = 0}
  have hN : ν N = 0 := (ae_iff).mp (hP.ae_differentiableAt (μ := ν))
  have hPN : ν (P '' N) = 0 := by
    have hh := hP.hausdorffMeasure_image_le
      (by positivity : (0:ℝ) ≤ Module.finrank ℝ E) N
    simpa only [ν, hN, mul_zero, nonpos_iff_eq_zero] using hh
  have hNμ : μ (P '' N) = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μ ν) hPN
  have hZμ : μ (P '' Z) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt) (fun y hy => hy.2)
  have hgood : ∀ᵐ x ∂μ, x ∉ P '' N ∧ x ∉ P '' Z := by
    exact (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hNμ)).and (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hZμ))
  filter_upwards [hgood] with x hx
  obtain ⟨y,hy⟩ := prox_surjective hlip hc x
  have hd : DifferentiableAt ℝ P y := by
    by_contra hn
    exact hx.1 ⟨y,hn,hy⟩
  refine ⟨y,hy,hd,?_⟩
  intro hz
  exact hx.2 ⟨y,⟨hd,hz⟩,hy⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma subgradient_line_deriv {f : E → ℝ} {x h : E} {t a : ℝ} {p : E}
    (hp : IsSubgradientOn f univ (x+t • h) p)
    (hd : HasDerivAt (fun s : ℝ => f (x+s • h)) a t) :
    a = inner ℝ p h := by
  have hm : IsLocalMin (fun s : ℝ => f (x+s • h) - s*inner ℝ p h) t := by
    apply Filter.Eventually.of_forall
    intro s
    have hh := hp (x+s • h) (mem_univ _)
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    rw [heq,real_inner_smul_right] at hh
    dsimp
    nlinarith
  have hh := hm.hasDerivAt_eq_zero (hd.sub ((hasDerivAt_id t).mul_const (inner ℝ p h)))
  simpa only [one_mul, sub_eq_zero] using hh

lemma quadraticExpansion_of_subgradient_differential {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x p : E} {A : E →L[ℝ] E}
    (hdiff : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z q : E, ‖z-x‖ < delta → IsSubgradientOn f univ z q →
        ‖q-p-A (z-x)‖ ≤ eps*‖z-x‖) :
    HasQuadraticExpansion (fun h => f (x+h)) p A := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hdiff eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  let g : ℝ → ℝ := fun t => f (x+t • h)
  have hline : LipschitzWith ‖h‖₊ (fun t : ℝ => x+t • h) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    simp only [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,coe_nnnorm]
    exact le_of_eq (mul_comm _ _)
  have hgAC : AbsolutelyContinuousOnInterval g 0 1 :=
    (hlip.comp hline).lipschitzOnWith.absolutelyContinuousOnInterval
  let a : ℝ := inner ℝ p h
  let b : ℝ := inner ℝ (A h) h
  have hlin : IntervalIntegrable (fun t : ℝ => a+t*b) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => a+t*b)).intervalIntegrable _ _
  have haebound : ∀ᵐ t : ℝ, t ∈ uIoc (0:ℝ) 1 →
      ‖deriv g t - (a+t*b)‖ ≤ eps*‖h‖^2 := by
    filter_upwards [hgAC.ae_differentiableAt] with t ht htc
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at htc
      exact ⟨htc.1.le,htc.2⟩
    have htu : t ∈ uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ht01
    obtain ⟨q,hq⟩ := exists_subgradient hlip hc (x+t • h)
    have hder : deriv g t = inner ℝ q h := subgradient_line_deriv hq (ht htu).hasDerivAt
    have hth : ‖(x+t • h)-x‖ ≤ ‖h‖ := by
      simp only [add_sub_cancel_left,norm_smul_of_nonneg ht01.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht01.2
    have hnorm := hbound (x+t • h) q (hth.trans_lt hh) hq
    have heq : deriv g t - (a+t*b) = inner ℝ (q-p-A ((x+t • h)-x)) h := by
      simp only [hder,a,b,inner_sub_left,add_sub_cancel_left,map_smul,
        real_inner_smul_left]
      ring
    calc
      ‖deriv g t - (a+t*b)‖ = ‖inner ℝ (q-p-A ((x+t • h)-x)) h‖ := congrArg norm heq
      _ ≤ ‖q-p-A ((x+t • h)-x)‖*‖h‖ := norm_inner_le_norm _ _
      _ ≤ (eps*‖(x+t • h)-x‖)*‖h‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ (eps*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hth heps.le) (norm_nonneg _)
      _ = eps*‖h‖^2 := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae haebound
  rw [intervalIntegral.integral_sub hgAC.intervalIntegrable_deriv hlin,
    hgAC.integral_deriv_eq_sub] at hi
  have hilin : (∫ t : ℝ in (0:ℝ)..1, a+t*b) = a+b/2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => a) (g := fun t : ℝ => t*b)
      (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => t*b)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,integral_id]
    norm_num
    ring
  rw [hilin] at hi
  simpa only [HasQuadraticExpansion,quadraticTaylor,g,a,b,one_smul,zero_smul,add_zero,
    Real.norm_eq_abs,sub_zero,abs_one,mul_one,sub_sub,add_assoc] using hi

omit [MeasurableSpace E] [BorelSpace E] in

lemma symmetrized_quadratic (A : E →L[ℝ] E) :
    let S := (1/2 : ℝ) • (A + A.adjoint)
    (∀ h k, inner ℝ (S h) k = inner ℝ h (S k)) ∧
      (∀ h, inner ℝ (S h) h = inner ℝ (A h) h) := by
  dsimp
  constructor
  · intro h k
    simp only [smul_apply,add_apply,real_inner_smul_left,real_inner_smul_right,
      inner_add_left,inner_add_right,A.adjoint_inner_left,A.adjoint_inner_right]
    ring
  · intro h
    simp only [smul_apply,add_apply,real_inner_smul_left,inner_add_left,
      A.adjoint_inner_left,real_inner_comm h (A h)]
    ring

lemma ae_quadraticExpansion_lipschitz_convex {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [hlip.ae_differentiableAt (μ := μ),
    ae_exists_regular_proximal_inverse hlip hc μ] with x hdf hx
  obtain ⟨y,hy,hdP,hdet⟩ := hx
  let B := (fderiv ℝ (prox f L hlip) y).toContinuousLinearEquivOfDetNeZero hdet
  have hB : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y := by
    simpa only [B,ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hdP.hasFDerivAt
  let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  let A := (B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E
  have hdiff := uniform_subgradient_differential_of_regular_prox hlip hc
    hdf.hasFDerivAt hy B hB
  have hquad : HasQuadraticExpansion (fun h => f (x+h)) p A :=
    quadraticExpansion_of_subgradient_differential hlip hc hdiff
  let S := (1/2 : ℝ) • (A + A.adjoint)
  obtain ⟨hsym,hdiag⟩ := symmetrized_quadratic A
  change ∀ h, inner ℝ (S h) h = inner ℝ (A h) h at hdiag
  refine ⟨p,S,hsym,?_⟩
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hquad eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have hi := hbound h hh
  simpa only [quadraticTaylor,hdiag h] using hi

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_congr_nhds {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hfg : f =ᶠ[𝓝 (0:E)] g) (hf : HasQuadraticExpansion f p A) :
    HasQuadraticExpansion g p A := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hfg
  have hzero : f 0 = g 0 := hfg.self_of_nhds
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hf eps heps
  refine ⟨min d r,by positivity,?_⟩
  intro h hh
  have hhg : f h = g h := hball (by
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_lt_of_le hh (min_le_right _ _))
  have hb := hbound h (lt_of_lt_of_le hh (min_le_left _ _))
  simpa only [quadraticTaylor,hzero,hhg] using hb

lemma ae_quadraticExpansion_convex_open {f : E → ℝ} {s : Set E}
    (hs : IsOpen s) (hc : ConvexOn ℝ s f) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  apply ae_of_locally_ae μ
  intro x hx
  obtain ⟨L,t,ht,hlip⟩ := hc.locallyLipschitzOn hs hx
  rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hx)] at ht
  obtain ⟨r,hr,hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (hs.mem_nhds hx))
  have hrt' : Metric.ball x r ⊆ t := fun _ hy => (hrt hy).1
  have hrs : Metric.ball x r ⊆ s := fun _ hy => (hrt hy).2
  obtain ⟨g,hgL,hgC,hfg⟩ := convex_lipschitz_extension
    (hc.subset hrs (convex_ball _ _)) (hlip.mono hrt')
    (Metric.nonempty_ball.mpr hr)
  refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
  filter_upwards [ae_quadraticExpansion_lipschitz_convex hgL hgC μ] with z hz hzb
  obtain ⟨p,A,hA,hquad⟩ := hz
  refine ⟨p,A,hA,quadraticExpansion_congr_nhds ?_ hquad⟩
  have hcont : Tendsto (fun h : E => z+h) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : E => z+h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0:E)
  filter_upwards [hcont (Metric.isOpen_ball.mem_nhds hzb)] with h hh
  exact (hfg hh).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_sub_quadratic {f : E → ℝ} {x p : E} {A : E →L[ℝ] E}
    (K : ℝ)
    (hg : HasQuadraticExpansion (fun h => f (x+h)+K/2*‖x+h‖^2) p A) :
    HasQuadraticExpansion (fun h => f (x+h)) (p-K • x)
      (A-K • ContinuousLinearMap.id ℝ E) := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hg eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have heq : (f (x+h)+K/2*‖x+h‖^2) -
      quadraticTaylor (f (x+0)+K/2*‖x+0‖^2) p A h =
        f (x+h)-quadraticTaylor (f (x+0)) (p-K • x)
          (A-K • ContinuousLinearMap.id ℝ E) h := by
    simp only [quadraticTaylor,add_zero,norm_sq_add_real,inner_sub_left,
      real_inner_smul_left,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    ring
  have hb := hbound h hh
  rwa [heq] at hb

lemma ae_quadraticExpansion_semiconvex_open {f : E → ℝ} {s : Set E} (K : ℝ)
    (hs : IsOpen s) (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [ae_quadraticExpansion_convex_open hs hc μ] with x hx hxs
  obtain ⟨p,A,hA,hquad⟩ := hx hxs
  refine ⟨p-K • x,A-K • ContinuousLinearMap.id ℝ E,?_,
    quadraticExpansion_sub_quadratic K hquad⟩
  intro h k
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,inner_sub_left,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,hA h k]
end Measurable

end ConvexProximal
end WeakMTWTransport

end
end
end
end

end OAI
