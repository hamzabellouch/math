import OAI.Dynamics.TriangleBilliards.WeakCompactness

namespace OAI

universe uAlpha uE uF uH

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards.Analysis.HilbertFlow
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : HilbertFlow H)

omit [CompleteSpace H] in
lemma HasGenerator.weak_limit {α : Type uAlpha} {l : Filter α} [l.NeBot]
    {u a : α → H} {v b : H} (hu : WeaklyTendsto u l v) (ha : WeaklyTendsto a l b)
    (h : ∀ᶠ n in l, W.HasGenerator (u n) (a n)) : W.HasGenerator v b := by
  exact (hu.prod ha).mem_of_closed_convex W.generatorGraph_closed W.generatorGraph_convex h

lemma exists_generator_of_bounded_approx
    {u a : ℕ → H} {v : H} {C : ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (ha : ∀ n, ‖a n‖ ≤ C)
    (h : ∀ n, W.HasGenerator (u n) (a n)) :
    ∃ b : H, W.HasGenerator v b ∧ ‖b‖ ≤ C := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨b,hb,φ,hφ,hlim⟩ := exists_weak_subsequence_unrestricted a ha
  exact ⟨b, HasGenerator.weak_limit W
    ((weaklyTendsto_of_tendsto hu).comp hφ.tendsto_atTop) hlim
    (Eventually.of_forall fun n => h (φ n)), hb⟩

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis

lemma supported_smoothing_toLp_tendsto (Q : Triangle) {K : ℝ} (hK : 0 < K)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (supportedSmoothing_memLp_of_memLp Q (hε n) (K*ε n) hm hf).toLp
      (supportedSmoothing Q (ε n) (K*ε n) f)) atTop (𝓝 (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall hε⟩
  convert (supported_smoothing_lpNorm_tendsto Q hK hm hf).comp he using 1
  ext n
  rw [← MemLp.toLp_sub, Lp.norm_toLp, toReal_eLpNorm]
  rfl

/-- Bounded modes for the nonsingular billiard unitary groups.
Only individual Fourier derivatives are bounded; this does not impose
a bound on the sum of all mode derivatives. -/
lemma bounded_invariant_modes (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (j : ℤ),
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp f)) dx ∧
        (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp f)) dy ∧
        ‖dx‖ ≤ C * H ∧ ‖dy‖ ≤ C * H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_modes Q
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro H f hm hf hH hfi j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  let K := Q.safetyFactor + 1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    simpa only [mul_zero, zero_mul] using hc.continuousAt.eventually
      (gt_mem_nhds (by simp only [mul_zero, zero_mul]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,hlim⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  let hw n := supportedSmoothing_memLp Q (hpos n) (K*ε n) hm hH
  let u n := (angularCircleAction Q).projection j
    ((hw n).toLp (supportedSmoothing Q (ε n) (K*ε n) f))
  have hu : Tendsto u atTop (𝓝 ((angularCircleAction Q).projection j (hf.toLp f))) :=
    ((angularCircleAction Q).projection j).continuous.tendsto _ |>.comp
      (supported_smoothing_toLp_tendsto Q hK hm hf hpos hlim)
  have hh (n : ℕ) := hbound hm hf hH hfi (hpos n) (hsmall n) j
  choose dx dy hgx hgy hbx hby using hh
  have hbd {a : ℝ} (ha : a^2 ≤ C*H^2) : a ≤ Real.sqrt C * H := by
    have hs := Real.sq_sqrt hC
    have hs' : (Real.sqrt C * H)^2 = C*H^2 := by rw [mul_pow, hs]
    exact (sq_le_sq₀ (by positivity : 0 ≤ |a|) (by positivity : 0 ≤ Real.sqrt C * H)).mp
      (by simpa only [sq_abs, hs'] using ha) |>.trans' (le_abs_self a)
  obtain ⟨ax,hax,hAx⟩ := (geodesicHilbertFlow Q).exists_generator_of_bounded_approx hu
    (fun n => hbd (hbx n)) hgx
  obtain ⟨ay,hay,hAy⟩ := (transverseHilbertFlow Q).exists_generator_of_bounded_approx hu
    (fun n => hbd (hby n)) hgy
  exact ⟨ax,ay,hax,hay,hAx,hAy⟩

end TriangularBilliards

namespace TriangularBilliards.Analytic
section Map
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : Type uAlpha} {l : Filter α}
lemma WeaklyTendsto.map {u : α → E} {v : E} (h : WeaklyTendsto u l v)
    (A : E →L[ℝ] F) : WeaklyTendsto (fun n => A (u n)) l (A v) :=
  fun L => h (L.comp A)
lemma WeaklyTendsto.add {u v : α → E} {a b : E}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => u n + v n) l (a+b) := by
  intro L
  simpa only [map_add] using (hu L).add (hv L)
lemma WeaklyTendsto.sub {u v : α → E} {a b : E}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => u n - v n) l (a-b) := by
  intro L
  simpa only [map_sub] using (hu L).sub (hv L)
end Map
end TriangularBilliards.Analytic

namespace TriangularBilliards.Analysis
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T}

omit [CompleteSpace H] [Fact (0 < T)] in
lemma weak_limit {α : Type uAlpha} {l : Filter α} [l.NeBot]
    {u a b : α → H} {v c d : H}
    (hu : WeaklyTendsto u l v) (ha : WeaklyTendsto a l c) (hb : WeaklyTendsto b l d)
    (h : ∀ n, RotationalCR X Y V (u n) (a n) (b n)) : RotationalCR X Y V v c d := by
  intro θ
  let A := ((V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let P : H →L[ℝ] H := (fourier (-1) θ • (V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let M : H →L[ℝ] H := (fourier 1 θ • (V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let I : H →L[ℝ] H := (Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
  exact ⟨HilbertFlow.HasGenerator.weak_limit X (hu.map A) ((ha.map P).add (hb.map M))
      (Eventually.of_forall fun n => (h n θ).1),
    HilbertFlow.HasGenerator.weak_limit Y (hu.map A) (((ha.map P).sub (hb.map M)).map I)
      (Eventually.of_forall fun n => (h n θ).2)⟩

omit [Fact (0 < T)] in
lemma exists_of_bounded_approx {u a b : ℕ → H} {v : H} {C : ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (ha : ∀ n, ‖a n‖ ≤ C) (hb : ∀ n, ‖b n‖ ≤ C)
    (h : ∀ n, RotationalCR X Y V (u n) (a n) (b n)) :
    ∃ c d, RotationalCR X Y V v c d ∧ ‖c‖ ≤ C ∧ ‖d‖ ≤ C := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨c,hc,φ,hφ,hac⟩ := exists_weak_subsequence_unrestricted a ha
  obtain ⟨d,hd,ψ,hψ,hbd⟩ := exists_weak_subsequence_unrestricted (b ∘ φ) (fun n => hb (φ n))
  exact ⟨c,d,weak_limit ((weaklyTendsto_of_tendsto hu).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (hac.comp hψ.tendsto_atTop) hbd (fun n => h (φ (ψ n))), hc, hd⟩

/-- In a single Fourier mode, the two CR components are exactly the two
Fourier components of its geodesic generator. -/
lemma components_unique {u a b dx : H} {j : ℤ}
    (h : RotationalCR X Y V u a b)
    (ha : V.projection (j+1) a = a) (hb : V.projection (j-1) b = b)
    (hx : X.HasGenerator u dx) :
    a = V.projection (j+1) dx ∧ b = V.projection (j-1) dx := by
  have he : dx = a+b := X.generator_unique hx h.generators.1
  rw [he, map_add, map_add, ha, hb]
  have hab : V.projection (j+1) b = 0 := by
    rw [← hb, V.projection_mul, ite_eq_right (by omega)]
  have hba : V.projection (j-1) a = 0 := by
    rw [← ha, V.projection_mul, ite_eq_right (by omega)]
  simp only [hab,hba,add_zero,zero_add,and_self]

end RotationalCR
end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma supportedSmoothing_rotationalCR (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    let hw := supportedSmoothing_memLp Q hε R hm hf
    ∃ a b, RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
      (hw.toLp _) a b := by
  dsimp only
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε
    ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
  have hd := fun v b => (supportedSmoothing_contDiff Q hε R hm hf v b).differentiable (by simp)
  have hm' := (supportedSmoothing_stronglyMeasurable Q ε R hm).measurable
  have hx := xDerivative_memLp_of_gradient_bound Q hm' hd hC
  have hy := yDerivative_memLp_of_gradient_bound Q hm' hd hC
  exact ⟨_,_,seam_rotationalCR (supportedSmoothing_seam Q hε hR hsmall f) hd hC
    (supportedSmoothing_memLp Q hε R hm hf) hx hy⟩

lemma bounded_invariant_regularized_CR (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
      {ε : ℝ} (hε : 0 < ε)
      (_hsmall : 2 * ((Q.safetyFactor + 1) * ε) * Q.coordinateBound < 1) (j : ℤ),
      let w := supportedSmoothing Q ε ((Q.safetyFactor + 1) * ε) f
      let hw := supportedSmoothing_memLp Q hε ((Q.safetyFactor + 1) * ε) hm hH
      ∃ a b : Lp ℂ 2 (doubleMeasure Q),
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
          ((angularCircleAction Q).projection j (hw.toLp w)) a b ∧
        ‖a‖ ^ 2 ≤ C * H^2 ∧ ‖b‖ ^ 2 ≤ C * H^2 := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_modes Q
  refine ⟨C,hC,?_⟩
  intro H f hm hf hH hfi ε hε hsmall j
  obtain ⟨dx,dy,hgx,_,hbx,_⟩ := hbound hm hf hH hfi hε hsmall j
  have hR : Q.safetyFactor * ε < (Q.safetyFactor+1)*ε := by nlinarith
  obtain ⟨a,b,hcr⟩ := supportedSmoothing_rotationalCR Q hε hR hsmall hm hH
  have hc := hcr.projection_covariant j
  have hh := hc.components_unique ((angularCircleAction Q).projection_idem _ a)
    ((angularCircleAction Q).projection_idem _ b) hgx
  refine ⟨_,_,hc,?_,?_⟩
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (hh.1 ▸ (angularCircleAction Q).projection_norm_le (j+1) dx) |>.trans hbx
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (hh.2 ▸ (angularCircleAction Q).projection_norm_le (j-1) dx) |>.trans hbx

end TriangularBilliards

namespace TriangularBilliards
open Analysis
lemma bounded_invariant_CR (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (j : ℤ),
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
          ((angularCircleAction Q).projection j (hf.toLp f)) dx dy ∧
        ‖dx‖ ≤ C * H ∧ ‖dy‖ ≤ C * H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_CR Q
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro H f hm hf hH hfi j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  let K := Q.safetyFactor + 1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    simpa only [mul_zero, zero_mul] using hc.continuousAt.eventually
      (gt_mem_nhds (by simp only [mul_zero, zero_mul]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,hlim⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  let hw n := supportedSmoothing_memLp Q (hpos n) (K*ε n) hm hH
  let u n := (angularCircleAction Q).projection j
    ((hw n).toLp (supportedSmoothing Q (ε n) (K*ε n) f))
  have hu : Tendsto u atTop (𝓝 ((angularCircleAction Q).projection j (hf.toLp f))) :=
    ((angularCircleAction Q).projection j).continuous.tendsto _ |>.comp
      (supported_smoothing_toLp_tendsto Q hK hm hf hpos hlim)
  have hh (n : ℕ) := hbound hm hf hH hfi (hpos n) (hsmall n) j
  choose dx dy hcr hbx hby using hh
  have hbd {a : ℝ} (ha : a^2 ≤ C*H^2) : a ≤ Real.sqrt C * H := by
    have hs := Real.sq_sqrt hC
    have hs' : (Real.sqrt C * H)^2 = C*H^2 := by rw [mul_pow, hs]
    exact (sq_le_sq₀ (by positivity : 0 ≤ |a|) (by positivity : 0 ≤ Real.sqrt C * H)).mp
      (by simpa only [sq_abs, hs'] using ha) |>.trans' (le_abs_self a)
  exact RotationalCR.exists_of_bounded_approx hu (fun n => hbd (hbx n))
    (fun n => hbd (hby n)) hcr

end TriangularBilliards

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
