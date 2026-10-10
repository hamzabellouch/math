import OAI.Dynamics.TriangleBilliards.WeakGenerators

namespace OAI

universe uH uIota

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

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]

omit [CompleteSpace H] in
lemma CR_components_eq {a b c d : H} (hx : a+b=c+d)
    (hy : Complex.I • (a-b) = Complex.I • (c-d)) : a=c ∧ b=d := by
  have hd : a-b=c-d := smul_right_injective H Complex.I_ne_zero hy
  have haa : (2 : ℂ) • a = (2 : ℂ) • c := by
    calc
      _ = (a+b)+(a-b) := by module
      _ = (c+d)+(c-d) := by rw [hx,hd]
      _ = _ := by module
  have ha := smul_right_injective H (by norm_num : (2 : ℂ) ≠ 0) haa
  exact ⟨ha, add_left_cancel (ha ▸ hx)⟩

namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T}
lemma mode_components {u a b : H} {j : ℤ} (h : RotationalCR X Y V u a b)
    (hu : ∀ θ, V.act θ u = fourier j θ • u) :
    V.projection (j+1) a = a ∧ V.projection (j-1) b = b := by
  have he (θ : AddCircle T) :
      fourier (-1) θ • V.act θ a = fourier j θ • a ∧
      fourier 1 θ • V.act θ b = fourier j θ • b := by
    have hx := (h.generators.1).smul (fourier j θ)
    have hy := (h.generators.2).smul (fourier j θ)
    rw [← hu θ] at hx hy
    exact CR_components_eq
      (by simpa only [smul_add] using X.generator_unique (h θ).1 hx)
      (by simpa only [smul_sub, smul_comm (fourier j θ) Complex.I] using
        Y.generator_unique (h θ).2 hy)
  have ha (θ : AddCircle T) : V.act θ a = fourier (j+1) θ • a := by
    have hc := congrArg (fun x : H => fourier 1 θ • x) (he θ).1
    simpa only [smul_smul, ← fourier_add, show (1 : ℤ)+(-1)=0 by norm_num,
      fourier_zero, Pi.one_apply, one_smul, show (1 : ℤ)+j=j+1 by omega] using hc
  have hb (θ : AddCircle T) : V.act θ b = fourier (j-1) θ • b := by
    have hc := congrArg (fun x : H => fourier (-1) θ • x) (he θ).2
    simpa only [smul_smul, ← fourier_add, show (-1 : ℤ)+1=0 by norm_num,
      fourier_zero, Pi.one_apply, one_smul, show (-1 : ℤ)+j=j-1 by omega] using hc
  exact ⟨by simpa using V.projection_of_eigen ha (j+1),
    by simpa using V.projection_of_eigen hb (j-1)⟩
end RotationalCR
end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace CircleAction
variable (V : CircleAction H T)

lemma inner_of_modes {a b : H} {j k : ℤ} (ha : V.projection j a = a)
    (hb : V.projection k b = b) (hjk : j ≠ k) : inner ℂ a b = 0 := by
  rw [← ha, ← hb]
  exact V.projection_orthogonal hjk a b

lemma mode_inner_right {a b : H} {j : ℤ} (ha : V.projection j a = a) :
    inner ℂ a (V.projection j b) = inner ℂ a b := by
  rw [← V.projection_adjoint, ha]

lemma mode_inner_left {a b : H} {j : ℤ} (hb : V.projection j b = b) :
    inner ℂ (V.projection j a) b = inner ℂ a b := by
  rw [V.projection_adjoint, hb]

end CircleAction

/-- The Fourier recurrence from exact invariance, justified on a dense
regular CR core and then on all L2 tests. It never differentiates an
infinite Fourier series term by term. -/
lemma invariant_CR_recurrence (X Y : HilbertFlow H) (V : CircleAction H T)
    (hD : Dense {v : H | ∃ c d, RotationalCR X Y V v c d})
    {f : H} (hf : X.HasGenerator f 0) (a b : ℤ → H)
    (hg : ∀ j, RotationalCR X Y V (V.projection j f) (a j) (b j)) (m : ℤ) :
    a m + b (m+2) = 0 := by
  have hmodes j := (hg j).mode_components (V.projection_eigen j f)
  have ha := (hmodes m).1
  have hb := (hmodes (m+2)).2
  have hb' : V.projection (m+1) (b (m+2)) = b (m+2) := by
    simpa only [show m+2-1=m+1 by omega] using hb
  have htest (v : H) (hv : ∃ c d, RotationalCR X Y V v c d) :
      inner ℂ (a m+b (m+2)) v = 0 := by
    obtain ⟨c,d,hv⟩ := hv
    have hp := (hv.projection (m+1)).1
    have hpf : X.HasGenerator (V.projection (m+1) v)
        (V.projection (m+2) c + V.projection m d) := by
      simpa only [show m+1+1=m+2 by omega, show m+1-1=m by omega] using hp
    have h0 := X.generator_skew hf hpf
    simp only [inner_zero_left, add_zero] at h0
    have h1 := X.generator_skew (hg m).generators.1 hpf
    have h2 := X.generator_skew (hg (m+2)).generators.1 hpf
    have hmc : inner ℂ (V.projection m f) (V.projection (m+2) c) = 0 :=
      V.projection_orthogonal (by omega) f c
    have hpmd : inner ℂ (V.projection (m+2) f) (V.projection m d) = 0 :=
      V.projection_orthogonal (by omega) f d
    have hmb : inner ℂ (b m) (V.projection (m+1) v) = 0 :=
      V.inner_of_modes (hmodes m).2 (V.projection_idem _ v) (by omega)
    have hpa : inner ℂ (a (m+2)) (V.projection (m+1) v) = 0 :=
      V.inner_of_modes (hmodes (m+2)).1 (V.projection_idem _ v) (by omega)
    simp only [inner_add_left, inner_add_right, hmc, hpmd, hmb, hpa,
      zero_add, add_zero, V.mode_inner_left (V.projection_idem m d),
      V.mode_inner_left (V.projection_idem (m+2) c), V.mode_inner_right ha,
      V.mode_inner_right hb'] at h1 h2
    rw [inner_add_left]
    rw [inner_add_right] at h0
    linear_combination h1 + h2 - h0
  have hall : ∀ v : H, inner ℂ (a m+b (m+2)) v = 0 :=
    hD.induction htest (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  exact inner_self_eq_zero.mp (hall (a m+b (m+2)))

omit [CompleteSpace H] in
lemma HilbertFlow.HasGenerator.zero (W : HilbertFlow H) : W.HasGenerator 0 0 := by
  intro t
  simp only [map_zero, sub_zero]

omit [CompleteSpace H] in
lemma HilbertFlow.HasGenerator.sum (W : HilbertFlow H) {ι : Type uIota}
    (s : Finset ι) (u a : ι → H) (h : ∀ i ∈ s, W.HasGenerator (u i) (a i)) :
    W.HasGenerator (∑ i ∈ s, u i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasGenerator.zero W
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma CircleAction.bounded_modes_weaklyTendsto (V : CircleAction H T)
    {φ : ℕ → ℤ} (hφ : Function.Injective φ) (r : ℕ → H) {C : ℝ}
    (hC : ∀ n, ‖r n‖ ≤ C) (hr : ∀ n, V.projection (φ n) (r n) = r n) :
    WeaklyTendsto r atTop 0 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  intro L
  let v := (InnerProductSpace.toDual ℝ H).symm L
  have hv (x : H) : inner ℝ v x = L x := InnerProductSpace.toDual_symm_apply
  have he := (Complex.continuous_re.tendsto 0).comp (V.bounded_modes_escape hφ r hC hr v)
  change Tendsto (fun n => (inner ℂ v (r n)).re) atTop (𝓝 (0 : ℝ)) at he
  have heq (x : H) : (inner ℂ v x).re = L x := hv x
  simpa only [heq, map_zero] using he

/-- The one-sided parity tail has the claimed L2 generator. The uniformly
bounded terminal term disappears WEAKLY by escaping angular frequency. -/
lemma parity_tail_endpoint (X Y : HilbertFlow H) (V : CircleAction H T)
    (hD : Dense {v : H | ∃ c d, RotationalCR X Y V v c d})
    {f : H} (hf : X.HasGenerator f 0) (a b : ℤ → H)
    (hg : ∀ j, RotationalCR X Y V (V.projection j f) (a j) (b j))
    {C : ℝ} (ha : ∀ j, ‖a j‖ ≤ C) (m : ℤ) :
    X.HasGenerator (V.parityTail m f) (b m) := by
  have hrec := invariant_CR_recurrence X Y V hD hf a b hg
  let U (N : ℕ) := ∑ n ∈ Finset.range (N+1), V.projection (m+2*(n : ℤ)) f
  let R (N : ℕ) := a (m+2*(N : ℤ))
  have hfinite (N : ℕ) : X.HasGenerator (U N) (b m + R N) := by
    induction N with
    | zero => simpa only [U,R,Nat.zero_add,Finset.sum_range_one,Nat.cast_zero,mul_zero,add_zero,add_comm]
        using (hg m).generators.1
    | succ N ih =>
      have h := ih.add (hg (m+2*((N+1 : ℕ) : ℤ))).generators.1
      have he : b m + R N + (a (m+2*((N+1 : ℕ) : ℤ)) + b (m+2*((N+1 : ℕ) : ℤ))) =
          b m + R (N+1) := by
        have hi : m+2*((N+1 : ℕ) : ℤ)=m+2*(N : ℤ)+2 := by push_cast; ring
        have hr := hrec (m+2*(N : ℤ))
        dsimp only [R]
        rw [hi]
        calc
          _ = b m + a (m+2*(N : ℤ)+2) + (a (m+2*(N : ℤ))+b (m+2*(N : ℤ)+2)) := by abel
          _ = _ := by rw [hr,add_zero]
      simpa only [U,Finset.sum_range_succ,he] using h
  have hu := (V.parityTail_convergence m f).comp (tendsto_add_atTop_nat 1)
  have hm (N : ℕ) : V.projection (m+1+2*(N : ℤ)) (R N) = R N := by
    have hh := ((hg (m+2*(N : ℤ))).mode_components
      (V.projection_eigen (m+2*(N : ℤ)) f)).1
    convert hh using 1
    congr 2
    ring
  have hr := V.bounded_modes_weaklyTendsto (CircleAction.parity_index_injective (m+1)) R
    (fun N => ha _) hm
  have hb : WeaklyTendsto (fun N => b m + R N) atTop (b m) := by
    simpa only [add_zero] using (weaklyTendsto_of_tendsto (tendsto_const_nhds (x := b m))).add hr
  exact HilbertFlow.HasGenerator.weak_limit X (weaklyTendsto_of_tendsto hu) hb
    (Eventually.of_forall hfinite)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis Filter Set
open scoped Topology BoundedContinuousFunction

lemma dense_rotationalCR_core (Q : Triangle) :
    Dense {v : DoubleL2 Q | ∃ a b, RotationalCR (geodesicHilbertFlow Q)
      (transverseHilbertFlow Q) (angularCircleAction Q) v a b} := by
  let D : Set (DoubleL2 Q) := {v | ∃ a b, RotationalCR (geodesicHilbertFlow Q)
    (transverseHilbertFlow Q) (angularCircleAction Q) v a b}
  have hb (g : DoublePhase →ᵇ ℂ) (hg : MemLp (g : DoublePhase → ℂ) 2 (doubleMeasure Q)) :
      hg.toLp g ∈ closure D := by
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
    apply isClosed_closure.mem_of_tendsto
      (supported_smoothing_toLp_tendsto Q hK g.continuous.stronglyMeasurable hg hpos hlim)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    exact supportedSmoothing_rotationalCR Q (hpos n)
      (by dsimp only [K]; nlinarith [hpos n]) (hsmall n)
      g.continuous.stronglyMeasurable g.norm_coe_le_norm
  intro u
  rw [← closure_closure (s := D)]
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨g,hg,hgp⟩ := (Lp.memLp u).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < δ/2))
  refine ⟨hgp.toLp g,hb g hgp,?_⟩
  rw [dist_eq_norm, ← Lp.toLp_coeFn u (Lp.memLp u), ← MemLp.toLp_sub, Lp.norm_toLp]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ/2)] at hh
  exact hh.trans_lt (by linarith)

/-- The actual triangular parity-tail endpoint. There is no unproved
smooth-core density assumption remaining in this application. -/
lemma bounded_invariant_tail_endpoint (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0),
      ∃ a b : ℤ → DoubleL2 Q,
        (∀ j, RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
          (angularCircleAction Q) ((angularCircleAction Q).projection j (hf.toLp f)) (a j) (b j)) ∧
        (∀ j, ‖a j‖ ≤ C*H ∧ ‖b j‖ ≤ C*H) ∧
        ∀ m, (geodesicHilbertFlow Q).HasGenerator
          ((angularCircleAction Q).parityTail m (hf.toLp f)) (b m) := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR Q
  refine ⟨C,hC,?_⟩
  intro H f hm hf hH hfi
  choose a b hg ha hb using fun j => hbound hm hf hH hfi j
  refine ⟨a,b,hg,fun j => ⟨ha j,hb j⟩,?_⟩
  exact fun m => parity_tail_endpoint _ _ _ (dense_rotationalCR_core Q) hfi a b hg ha m

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
