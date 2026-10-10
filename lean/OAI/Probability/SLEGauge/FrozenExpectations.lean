import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.EulerMeasurability

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
namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma expected_frozen_nodes {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mU : ∀ k, MeasurableSet (U k))
    (h : ℝ≥0) (q : E × ℝ)
    (hU : ∀ (k : ℕ) b c, (∀ t ≤ (k:ℝ≥0)*h, b t = c t) → ∀ x,
      ((b,x) ∈ U k ↔ (c,x) ∈ U k))
    {M : ℝ} (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hg : ∀ k b x, (b,x) ∈ U k → A.D x.1 x.2 (v x.1 x.2)+deriv (deriv (A.F x.1)) x.2/2 ≤ 0)
    (k : ℕ) :
    (∫ b : Driver, A.F (frozenNodes v U h q k b).1 (frozenNodes v U h q k b).2 ∂W) ≤
      A.F q.1 q.2+(k:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h:ℝ)^2+A.C₃/3*(h:ℝ)*Real.sqrt h) := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hi (i : ℕ) : Integrable (fun b : Driver =>
      A.F (frozenNodes v U h q i b).1 (frozenNodes v U h q i b).2) W := by
    have hm := (measurable_frozenNodes v mv U mU h q i).comp
      (Measurable.of_eval fun time => (show Continuous (fun driver : Driver => driver time) from continuous_eval_const time).measurable)
    exact (integrable_const A.C₀).mono' (A.mF.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using A.hF _ _)
  induction k with
  | zero => simp [frozenNodes,Measure.real]
  | succ k ih =>
    have he := expected_frozen_step hW A v mv U mU h q hU hv hg k
    rw [integral_sub (hi (k+1)) (hi k)] at he
    push_cast
    linarith

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem expected_frozen_limit {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (U : ℕ → ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)))
    (mU : ∀ n k, MeasurableSet (U n k)) (h : ℕ → ℝ≥0) (k : ℕ → ℕ) (q : E × ℝ)
    (hU : ∀ n (k : ℕ) b c, (∀ t ≤ (k:ℝ≥0)*h n, b t = c t) → ∀ x,
      ((b,x) ∈ U n k ↔ (c,x) ∈ U n k))
    (M : ℝ) (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hg : ∀ n k b x, (b,x) ∈ U n k →
      A.D x.1 x.2 (v x.1 x.2)+deriv (deriv (A.F x.1)) x.2/2 ≤ 0)
    (X : Driver → E × ℝ) (t : ℝ)
    (hh : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0))
    (ht : Tendsto (fun n => (k n:ℝ)*(h n:ℝ)) atTop (𝓝 t))
    (hX : ∀ᵐ (b : Driver) ∂W, Tendsto (fun n => frozenNodes v (U n) (h n) q (k n) b)
      atTop (𝓝 (X b))) :
    (∫ b, A.F (X b).1 (X b).2 ∂W) ≤ A.F q.1 q.2 := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hc : ∀ᵐ (b : Driver) ∂W, Tendsto (fun n =>
      A.F (frozenNodes v (U n) (h n) q (k n) b).1 (frozenNodes v (U n) (h n) q (k n) b).2)
      atTop (𝓝 (A.F (X b).1 (X b).2)) := by
    filter_upwards [hX] with b hb
    exact A.cF.continuousAt.tendsto.comp hb
  have hi : Tendsto (fun n => ∫ b : Driver,
      A.F (frozenNodes v (U n) (h n) q (k n) b).1 (frozenNodes v (U n) (h n) q (k n) b).2 ∂W)
      atTop (𝓝 (∫ b, A.F (X b).1 (X b).2 ∂W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Driver => A.C₀)
    · intro n
      have hm : Measurable (fun b : Driver => (b : ℝ≥0 → ℝ)) :=
        Measurable.of_eval fun time => (continuous_eval_const time).measurable
      exact (A.mF.comp ((measurable_frozenNodes v mv (U n) (mU n) (h n) q (k n)).comp hm)).aestronglyMeasurable
    · exact integrable_const A.C₀
    · intro n
      exact Filter.Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs] using A.hF _ _
    · exact hc
  have hs : Tendsto (fun n => Real.sqrt (h n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hh
  have he : Tendsto (fun n => (k n:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h n:ℝ)^2+
      A.C₃/3*(h n:ℝ)*Real.sqrt (h n))) atTop (𝓝 0) := by
    have hh' := ht.mul (((tendsto_const_nhds (x := A.Cx*M^2+A.Ccross*M/2)).mul hh).add
      ((tendsto_const_nhds (x := A.C₃/3)).mul hs))
    convert! hh' using 1
    · ext n; ring
    · simp
  have hb : Tendsto (fun n => A.F q.1 q.2+(k n:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h n:ℝ)^2+
      A.C₃/3*(h n:ℝ)*Real.sqrt (h n))) atTop (𝓝 (A.F q.1 q.2)) := by
    simpa using tendsto_const_nhds.add he
  exact le_of_tendsto_of_tendsto hi hb (Filter.Eventually.of_forall fun n =>
    expected_frozen_nodes hW A v mv (U n) (mU n) (h n) q (hU n) hv (hg n) (k n))

end SLEExactGauge.BrownianCalculus

 

noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.EulerGeneral

variable {Vspace : Type*} [NormedAddCommGroup Vspace] [NormedSpace ℝ Vspace] [CompleteSpace Vspace]

def nodes (f : ℝ → Vspace → Vspace) (h : ℝ) (z : Vspace) : ℕ → Vspace
  | 0 => z
  | k+1 => nodes f h z k + h • f ((k:ℝ)*h) (nodes f h z k)

def interpolate (f : ℝ → Vspace → Vspace) (h : ℝ) (z : Vspace) (t : ℝ) : Vspace :=
  let k := ⌊t/h⌋₊
  let w := t/h-(k:ℝ)
  (1-w) • nodes f h z k + w • nodes f h z (k+1)

lemma finite_gronwall {e : ℕ → ℝ} {L h ε : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hε : 0 ≤ ε) (he0 : e 0 ≤ 0) {N : ℕ}
    (hrec : ∀ k < N, e (k+1) ≤ (1+L*h)*e k + ε*h) :
    e N ≤ ε*((N:ℝ)*h)*Real.exp (L*((N:ℝ)*h)) := by
  have hstep : ∀ k ≤ N, e k ≤ ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h)) := by
    intro k hk
    induction k with
    | zero => simpa using he0
    | succ k ih =>
      have hi := ih (by omega)
      have hk' : k < N := by omega
      have he : 1+L*h ≤ Real.exp (L*h) := by
        simpa only [add_comm] using Real.add_one_le_exp (L*h)
      have he1 : 1 ≤ Real.exp (L*(((k+1:ℕ):ℝ)*h)) :=
        Real.one_le_exp (by positivity)
      calc e (k+1)
          ≤ (1+L*h)*(ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h))) + ε*h :=
            (hrec k hk').trans (add_le_add (mul_le_mul_of_nonneg_left hi
              (show 0 ≤ 1+L*h from by positivity)) le_rfl)
        _ ≤ Real.exp (L*h)*(ε*((k:ℝ)*h)*Real.exp (L*((k:ℝ)*h))) +
            (ε*h)*Real.exp (L*(((k+1:ℕ):ℝ)*h)) := by
          exact add_le_add (mul_le_mul_of_nonneg_right he (by positivity))
            (le_mul_of_one_le_right (mul_nonneg hε hh) he1)
        _ = ε*(((k+1:ℕ):ℝ)*h)*Real.exp (L*(((k+1:ℕ):ℝ)*h)) := by
          have hex : Real.exp (L*(((k+1:ℕ):ℝ)*h)) =
              Real.exp (L*h)*Real.exp (L*((k:ℝ)*h)) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring
          rw [hex]
          push_cast
          ring
  exact hstep N le_rfl

omit [CompleteSpace Vspace] in
lemma nodes_error {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {z : Vspace} {L h ε T : ℝ}
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hg0 : g 0 = z)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y, ‖f t x-f t y‖ ≤ L*‖x-y‖)
    (hres : ∀ k : ℕ, ((k+1:ℕ):ℝ)*h ≤ T →
      ‖g (((k+1:ℕ):ℝ)*h) - g ((k:ℝ)*h) - h • f ((k:ℝ)*h) (g ((k:ℝ)*h))‖ ≤ ε*h)
    (N : ℕ) (hN : (N:ℝ)*h ≤ T) :
    ‖nodes f h z N - g ((N:ℝ)*h)‖ ≤ ε*T*Real.exp (L*T) := by
  have hrec (k : ℕ) (hk : k < N) :
      ‖nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h)‖ ≤
        (1+L*h)*‖nodes f h z k-g ((k:ℝ)*h)‖ + ε*h := by
    have hkT : ((k+1:ℕ):ℝ)*h ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hh).trans hN
    have hk0 : 0 ≤ (k:ℝ)*h := by positivity
    have hkT' : (k:ℝ)*h ≤ T := (by push_cast; nlinarith : (k:ℝ)*h ≤ ((k+1:ℕ):ℝ)*h).trans hkT
    let r := g (((k+1:ℕ):ℝ)*h)-g ((k:ℝ)*h)-h • f ((k:ℝ)*h) (g ((k:ℝ)*h))
    have he : nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h) =
        (nodes f h z k-g ((k:ℝ)*h)) +
          h • (f ((k:ℝ)*h) (nodes f h z k)-f ((k:ℝ)*h) (g ((k:ℝ)*h))) - r := by
      simp only [nodes, r, smul_sub]
      abel
    rw [he]
    calc _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖ +
          ‖h • (f ((k:ℝ)*h) (nodes f h z k)-f ((k:ℝ)*h) (g ((k:ℝ)*h)))‖ + ‖r‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖ +
          h*(L*‖nodes f h z k-g ((k:ℝ)*h)‖) + ε*h := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (hlip _ ⟨hk0,hkT'⟩ _ _) hh)) (hres k hkT)
      _ = _ := by ring
  have hb := finite_gronwall (e := fun k => ‖nodes f h z k-g ((k:ℝ)*h)‖)
    hL hh hε (by simp [nodes, hg0]) hrec
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg _) hh).trans hN
  exact hb.trans (by gcongr)

omit [CompleteSpace Vspace] in
lemma residual_bound {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {T s h ε : ℝ}
    (hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (f t (g t)) (Icc 0 T) t)
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s+h ≤ T)
    (hosc : ∀ t ∈ Icc s (s+h), ‖f t (g t)-f s (g s)‖ ≤ ε) :
    ‖g (s+h)-g s-h • f s (g s)‖ ≤ ε*h := by
  have hsub : Icc s (s+h) ⊆ Icc 0 T := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsh⟩
  have hd (t : ℝ) (ht : t ∈ Icc s (s+h)) :
      HasDerivWithinAt (fun u => g u-u • f s (g s))
        (f t (g t)-f s (g s)) (Icc s (s+h)) t := by
    convert! ((hder t (hsub ht)).mono hsub).sub
      (((hasDerivAt_id t).smul_const (f s (g s))).hasDerivWithinAt) using 1
    simp only [one_smul]
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hosc
    (convex_Icc s (s+h)) (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith))
  have he : (g (s+h)-(s+h) • f s (g s))-(g s-s • f s (g s)) =
      g (s+h)-g s-h • f s (g s) := by rw [add_smul]; abel
  simpa only [he, add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh] using hb

omit [CompleteSpace Vspace] in
lemma exists_residual_bound {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {T : ℝ}
    (hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (f t (g t)) (Icc 0 T) t)
    (hcf : ContinuousOn (fun t => f t (g t)) (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 ≤ h → h < δ → ∀ s : ℝ, 0 ≤ s → s+h ≤ T →
      ‖g (s+h)-g s-h • f s (g s)‖ ≤ ε*h := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hcf
  obtain ⟨δ,hδ,hb⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ, fun h hh hhδ s hs hsT => residual_bound hder hs hh hsT ?_⟩
  intro u hu
  apply le_of_lt
  have huT : u ∈ Icc 0 T := ⟨hs.trans hu.1, hu.2.trans hsT⟩
  have hsT' : s ∈ Icc 0 T := ⟨hs, by linarith⟩
  have hd : dist u s < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
    linarith [hu.2]
  simpa only [dist_eq_norm] using hb u huT s hsT' hd

omit [CompleteSpace Vspace] in
lemma norm_interpolate_sub_le {x y z : Vspace} {w E : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hx : ‖x-z‖ ≤ E) (hy : ‖y-z‖ ≤ E) :
    ‖(1-w) • x+w • y-z‖ ≤ E := by
  have he : (1-w) • x+w • y-z = (1-w) • (x-z)+w • (y-z) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc _ ≤ ‖(1-w) • (x-z)‖+‖w • (y-z)‖ := norm_add_le _ _
    _ = (1-w)*‖x-z‖+w*‖y-z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hw1), abs_of_nonneg hw]
    _ ≤ (1-w)*E+w*E := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hw1))
      (mul_le_mul_of_nonneg_left hy hw)
    _ = E := by ring

omit [CompleteSpace Vspace] in
lemma interpolate_error {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {z : Vspace} {L M h ε T t : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hh : 0 < h) (hε : 0 ≤ ε) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hres : ∀ k : ℕ, ((k+1:ℕ):ℝ)*h ≤ T →
      ‖g (((k+1:ℕ):ℝ)*h) - g ((k:ℝ)*h) - h • f ((k:ℝ)*h) (g ((k:ℝ)*h))‖ ≤ ε*h)
    (hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v|)
    (ht : 0 ≤ t) (htT : t+h ≤ T) :
    ‖interpolate f h z t-g t‖ ≤ ε*T*Real.exp (L*T)+M*h := by
  let k := ⌊t/h⌋₊
  have hf0 : (k:ℝ) ≤ t/h := Nat.floor_le (div_nonneg ht hh.le)
  have hf1 : t/h < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk0 : 0 ≤ (k:ℝ)*h := by positivity
  have hkt : (k:ℝ)*h ≤ t := (le_div_iff₀ hh).mp hf0
  have htks : t < ((k+1:ℕ):ℝ)*h := by
    push_cast
    exact (div_lt_iff₀ hh).mp hf1
  have hksT : ((k+1:ℕ):ℝ)*h ≤ T := by push_cast; nlinarith
  have hkT : (k:ℝ)*h ≤ T := hkt.trans (by linarith)
  have hw : 0 ≤ t/h-(k:ℝ) := by linarith
  have hw1 : t/h-(k:ℝ) ≤ 1 := by linarith
  apply norm_interpolate_sub_le hw hw1
  · calc _ ≤ ‖nodes f h z k-g ((k:ℝ)*h)‖+‖g ((k:ℝ)*h)-g t‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε*T*Real.exp (L*T)+M*h := add_le_add
        (nodes_error hL hh.le hε hg0 hlip hres k hkT)
        ((hpath _ ⟨hk0,hkT⟩ _ ⟨ht,by linarith⟩).trans (by
          rw [abs_of_nonpos (sub_nonpos.mpr hkt)]
          apply mul_le_mul_of_nonneg_left _ hM
          push_cast at htks
          linarith))
  · calc _ ≤ ‖nodes f h z (k+1)-g (((k+1:ℕ):ℝ)*h)‖+
          ‖g (((k+1:ℕ):ℝ)*h)-g t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε*T*Real.exp (L*T)+M*h := add_le_add
        (nodes_error hL hh.le hε hg0 hlip hres (k+1) hksT)
        ((hpath _ ⟨by positivity,hksT⟩ _ ⟨ht,by linarith⟩).trans (by
          rw [abs_of_nonneg (by linarith : 0 ≤ ((k+1:ℕ):ℝ)*h-t)]
          apply mul_le_mul_of_nonneg_left _ hM
          push_cast
          linarith))

omit [CompleteSpace Vspace] in
lemma converge {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {z : Vspace} {L M T t : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (ht : 0 ≤ t) (htT : t < T)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => interpolate f (h n) z t) atTop (𝓝 (g t)) := by
  have hT : 0 < T := lt_of_le_of_lt ht htT
  have hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v| := by
    intro u hu v hv
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 T) hv hu
  rw [Metric.tendsto_nhds]
  intro ε hε
  let E := T*Real.exp (L*T)
  have hE : 0 < E := mul_pos hT (Real.exp_pos _)
  let η := ε/(2*E)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hres⟩ := exists_residual_bound hder hcf hη
  have hev1 : ∀ᶠ n in atTop, h n < δ := (tendsto_order.1 hh0).2 δ hδ
  have hev2 : ∀ᶠ n in atTop, h n < T-t :=
    (tendsto_order.1 hh0).2 (T-t) (sub_pos.mpr htT)
  have hev3 : ∀ᶠ n in atTop, h n < ε/(2*(M+1)) :=
    (tendsto_order.1 hh0).2 _ (div_pos hε (by positivity))
  filter_upwards [hev1,hev2,hev3] with n hnδ hnT hnε
  rw [dist_eq_norm]
  have hb := interpolate_error hL hM (hh n) hη.le hg0 hlip
    (fun k hk => by
      have hc : ((k+1:ℕ):ℝ)*h n = (k:ℝ)*h n+h n := by push_cast; ring
      rw [hc] at hk ⊢
      exact hres (h n) (hh n).le hnδ ((k:ℝ)*h n) (mul_nonneg (Nat.cast_nonneg _) (hh n).le) hk)
    hpath ht (by linarith : t+h n ≤ T)
  apply lt_of_le_of_lt hb
  have hηE : η*T*Real.exp (L*T) = ε/2 := by
    dsimp [η, E]
    field_simp
  have hsmall : M*h n < ε/2 := by
    have hhε := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hnε
    nlinarith [hh n]
  rw [hηE]
  linarith

omit [CompleteSpace Vspace] in
lemma converge_uniformOn {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {z : Vspace} {L M T U : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Icc 0 T, HasDerivWithinAt g (f u (g u)) (Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Icc 0 T))
    (hbound : ∀ u ∈ Icc 0 T, ‖f u (g u)‖ ≤ M)
    (hU : 0 ≤ U) (hUT : U < T)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => interpolate f (h n) z) g atTop (Icc 0 U) := by
  have hT : 0 < T := lt_of_le_of_lt hU hUT
  have hpath : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖g u-g v‖ ≤ M*|u-v| := by
    intro u hu v hv
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 T) hv hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let E := T*Real.exp (L*T)
  have hE : 0 < E := mul_pos hT (Real.exp_pos _)
  let η := ε/(2*E)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hres⟩ := exists_residual_bound hder hcf hη
  have hev1 : ∀ᶠ n in atTop, h n < δ := (tendsto_order.1 hh0).2 δ hδ
  have hev2 : ∀ᶠ n in atTop, h n < T-U :=
    (tendsto_order.1 hh0).2 (T-U) (sub_pos.mpr hUT)
  have hev3 : ∀ᶠ n in atTop, h n < ε/(2*(M+1)) :=
    (tendsto_order.1 hh0).2 _ (div_pos hε (by positivity))
  filter_upwards [hev1,hev2,hev3] with n hnδ hnT hnε
  intro t ht
  rw [dist_comm, dist_eq_norm]
  have hb := interpolate_error hL hM (hh n) hη.le hg0 hlip
    (fun k hk => by
      have hc : ((k+1:ℕ):ℝ)*h n = (k:ℝ)*h n+h n := by push_cast; ring
      rw [hc] at hk ⊢
      exact hres (h n) (hh n).le hnδ ((k:ℝ)*h n)
        (mul_nonneg (Nat.cast_nonneg _) (hh n).le) hk)
    hpath ht.1 (by linarith [ht.2] : t+h n ≤ T)
  apply lt_of_le_of_lt hb
  have hηE : η*T*Real.exp (L*T) = ε/2 := by
    dsimp [η, E]
    field_simp
  have hsmall : M*h n < ε/2 := by
    have hhε := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hnε
    nlinarith [hh n]
  rw [hηE]
  linarith

end SLEExactGauge.EulerGeneral

namespace SLEExactGauge.EulerGeneral
variable {Vspace : Type*} [NormedAddCommGroup Vspace] [NormedSpace ℝ Vspace] [CompleteSpace Vspace]

omit [CompleteSpace Vspace] in
lemma norm_nodes_sub_interpolate {f : ℝ → Vspace → Vspace} {h t M : ℝ} {z : Vspace}
    (hh : 0 < h) (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hf : ∀ u ≥ 0, ∀ w, ‖f u w‖ ≤ M) :
    ‖nodes f h z ⌊t/h⌋₊ - interpolate f h z t‖ ≤ h*M := by
  let k := ⌊t/h⌋₊
  let w := t/h-(k:ℝ)
  have hfloor : (k:ℝ) ≤ t/h := Nat.floor_le (div_nonneg ht hh.le)
  have hlt : t/h < (k:ℝ)+1 := Nat.lt_floor_add_one (t/h)
  have hw : 0 ≤ w := sub_nonneg.mpr hfloor
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  have he : nodes f h z k - interpolate f h z t =
      -(w*h) • f ((k:ℝ)*h) (nodes f h z k) := by
    dsimp only [interpolate]
    change nodes f h z k- ((1-w) • nodes f h z k+w • nodes f h z (k+1)) = _
    rw [nodes, smul_add, sub_smul, one_smul, smul_smul]
    module
  change ‖nodes f h z k - interpolate f h z t‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hw hh.le)]
  calc w*h*‖f ((k:ℝ)*h) (nodes f h z k)‖
      ≤ w*h*M := mul_le_mul_of_nonneg_left (hf _ (by positivity) _) (by positivity)
    _ ≤ h*M := by nlinarith [mul_nonneg hh.le hM]

omit [CompleteSpace Vspace] in
lemma nodes_converge {f : ℝ → Vspace → Vspace} {g : ℝ → Vspace} {z : Vspace} {L M T t : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hg0 : g 0 = z)
    (hlip : ∀ u ∈ Set.Icc 0 T, ∀ x y, ‖f u x-f u y‖ ≤ L*‖x-y‖)
    (hder : ∀ u ∈ Set.Icc 0 T, HasDerivWithinAt g (f u (g u)) (Set.Icc 0 T) u)
    (hcf : ContinuousOn (fun u => f u (g u)) (Set.Icc 0 T))
    (hbound : ∀ u ≥ 0, ∀ w, ‖f u w‖ ≤ M)
    (ht : 0 ≤ t) (htT : t < T)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => nodes f (h n) z ⌊t/h n⌋₊) atTop (𝓝 (g t)) := by
  have hi := converge hL hM hg0 hlip hder hcf (fun u hu => hbound u hu.1 _) ht htT hh hh0
  have hd : Tendsto (fun n => nodes f (h n) z ⌊t/h n⌋₊-interpolate f (h n) z t)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => norm_nodes_sub_interpolate (hh n) ht hM hbound)
    simpa using hh0.mul_const M
  have he := hd.add hi
  simpa only [sub_add_cancel, zero_add] using he

lemma mesh_times_converge {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => (⌊t/h n⌋₊:ℝ)*h n) atTop (𝓝 t) := by
  have hb (n : ℕ) : 0 ≤ t-(⌊t/h n⌋₊:ℝ)*h n ∧ t-(⌊t/h n⌋₊:ℝ)*h n ≤ h n := by
    have hl := Nat.floor_le (div_nonneg ht (hh n).le)
    have hu := Nat.lt_floor_add_one (t/h n)
    have hl' := (le_div_iff₀ (hh n)).mp hl
    have hu' := (div_lt_iff₀ (hh n)).mp hu
    constructor <;> linarith
  have hz : Tendsto (fun n => t-(⌊t/h n⌋₊:ℝ)*h n) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2) hh0
  have he := (tendsto_const_nhds (x := t) (f := atTop)).sub hz
  simpa only [sub_sub_cancel, sub_zero] using he

end SLEExactGauge.EulerGeneral

namespace SLEExactGauge.EulerGeneral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end SLEExactGauge.EulerGeneral
end
end
end
end
end
end
end

end OAI
