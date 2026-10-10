import OAI.Geometry.RCD.Heat.CanonicalLocalLower

namespace OAI

/-! # A quantitative power lower bound for short-time heat kernels

A fixed near-diagonal estimate is iterated a prescribed number of times.
The number of steps remains explicit, allowing a Gaussian rate afterward.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_power_lower :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ ∀ (N : ℕ), 0 < N →
      ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x y : X,
        (dist x y)^2 ≤ (N:ℝ)*t/4 →
        b^N/(hausdorff n X).real (ball y (Real.sqrt t)) ≤
          hX.canonicalHeatKernel hn p t x y := by
  obtain ⟨c,hc,hnear0⟩ := hX.canonicalHeatKernel_local_lower hn p 1 zero_le_one
  let δ : ℝ := 1
  let τ : ℝ := 1
  have hδ : 0 < δ := by norm_num [δ]
  have hδ1 : δ ≤ 1 := le_rfl
  have hτ : 0 < τ := by norm_num [τ]
  have hnear (s : ℝ) (hs : 0 < s) (hsτ : s ≤ τ) (v w : X)
      (hd : dist v w ≤ δ*Real.sqrt s) :
      c/(hausdorff n X).real (ball w (Real.sqrt s)) ≤ hX.canonicalHeatKernel hn p s v w := by
    apply hnear0 s hs hsτ v w
    dsimp only [δ] at hd
    nlinarith only [Real.sq_sqrt hs.le,dist_nonneg (x := v) (y := w),Real.sqrt_nonneg s,hd]
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (abs_nonneg K)
    (by positivity : 0 < δ/4) (by linarith : δ/4 ≤ 1)
  let b := min (1/2:ℝ) (c/D)
  have hb : 0 < b := lt_min (by norm_num) (div_pos hc (zero_lt_one.trans_le hD))
  refine ⟨b,hb,(min_le_left _ _).trans_lt (by norm_num),?_⟩
  intro N hNnat t ht ht1 x y hdist
  have hN0 : (0:ℝ) < N := by exact_mod_cast hNnat
  have hNτ : 1 ≤ τ*(N:ℝ) := by dsimp only [τ]; norm_num; exact_mod_cast hNnat
  let A : ℝ := (N:ℝ)/4
  have hNA : 4*A ≤ δ^2*(N:ℝ) := by dsimp only [A,δ]; ring_nf; exact le_rfl
  have hdist : (dist x y)^2 ≤ A*t := by dsimp only [A]; nlinarith only [hdist]
  let s := t/(N:ℝ)
  let T := Real.sqrt s
  let r := δ/4*T
  have hs : 0 < s := div_pos ht hN0
  have hNs : s*(N:ℝ) = t := div_mul_cancel₀ _ hN0.ne'
  have hsτ : s ≤ τ := (div_le_iff₀ hN0).mpr (ht1.trans hNτ)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNnat
  have hst : s ≤ t := div_le_self ht.le hN1
  have hs1 : s ≤ 1 := hst.trans ht1
  have hT : 0 < T := Real.sqrt_pos.mpr hs
  have hT2 : T^2 = s := Real.sq_sqrt hs.le
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrT : r ≤ T := by dsimp only [r]; nlinarith only [hδ1,hT]
  have hcurv : -|K| ≤ K*T^2 := by
    rw [hT2]
    have h1 := mul_le_mul_of_nonneg_right (neg_abs_le K) hs.le
    have h2 := mul_le_mul_of_nonpos_left hs1 (neg_nonpos.mpr (abs_nonneg K))
    nlinarith only [h1,h2]
  obtain ⟨γ,hγ0,hγ1,hγ⟩ := hX.geodesic x y
  let θ (i : ℕ) : Time := ⟨min ((i:ℝ)/N) 1,le_min (by positivity) zero_le_one,min_le_right _ _⟩
  let z (i : ℕ) := γ (θ i)
  let V (i : ℕ) := (hausdorff n X).real (ball (z i) r)
  have hV (i : ℕ) : 0 < V i := ENNReal.toReal_pos (hX.fullSupport _ _ hr).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hθ (i : ℕ) (hi : i ≤ N) : (θ i : ℝ) = (i:ℝ)/N :=
    min_eq_left ((div_le_one hN0).mpr (by exact_mod_cast hi))
  have hz0 : z 0 = x := by
    have he : θ 0 = 0 := by apply Subtype.ext; simp [θ]
    simpa only [z,he] using hγ0
  have hzN : z N = y := by
    have he : θ N = 1 := by apply Subtype.ext; rw [hθ N le_rfl,div_self hN0.ne']; rfl
    simpa only [z,he] using hγ1
  have hsmall : dist x y/(N:ℝ) ≤ δ/2*T := by
    apply (sq_le_sq₀ (div_nonneg dist_nonneg hN0.le) (by positivity)).mp
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN0)).mp
    have he : (N:ℝ)^2*(dist x y/(N:ℝ))^2 = (dist x y)^2 := by field_simp
    rw [he]
    have hnt := mul_le_mul_of_nonneg_right hNA ht.le
    have hident : (N:ℝ)^2*(δ/2*T)^2 = δ^2*(N:ℝ)*t/4 := by
      rw [mul_pow,hT2]
      linear_combination (δ^2*(N:ℝ)/4)*hNs
    rw [hident]
    nlinarith only [hnt,hdist]
  have hstep (i : ℕ) (hi : i < N) : dist (z i) (z (i+1)) ≤ δ/2*T := by
    have he : dist (z i) (z (i+1)) = dist x y/(N:ℝ) := by
      dsimp only [z]
      rw [hγ,hθ i hi.le,hθ (i+1) (by omega),hγ0,hγ1]
      have hi' : (i:ℝ)/(N:ℝ)-((i+1:ℕ):ℝ)/N = -(N:ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      rw [hi',abs_neg,abs_of_pos (inv_pos.mpr hN0)]
      ring
    exact he.trans_le hsmall
  have htransition (i : ℕ) (hi : i < N) (v w : X)
      (hv : v ∈ ball (z i) r) (hw : w ∈ ball (z (i+1)) r) :
      b/V (i+1) ≤ hX.canonicalHeatKernel hn p s v w := by
    have hdist' : dist v w ≤ δ*T := by
      have h1 := dist_triangle v (z i) w
      have h2 := dist_triangle (z i) (z (i+1)) w
      have hv' := mem_ball.mp hv
      have hw' : dist (z (i+1)) w < r := by simpa only [dist_comm] using mem_ball.mp hw
      have hi' := hstep i hi
      dsimp only [r] at hv' hw'
      linarith only [h1,h2,hv',hw',hi']
    have hnear' := hnear s hs hsτ v w hdist'
    have hVW : (hausdorff n X).real (ball w T) ≤ D*V (i+1) :=
      hvol w T hT hcurv (z (i+1)) (by
        have hd : dist (z (i+1)) w ≤ r := by simpa only [dist_comm] using (mem_ball.mp hw).le
        exact hd.trans hrT)
    have hW : 0 < (hausdorff n X).real (ball w T) :=
      ENNReal.toReal_pos (hX.fullSupport w T hT).ne' (hX.finiteOnBounded _ isBounded_ball).ne
    calc
      _ ≤ (c/D)/V (i+1) := div_le_div_of_nonneg_right (min_le_right _ _) (hV (i+1)).le
      _ = c/(D*V (i+1)) := by ring
      _ ≤ c/(hausdorff n X).real (ball w T) :=
        div_le_div_of_nonneg_left hc.le hW hVW
      _ ≤ _ := hnear'
  have hall (i : ℕ) : i ≤ N → 0 < i → ∀ w ∈ ball (z i) r,
      b^i/V i ≤ hX.canonicalHeatKernel hn p ((i:ℝ)*s) x w := by
    induction i with
    | zero => omega
    | succ i ih =>
      intro hi _ w hw
      by_cases hi0 : i = 0
      · subst i
        simpa only [Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,one_mul,pow_one] using
          htransition 0 (by omega) x w (by rw [hz0]; exact mem_ball_self hr) hw
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hh := hX.canonicalHeatKernel_lower_from_set hn p
          (mul_pos (by exact_mod_cast hipos) hs) hs (div_nonneg (pow_pos hb i).le (hV i).le)
          (div_nonneg hb.le (hV (i+1)).le) x w measurableSet_ball
          (hX.finiteOnBounded _ isBounded_ball).ne (ih (by omega) hipos)
          (fun v hv => htransition i (by omega) v w hv hw)
        have he : b^i/V i*(b/V (i+1))*V i = b^(i+1)/V (i+1) := by
          rw [pow_succ]
          field_simp [(hV i).ne']
        rw [he] at hh
        simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh
  have hh := hall N le_rfl hNnat y (by rw [hzN]; exact mem_ball_self hr)
  have htime : (N:ℝ)*s = t := by nlinarith only [hNs]
  rw [htime] at hh
  apply le_trans _ hh
  apply div_le_div_of_nonneg_left (pow_pos hb N).le (hV N)
  dsimp only [V]
  rw [hzN]
  exact measureReal_mono (ball_subset_ball (hrT.trans (Real.sqrt_le_sqrt hst)))
    (hX.finiteOnBounded _ isBounded_ball).ne

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
