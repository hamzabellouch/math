import OAI.Geometry.RCD.Heat.CanonicalNearDiagonal

namespace OAI

/-! # Strict positivity at every positive time and pair of points

The near-diagonal lower bound propagates through the actual convolution
identity along a finite subdivision of a geodesic.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_pos_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x z y : X) (hxz : 0 < hX.canonicalHeatKernel hn p s x z)
    (hzy : 0 < hX.canonicalHeatKernel hn p t z y) :
    0 < hX.canonicalHeatKernel hn p (s+t) x y := by
  let μ := hausdorff n X
  let k := hX.canonicalHeatKernel hn p
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let := hX.openPos K n
  rw [← hk.convolution s t hs ht x y]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((hk.continuous_right s hs x).mul
      ((hk.continuous_right t ht y).congr (fun w => hk.symmetric t ht y w)))
    (hk.convolution_integrable s t hs ht x y)
    (fun w => mul_nonneg (hk.nonneg s hs x w) (hk.nonneg t ht w y))
  exact (mul_pos hxz hzy).ne'

theorem canonicalHeatKernel_pos (t : ℝ) (ht : 0 < t) (x y : X) :
    0 < hX.canonicalHeatKernel hn p t x y := by
  obtain ⟨c,δ,τ,hc,hδ,_hδ1,hτ,_hτ1,hnear⟩ := hX.canonicalHeatKernel_near_diagonal hn p
  obtain ⟨γ,hγ0,hγ1,hγ⟩ := hX.geodesic x y
  let d := dist x y
  obtain ⟨N,hN⟩ := exists_nat_gt (max (t/τ) (max (d^2/(δ^2*t)) 1))
  have hN0 : (0:ℝ) < N := by
    have hh := (le_max_right (t/τ) (max (d^2/(δ^2*t)) 1)).trans_lt hN
    have hh' := (le_max_right (d^2/(δ^2*t)) 1).trans_lt hh
    linarith
  have hNnat : 0 < N := by exact_mod_cast hN0
  let s := t/(N:ℝ)
  have hs : 0 < s := div_pos ht hN0
  have hsτ : s ≤ τ := by
    have hh := (le_max_left (t/τ) (max (d^2/(δ^2*t)) 1)).trans_lt hN
    apply (div_le_iff₀ hN0).mpr
    have hh' := (div_lt_iff₀ hτ).mp hh
    linarith
  have hstepdist : d/N ≤ δ*Real.sqrt s := by
    have hh := (le_max_left (d^2/(δ^2*t)) 1).trans
      (le_max_right (t/τ) (max (d^2/(δ^2*t)) 1)) |>.trans_lt hN
    have hh' := (div_lt_iff₀ (by positivity : 0 < δ^2*t)).mp hh
    have he : s*(N:ℝ) = t := div_mul_cancel₀ _ hN0.ne'
    have hss := Real.sq_sqrt hs.le
    apply (sq_le_sq₀ (div_nonneg dist_nonneg hN0.le) (by positivity)).mp
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN0)).mp
    have he' : (d/(N:ℝ))^2*(N:ℝ)^2 = d^2 := by field_simp
    change (N:ℝ)^2*(d/(N:ℝ))^2 ≤ (N:ℝ)^2*(δ*Real.sqrt s)^2
    rw [mul_comm ((N:ℝ)^2) ((d/(N:ℝ))^2),he']
    rw [mul_pow,hss]
    have he'' := congrArg (fun v : ℝ => v*(δ^2*(N:ℝ))) he
    nlinarith only [hh',he'']
  let θ (i : ℕ) : Time := ⟨min ((i:ℝ)/N) 1,le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hθ (i : ℕ) (hi : i ≤ N) : (θ i : ℝ) = (i:ℝ)/N := by
    apply min_eq_left
    exact (div_le_one hN0).mpr (by exact_mod_cast hi)
  have hθ0 : θ 0 = 0 := by apply Subtype.ext; simp [θ]
  have hθN : θ N = 1 := by
    apply Subtype.ext
    rw [hθ N le_rfl,div_self hN0.ne']
    rfl
  have hstep (i : ℕ) (hi : i < N) : dist (γ (θ i)) (γ (θ (i+1))) = d/N := by
    rw [hγ,hθ i hi.le,hθ (i+1) (by omega),hγ0,hγ1]
    have he : (i:ℝ)/(N:ℝ)-((i+1:ℕ):ℝ)/N = -(N:ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [he,abs_neg,abs_of_pos (inv_pos.mpr hN0)]
    dsimp only [d]
    ring
  have hpstep (i : ℕ) (hi : i < N) :
      0 < hX.canonicalHeatKernel hn p s (γ (θ i)) (γ (θ (i+1))) := by
    have hh := hnear s hs hsτ (γ (θ i)) (γ (θ (i+1))) (by rw [hstep i hi]; exact hstepdist)
    have hV : 0 < (hausdorff n X).real (ball (γ (θ (i+1))) (Real.sqrt s)) :=
      ENNReal.toReal_pos (hX.fullSupport _ _ (Real.sqrt_pos.mpr hs)).ne'
        (hX.finiteOnBounded _ isBounded_ball).ne
    exact (div_pos hc hV).trans_le hh
  have hall (i : ℕ) : i ≤ N → 0 < i →
      0 < hX.canonicalHeatKernel hn p ((i:ℝ)*s) x (γ (θ i)) := by
    induction i with
    | zero => omega
    | succ i ih =>
      intro hi _
      by_cases hi0 : i = 0
      · subst i
        simpa only [Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,one_mul,hθ0,hγ0] using hpstep 0 (by omega)
      · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
        have hh := hX.canonicalHeatKernel_pos_add hn p
          (mul_pos (by exact_mod_cast hpos) hs) hs x (γ (θ i)) (γ (θ (i+1)))
          (ih (by omega) hpos) (hpstep i (by omega))
        simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh
  have hh := hall N le_rfl hNnat
  have he : (N:ℝ)*s = t := mul_div_cancel₀ _ hN0.ne'
  simpa only [he,hθN,hγ1] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
