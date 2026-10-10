import OAI.Geometry.RCD.Coordinates.RegularDirichletCore

namespace OAI

/-! # Support of the actual weak Laplacian

Locality against cutoff multiples and density of the Sobolev domain show
that a compactly supported function has no Laplacian outside its support.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (Q : QuadraticCheegerEnergy μ)

theorem IsWeakLaplacian.cutoff_mul_eq_zero
    {f : SobolevSpace μ Q} {d : Lp ℝ 2 μ} (hd : IsWeakLaplacian μ Q f d)
    (χ : X → ℝ) {L B : ℝ≥0} (hχ : LipschitzWith L χ)
    (hc : HasCompactSupport χ) (hB : ∀ x, |χ x| ≤ B) (h0 : ∀ x, 0 ≤ χ x)
    (hf : ∀ᵐ x ∂μ, χ x ≠ 0 → SobolevSpace.toLp μ Q f x = 0) :
    (fun x => χ x*d x) =ᵐ[μ] 0 := by
  let M := SobolevSpace.cutoffCLM μ Q hχ hc hB h0
  have hm : MemLp χ ∞ μ := memLp_top_of_bound hχ.continuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hq : MemLp (fun x => χ x*d x) 2 μ := hm.mul (Lp.memLp d)
  let q := hq.toLp _
  have hzero (g : SobolevSpace μ Q) : energyForm μ Q f (M g) = 0 := by
    rw [← integral_localGamma_eq_energyForm]
    apply integral_eq_zero_of_ae
    filter_upwards [hf,SobolevSpace.cutoffCLM_coe μ Q hχ hc hB h0 g,
      localGamma_zero_on_level μ Q f (M g) 0,
      localGamma_zero_on_level μ Q (M g) f 0,
      localGamma_comm μ Q f (M g)] with x hx he hz hw hcomm
    by_cases hχx : χ x = 0
    · exact hcomm.trans (hw (he.trans (by rw [hχx,zero_mul])))
    · exact hz (hx hχx)
  have hi (g : SobolevSpace μ Q) : inner ℝ q (SobolevSpace.toLp μ Q g) = 0 := by
    have he : inner ℝ q (SobolevSpace.toLp μ Q g) =
        inner ℝ d (SobolevSpace.toLp μ Q (M g)) := by
      rw [L2.inner_def,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp,SobolevSpace.cutoffCLM_coe μ Q hχ hc hB h0 g]
        with x hqx hmx
      simp only [Real.inner_apply]
      change q x * SobolevSpace.toLp μ Q g x = d x * SobolevSpace.toLp μ Q (M g) x
      change q x = _ at hqx
      change SobolevSpace.toLp μ Q (M g) x = _ at hmx
      rw [hqx,hmx]
      ring
    rw [he]
    have hh := hd (M g)
    rw [hzero g] at hh
    linarith
  have heq : (fun a : Lp ℝ 2 μ => inner ℝ q a) = fun _ => (0:ℝ) :=
    (SobolevSpace.toLp_denseRange μ Q).equalizer (by fun_prop) (by fun_prop) (funext hi)
  have hq0 : q = 0 := inner_self_eq_zero.mp (congrFun heq q)
  have hz : (q : X → ℝ) =ᵐ[μ] 0 := by
    rw [hq0]
    exact Lp.coeFn_zero ℝ 2 μ
  exact hq.coeFn_toLp.symm.trans hz

theorem IsWeakLaplacian.zero_off_closedBall
    {f : SobolevSpace μ Q} {d : Lp ℝ 2 μ} (hd : IsWeakLaplacian μ Q f d)
    (z : X) (r : ℝ)
    (hf : ∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q f x = 0) :
    ∀ᵐ x ∂μ, x ∉ closedBall z r → d x = 0 := by
  let a := fun x => min (max (dist x z-r) 0) 1
  have hs : LipschitzWith 1 (fun x => dist x z-r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right,NNReal.coe_one,one_mul]
      using (LipschitzWith.dist_left z).dist_le_mul x y
  have ha : LipschitzWith 1 a := (hs.max_const 0).min_const 1
  have ha0 (x : X) : 0 ≤ a x := le_min (le_max_right _ _) zero_le_one
  have haB (x : X) : |a x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (ha0 x)]
    exact min_le_right _ _
  let χ := fun k : ℕ => fun x => radialCutoff z ((k:ℝ)+1) x*a x
  have hb (k : ℕ) (x : X) : |radialCutoff z ((k:ℝ)+1) x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds z _ x).1]
    exact (radialCutoff_bounds z _ x).2
  have hprod (k : ℕ) : (fun x => χ k x*d x) =ᵐ[μ] 0 := by
    have hk : 0 < (k:ℝ)+1 := by positivity
    have hχ := lipschitzWith_mul_of_support_bound (radialCutoff_lipschitz z hk) ha
      (hb k) (fun x _ => haB x)
    apply hd.cutoff_mul_eq_zero μ Q (χ k) hχ
      ((radialCutoff_hasCompactSupport z hk).mul_right)
      (B := 1)
    · intro x
      rw [abs_mul]
      exact (mul_le_mul (hb k x) (haB x) (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
    · intro x
      exact mul_nonneg (radialCutoff_bounds z _ x).1 (ha0 x)
    · filter_upwards [hf] with x hx hχx
      apply hx
      intro hin
      have hz : a x = 0 := by
        dsimp only [a]
        rw [max_eq_right (sub_nonpos.mpr hin),min_eq_left zero_le_one]
      exact hχx (by dsimp only [χ]; rw [hz,mul_zero])
  filter_upwards [ae_all_iff.mpr hprod] with x hx hout
  obtain ⟨k,hk⟩ := exists_nat_gt (dist x z)
  have hk0 : 0 < (k:ℝ)+1 := by positivity
  have hax : 0 < a x := lt_min (lt_max_of_lt_left (sub_pos.mpr (lt_of_not_ge hout))) zero_lt_one
  have hχx : χ k x ≠ 0 := by
    dsimp only [χ]
    rw [radialCutoff_eq_one z hk0 (by rw [dist_comm]; linarith),one_mul]
    exact ne_of_gt hax
  exact (mul_eq_zero.mp (hx k)).resolve_left hχx

end RegularPointCoordinates

end

end OAI
