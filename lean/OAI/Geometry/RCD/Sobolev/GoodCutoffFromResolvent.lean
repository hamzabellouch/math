import OAI.Geometry.RCD.Sobolev.UniformRadialResolvent
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Good Laplacian cutoffs from the actual RCD resolvent

A scalar plateau applied to a radial resolvent yields the exact inner and
outer radii used by the chart argument. Its differentiated formula gives
locality of the Laplacian on both constant regions.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

private theorem boundedLaplacian_comp_C2_formula (f : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d) {v : X → ℝ} {L D : ℝ≥0}
    (hv : LipschitzWith L v) (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ] v)
    (hD : ∀ᵐ x ∂μ, |d x| ≤ D)
    {φ ψ χ : ℝ → ℝ} {C J : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0=0)
    (hψ : LipschitzWith J ψ) (hψ0 : ψ 0=0)
    (hχ : Continuous χ) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (hdψ : ∀ a, HasDerivAt ψ (χ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) (hE : ∀ a, |χ a| ≤ E) :
    ∃ q : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) q ∧
      (∀ᵐ x ∂μ, |q x| ≤ (B*D+E*L^2:ℝ≥0)) ∧
      (∀ᵐ x ∂μ, q x = ψ (v x)*d x + χ (v x)*localGamma μ hQ f f x) := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.minimalSlope μ hQ f
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ G x := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)
  have hGL := SobolevSpace.minimalSlope_le_lipschitz μ hQ f hv hf
  have hGs : MemLp (fun x => G x^2) 2 μ := by
    apply (Lp.memLp G).of_le_mul (c := (L:ℝ)) ((Lp.aestronglyMeasurable G).pow 2)
    filter_upwards [hG0,hGL] with x h0 hL
    change |G x^2| ≤ (L:ℝ)*|G x|
    rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg h0]
    change G x ≤ L at hL
    nlinarith
  have hmψ : MemLp (fun x => ψ (F x)) ∞ μ :=
    memLp_top_of_bound (hψ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)) B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (F x))
  have hmχ : MemLp (fun x => χ (F x)) ∞ μ :=
    memLp_top_of_bound (hχ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)) E
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (F x))
  let Q (x : X) := ψ (F x)*d x+χ (F x)*G x^2
  have hm : MemLp Q 2 μ := by
    simpa only [Q, Pi.add_apply, Pi.mul_apply, mul_comm] using!
      ((Lp.memLp d).mul hmψ).add (hGs.mul hmχ)
  let q := hm.toLp Q
  have heq : ⇑q =ᵐ[μ] Q := hm.coeFn_toLp
  refine ⟨q,weakLaplacian_comp_C2 μ hQ f d q hd hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE ?_,?_,?_⟩
  · filter_upwards [heq,localGamma_self μ hQ f] with x hx hg
    rw [hx,hg]
  · filter_upwards [heq,hD,hG0,hGL] with x hx hd h0 hL
    rw [hx]
    change |ψ (F x)*d x+χ (F x)*G x^2| ≤ (B:ℝ)*D+E*(L:ℝ)^2
    calc
      _ ≤ |ψ (F x)*d x|+|χ (F x)*G x^2| := abs_add_le _ _
      _ ≤ (B:ℝ)*D+E*(L:ℝ)^2 := by
        simp only [abs_mul,abs_pow,abs_of_nonneg h0]
        exact add_le_add (mul_le_mul (hB _) hd (abs_nonneg _) B.coe_nonneg)
          (mul_le_mul (hE _) ((sq_le_sq₀ h0 L.coe_nonneg).mpr hL) (sq_nonneg _) E.coe_nonneg)

  · filter_upwards [heq, hf, localGamma_self μ hQ f] with x hx hvx hgamma
    rw [hx]
    dsimp only [Q, F, G]
    rw [hvx, hgamma]


omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts μ] in
private theorem plateau_derivatives_zero {φ ψ χ : ℝ → ℝ}
    (hdφ : ∀ a, HasDerivAt φ (ψ a) a) (hdψ : ∀ a, HasDerivAt ψ (χ a) a)
    {a c : ℝ} (h : φ =ᶠ[𝓝 a] fun _ => c) : ψ a = 0 ∧ χ a = 0 := by
  have hz : ψ =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [eventually_eventually_nhds.mpr h] with b hb
    have hb' : φ =ᶠ[𝓝 b] fun _ => c := hb
    exact (hdφ b).unique ((hasDerivAt_const b c).congr_of_eventuallyEq hb')
  exact ⟨hz.self_of_nhds, (hdψ a).unique
    ((hasDerivAt_const a 0).congr_of_eventuallyEq hz)⟩


variable {μ hQ}

/-- The curvature-dimension condition and heat resolvents produce a cutoff
with uniformly controlled gradient and Laplacian. -/
theorem NoncollapsedRCD.goodCutoffInput_bounded {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (a : ℝ) (ha : 0 ≤ a) :
    2 ≤ n → ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r →
      -a ≤ K * r ^ 2 → Nonempty (GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C) := by
  intro hn
  obtain ⟨D, hD, hresolvent⟩ := hX.uniform_radial_resolvent_bounded hn a ha
  obtain ⟨φ, ψ, χ, C, J, B, E, hφ, hψ, hχ, hdφ, hdψ, hB, hE,
    hφ0, hψ0, hφbounds, hφzero, hφone⟩ := exists_smooth_scalar_cutoff
  let CC : ℝ := (2*C+1)+(2048*B*D+4*E)
  have hCC : 1 ≤ CC := by
    dsimp only [CC]
    have hD0 : 0 ≤ D := zero_le_one.trans hD
    nlinarith only [C.coe_nonneg, B.coe_nonneg, E.coe_nonneg, mul_nonneg B.coe_nonneg hD0]
  refine ⟨CC, hCC, ?_⟩
  intro p R hR hcurv
  let := hX.separable
  let μ := hausdorff n X
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hQ := hX.quadratic
  obtain ⟨u, d, v, hud, hd, hv, hu, huM, happrox⟩ := hresolvent p R hR hcurv
  let DD : ℝ≥0 := ⟨(2048*D)/R^2, by positivity⟩
  have hd' : ∀ᵐ x ∂μ, |d x| ≤ DD := hd
  let a := SobolevSpace.comp μ hQ hφ hφ0 u
  have ha : SobolevSpace.toLp μ hQ a =ᵐ[μ] fun x => φ (v x) := by
    filter_upwards [SobolevSpace.comp_coe μ hQ hφ hφ0 u, hu] with x hx he
    exact hx.trans (congrArg φ he)
  have haB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ a x| ≤ (1:ℝ≥0) := by
    filter_upwards [ha] with x hx
    rw [hx, abs_of_nonneg (hφbounds _).1]
    exact (hφbounds _).2
  obtain ⟨q, hq, hqB, hqformula⟩ := boundedLaplacian_comp_C2_formula μ hQ u d hud hv hu hd'
    hφ hφ0 hψ hψ0 hχ hdφ hdψ B E hB hE
  have hR2 : 0 < 2*R := by positivity
  let b := radialSobolevCutoff μ hQ p hR2
  let η := radialCutoff p (2*R)
  have hb : SobolevSpace.toLp μ hQ b =ᵐ[μ] η := radialSobolevCutoff_coe μ hQ p hR2
  have hη (x : X) : 0 ≤ η x ∧ η x ≤ 1 := radialCutoff_bounds p (2*R) x
  have hηabs (x : X) : |η x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (hη x).1]; exact (hη x).2
  have hbB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ (1:ℝ≥0) :=
    hb.mono fun x hx => hx ▸ hηabs x
  have hplateau : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ a x=0 ∨
      SobolevSpace.toLp μ hQ b x=0 ∨ SobolevSpace.toLp μ hQ b x=1 := by
    filter_upwards [ha,hb] with x hx hy
    rw [hx,hy]
    by_cases hi : dist p x ≤ 2*R
    · exact Or.inr (Or.inr (radialCutoff_eq_one p hR2 hi))
    by_cases ho : 4*R ≤ dist p x
    · exact Or.inr (Or.inl (radialCutoff_eq_zero p hR2 (by linarith)))
    left
    have hc := happrox x (by linarith)
    rw [radialCutoff_eq_zero p hR (by linarith), sub_zero] at hc
    exact hφzero _ (by linarith [le_abs_self (v x)])
  let mult := boundedMultiplier μ η (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs
  let dq := lpMultiplier μ mult q
  have hdq : ⇑dq =ᵐ[μ] fun x => η x*q x := by
    filter_upwards [lpMultiplier_coe μ mult q, boundedMultiplier_coe μ η
      (radialCutoff_lipschitz p hR2).continuous.measurable 1 hηabs] with x hx hy
    exact hx.trans (by rw [hy])
  let w := SobolevSpace.product μ hQ a b 1 1
  have hwd : IsWeakLaplacian μ hQ w dq := by
    apply weakLaplacian_product_plateau μ hQ a b q dq 1 1 haB hbB hq hplateau
    filter_upwards [hdq,hb] with x hx hy
    rw [hx,hy]
  let F (x : X) := η x*φ (v x)
  have hwe : SobolevSpace.toLp μ hQ w =ᵐ[μ] F := by
    filter_upwards [SobolevSpace.product_coe μ hQ a b 1 1 haB hbB, ha, hb] with x hx hax hbx
    rw [hx,hax,hbx]
    exact mul_comm _ _
  let rL : ℝ≥0 := ⟨R⁻¹, inv_nonneg.mpr hR.le⟩
  let r2L : ℝ≥0 := ⟨(2*R)⁻¹, inv_nonneg.mpr hR2.le⟩
  have hv' : LipschitzWith (2*rL) v := hv
  have hLL : LipschitzWith (1*(C*(2*rL))+1*r2L) F :=
    lipschitzWith_mul_of_support_bound (radialCutoff_lipschitz p hR2) (hφ.comp hv')
      hηabs (fun x _ => by
        rw [abs_of_nonneg (hφbounds _).1]
        exact (hφbounds _).2)
  have hLbound : ((1*(C*(2*rL))+1*r2L : ℝ≥0) : ℝ) ≤ CC/R := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, one_mul]
    change (C:ℝ)*(2*R⁻¹)+(2*R)⁻¹ ≤ CC/R
    have hi : (2*R)⁻¹ ≤ R⁻¹ := inv_anti₀ hR (by linarith)
    have hc : (2*C+1:ℝ) ≤ CC := by
      dsimp only [CC]
      exact le_add_of_nonneg_right (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) B.coe_nonneg) (zero_le_one.trans hD))
        (mul_nonneg (by norm_num) E.coe_nonneg))
    calc
      _ ≤ C*(2*R⁻¹)+R⁻¹ := by linarith only [hi]
      _ = (2*C+1)*R⁻¹ := by ring
      _ ≤ CC*R⁻¹ := mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hR.le)
      _ = _ := div_eq_mul_inv _ _ |>.symm
  have hFbounds (x : X) : 0 ≤ F x ∧ F x ≤ 1 :=
    ⟨mul_nonneg (hη x).1 (hφbounds _).1,
      (mul_le_mul (hη x).2 (hφbounds _).2 (hφbounds _).1 zero_le_one).trans_eq (one_mul _)⟩
  have hFone (x : X) (hx : dist p x ≤ R) : F x=1 := by
    have hi : η x=1 := radialCutoff_eq_one p hR2 (by linarith)
    have hc := happrox x (by linarith)
    rw [radialCutoff_eq_one p hR hx] at hc
    exact show η x*φ (v x)=1 from by rw [hi,hφone _ (by linarith),one_mul]
  have hFzero (x : X) (hx : 2*R < dist p x) : F x=0 := by
    by_cases ho : 4*R ≤ dist p x
    · have hi : η x=0 := radialCutoff_eq_zero p hR2 (by linarith)
      exact show η x*φ (v x)=0 from by rw [hi,zero_mul]
    have hc := happrox x (le_of_not_ge ho)
    rw [radialCutoff_eq_zero p hR hx.le, sub_zero] at hc
    exact show η x*φ (v x)=0 from by rw [hφzero _ (by linarith [le_abs_self (v x)]),mul_zero]
  have hlocal : ∀ᵐ x ∂μ, (dist p x < R ∨ 2*R < dist p x) → dq x=0 := by
    filter_upwards [hdq, hqformula] with x hx hqx hdist
    rw [hx]
    rcases hdist with hin | hout
    · have hc := happrox x (by linarith)
      rw [radialCutoff_eq_one p hR hin.le] at hc
      have hs : φ =ᶠ[𝓝 (v x)] fun _ => 1 := by
        have hab : |v x-1| < 1/4 := by linarith
        filter_upwards [((continuous_id.sub continuous_const).abs.tendsto (v x)).eventually
          (gt_mem_nhds hab)] with z hz
        exact hφone z hz.le
      obtain ⟨hψx,hχx⟩ := plateau_derivatives_zero hdφ hdψ hs
      rw [hqx,hψx,hχx]; ring
    · by_cases ho : 4*R ≤ dist p x
      · have hi : η x=0 := radialCutoff_eq_zero p hR2 (by linarith)
        rw [hi,zero_mul]
      have hc := happrox x (le_of_not_ge ho)
      rw [radialCutoff_eq_zero p hR hout.le, sub_zero] at hc
      have hs : φ =ᶠ[𝓝 (v x)] fun _ => 0 := by
        have hvx : v x < 1/4 := by linarith [le_abs_self (v x)]
        filter_upwards [gt_mem_nhds hvx] with z hz
        exact hφzero z hz.le
      obtain ⟨hψx,hχx⟩ := plateau_derivatives_zero hdφ hdψ hs
      rw [hqx,hψx,hχx]; ring
  have hqbound : ∀ᵐ x ∂μ, |dq x| ≤ CC/R^2 := by
    filter_upwards [hdq,hqB] with x hx hqb
    rw [hx,abs_mul]
    have hh := (mul_le_mul (hηabs x) hqb (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq
      (one_mul _)
    apply hh.trans
    change (B:ℝ)*((2048*D)/R^2)+(E:ℝ)*(2*R⁻¹)^2 ≤ CC/R^2
    have hEq : (B:ℝ)*((2048*D)/R^2)+(E:ℝ)*(2*R⁻¹)^2 =
        (2048*B*D+4*E)/R^2 := by field_simp; ring
    rw [hEq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg R)
    dsimp only [CC]
    exact le_add_of_nonneg_left (by positivity)
  let weight : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hLL.continuous
    1 (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hFbounds x).1]; exact (hFbounds x).2)
  refine ⟨{
    weight := weight
    sobolev := w
    laplacian := dq
    bounds := hFbounds
    one := ?_
    zero := hFzero
    lipschitz := hLL.weaken ?_
    representative := hwe
    weak_laplacian := hwd
    laplacian_bound := hqbound
    laplacian_locality := hlocal }⟩
  · intro x hx
    apply hFone
    rw [dist_comm]
    exact le_of_lt hx
  · apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg (zero_le_one.trans hCC) hR.le)]
    exact hLbound

/-- The dimensional cutoff bound at unit rescaled curvature. -/
theorem NoncollapsedRCD.goodCutoffInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : LocalGoodCutoffInput hX := by
  exact hX.goodCutoffInput_bounded 1 (by norm_num)

/-- At any fixed radius the actual RCD resolvent supplies a good cutoff.
The constant may depend on the rescaled lower curvature. -/
theorem NoncollapsedRCD.goodCutoff_exists {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 1 ≤ C ∧ Nonempty (GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C) := by
  obtain ⟨C, hC, hcutoff⟩ := hX.goodCutoffInput_bounded (|K| * r ^ 2) (by positivity) hn
  refine ⟨C, hC, hcutoff p r hr ?_⟩
  simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)

end RegularPointCoordinates

end

end OAI
