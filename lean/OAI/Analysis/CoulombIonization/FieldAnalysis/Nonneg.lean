import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.SommerfeldCoefficient

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem SingularProfile.nonneg {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) : 0 ≤ F x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => -F y - δ
  have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
    (h.regular y hy).neg.sub contDiffAt_const
  have hsub (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hf : F y ≤ 1 := by dsimp [u] at hp; linarith
    have he : reaction d (F y) = 0 := by
      simp [reaction, max_eq_right (sub_nonpos.mpr hf)]
    change 0 ≤ Δ ((-F) - (fun _ : Space => δ)) y
    have hneg : ContDiffAt ℝ 2 (-F) y := (h.regular y hy).neg
    have hconst : ContDiffAt ℝ 2 (fun _ : Space => δ) y := contDiffAt_const
    rw [hneg.laplacian_sub hconst,
      laplacian_neg, Pi.neg_apply, laplacian_const, Pi.zero_apply, h.equation y hy, he]
    norm_num
  obtain ⟨c, hc, C, _hC, R, hR, hl, _hu⟩ := h.bounds
  have hnear : ∃ r > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ r → u y ≤ 0 := by
    refine ⟨R, hR, ?_⟩
    intro y hy hr
    have hF : 0 ≤ F y := (mul_nonneg hc.le (radialPower_nonneg _ _)).trans (hl y hy hr)
    dsimp [u]
    linarith
  have hfar : ∃ r > 0, ∀ y, r ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨r, hr, hb⟩ := h.decay δ hδ
    refine ⟨r, hr, ?_⟩
    intro y hy
    have hf := (abs_lt.mp (hb y hy)).1
    dsimp [u]
    linarith
  have hm := global_punctured_maximum_principle hreg hsub hnear hfar x hx
  dsimp [u] at hm
  linarith

theorem SingularProfile.reaction_vanishes_at_infinity {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) : ∃ R > 0, ∀ x, R ≤ ‖x‖ → reaction d (F x) = 0 := by
  obtain ⟨R, hR, hb⟩ := h.decay 1 zero_lt_one
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hf : F x ≤ 1 := (abs_lt.mp (hb x hx)).2.le
  simp [reaction, max_eq_right (sub_nonpos.mpr hf)]

theorem SingularProfile.homogeneous_lower_bound {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) :
    sommerfeldCoefficient d * radialPower (-2) x ≤ F x := by
  have hA := sommerfeldCoefficient_pos hd
  have hBbound (B : ℝ) (hB : 0 < B) (hBA : B < sommerfeldCoefficient d) :
      B * radialPower (-2) x ≤ F x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let V : Space → ℝ := B • radialPower (-2)
    let u : Space → ℝ := V - F - fun _ => δ
    have hV (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 V y :=
      contDiffAt_const.smul (radialPower_contDiffAt _ hy)
    have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
      ((hV y hy).sub (h.regular y hy)).sub contDiffAt_const
    have hq : d * B ^ (1 / 2 : ℝ) ≤ 12 := by
      rw [← sommerfeldCoefficient_half hd]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hB.le hBA.le (by norm_num)) hd.le
    have hsub (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
      have hp' : F y < radialPower (-2) y * B := by
        change 0 < B * radialPower (-2) y - F y - δ at hp
        nlinarith
      have ht : max (F y - 1) 0 ≤ radialPower (-2) y * B := by
        apply max_le
        · linarith
        · exact mul_nonneg (radialPower_nonneg _ _) hB.le
      have hr : reaction d (F y) ≤ 12 * B * radialPower (-3) y := by
        calc
          reaction d (F y) ≤ d * (radialPower (-2) y * B) ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_max_right _ _) ht (by norm_num)) hd.le
          _ = d * (radialPower (-3) y * (B * B ^ (1 / 2 : ℝ))) := by
            rw [radial_scaled_reaction hB.le, rpow_three_halves B hB.le]
          _ ≤ 12 * B * radialPower (-3) y := by
            nlinarith [mul_nonneg (mul_nonneg hB.le (radialPower_nonneg (-3) y))
              (sub_nonneg.mpr hq)]
      have hVF : ContDiffAt ℝ 2 (V - F) y := (hV y hy).sub (h.regular y hy)
      have hc : ContDiffAt ℝ 2 (fun _ : Space => δ) y := contDiffAt_const
      change 0 ≤ (Δ ((V - F) - fun _ : Space => δ) : Space → ℝ) y
      rw [hVF.laplacian_sub hc, (hV y hy).laplacian_sub (h.regular y hy),
        laplacian_const, Pi.zero_apply, sub_zero, h.equation y hy]
      change 0 ≤ (Δ (B • radialPower (-2)) : Space → ℝ) y - reaction d (F y)
      rw [laplacian_smul B (radialPower_contDiffAt _ hy), radial_laplacian_three _ hy]
      norm_num only [smul_eq_mul] at *
      nlinarith
    have hnear : ∀ᶠ y in 𝓝[≠] (0 : Space), u y ≤ 0 := by
      filter_upwards [(h.asymptotic hd).eventually (eventually_gt_nhds hBA),
        self_mem_nhdsWithin] with y hy hy0
      have hn : 0 < ‖y‖ ^ 4 := pow_pos (norm_pos_iff.mpr hy0) _
      have hlow : B * radialPower (-2) y ≤ F y := by
        apply (mul_le_mul_iff_right₀ hn).mp
        have he := norm_four_mul_radialPower hy0
        nlinarith
      change B * radialPower (-2) y - F y - δ ≤ 0
      linarith
    have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
      refine ⟨max 1 (B / δ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
      intro y hy
      have hn : 1 ≤ ‖y‖ := (le_max_left _ _).trans hy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hn)
      have h4 : B / δ ≤ ‖y‖ ^ 4 :=
        ((le_max_right _ _).trans hy).trans (le_self_pow₀ hn (by norm_num))
      have hB4 : B ≤ ‖y‖ ^ 4 * δ := (div_le_iff₀ hδ).mp h4
      have hv : B * radialPower (-2) y ≤ δ := by
        have ht := mul_le_mul_of_nonneg_right hB4 (radialPower_nonneg (-2) y)
        have he := norm_four_mul_radialPower hy0
        nlinarith
      have hnonneg := h.nonneg y hy0
      change B * radialPower (-2) y - F y - δ ≤ 0
      linarith
    have hm := global_punctured_maximum_principle hreg hsub
      (deleted_eventually_to_small_ball hnear) hfar x hx
    change B * radialPower (-2) x - F x - δ ≤ 0 at hm
    linarith
  have ht : Tendsto (fun B : ℝ => B * radialPower (-2) x)
      (𝓝[<] (sommerfeldCoefficient d))
      (𝓝 (sommerfeldCoefficient d * radialPower (-2) x)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
  apply le_of_tendsto_of_tendsto ht tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ B in 𝓝[<] (sommerfeldCoefficient d), 0 < B from
      (eventually_gt_nhds hA).filter_mono nhdsWithin_le_nhds)] with B hBA hB
  exact hBbound B hB hBA

theorem SingularProfile.pos {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) (x : Space) (hx : x ≠ 0) : 0 < F x :=
  (mul_pos (sommerfeldCoefficient_pos hd) (radialPower_pos _ hx)).trans_le
    (h.homogeneous_lower_bound hd x hx)

theorem annular_maximum_principle_on [Nontrivial E] {a R : ℝ}
    {u : E → ℝ} (hd : ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set E := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = Metric.closedBall (0 : E) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hb' (x : E) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! hh
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 hh.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 hh.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha', hr'⟩)
    exact fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hm := compact_maximum_principle hk
    (fun x hx => (hd x hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => hd x (interior_subset hx).1 (interior_subset hx).2)
    (fun x hx hp => hl x (interior_subset hx).1 (interior_subset hx).2 hp) hb'
  exact fun x hx hr => hm x ⟨hx, hr⟩

theorem exterior_maximum_principle [Nontrivial E] {a : ℝ} {u : E → ℝ}
    (hd : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, a ≤ ‖x‖ → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a → u x ≤ 0)
    (hf : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → u x ≤ ε) :
    ∀ x, a ≤ ‖x‖ → u x ≤ 0 := by
  intro x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R, hR⟩ := hf ε hε
  let S := max R ‖x‖
  have hv (y : E) (hy : a ≤ ‖y‖) : ContDiffAt ℝ 2 (fun z => u z - ε) y :=
    (hd y hy).sub contDiffAt_const
  have hl' (y : E) (hy : a ≤ ‖y‖) (_hyS : ‖y‖ ≤ S) (hp : 0 < u y - ε) :
      0 ≤ Δ (fun z => u z - ε) y := by
    have he := (hd y hy).laplacian_sub (show ContDiffAt ℝ 2 (fun _ : E => ε) y from contDiffAt_const)
    simp only [laplacian_const, Pi.zero_apply, sub_zero] at he
    change 0 ≤ (Δ (u - fun _ => ε) : E → ℝ) y
    rw [he]
    exact hl y hy (by linarith)
  have hm := annular_maximum_principle_on (a := a) (R := S)
    (fun y hy _ => hv y hy) hl' (fun y hy => ?_) x hx (le_max_right _ _)
  · simpa using (sub_nonpos.mp hm)
  · rcases hy with hy | hy
    · have hh := hb y hy
      linarith
    · have hh := hR y ((le_max_left R ‖x‖).trans hy.ge)
      linarith

lemma radialPower_half_inv (x : Space) : radialPower (-(1 / 2)) x = ‖x‖⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_norm]

theorem exterior_harmonic_unique {a : ℝ} {F G : Space → ℝ}
    (hF : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 F x)
    (hG : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 G x)
    (hΔ : ∀ x, a ≤ ‖x‖ → Δ F x = Δ G x)
    (hb : ∀ x, ‖x‖ = a → F x = G x)
    (hf : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → |F x - G x| ≤ ε) :
    ∀ x, a ≤ ‖x‖ → F x = G x := by
  have hle {U V : Space → ℝ}
      (hU : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 U x)
      (hV : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 V x)
      (he : ∀ x, a ≤ ‖x‖ → Δ U x = Δ V x)
      (hbu : ∀ x, ‖x‖ = a → U x = V x)
      (hf' : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → U x - V x ≤ ε) :
      ∀ x, a ≤ ‖x‖ → U x ≤ V x := by
    intro x hx
    apply sub_nonpos.mp
    apply exterior_maximum_principle (fun y hy => (hU y hy).sub (hV y hy))
      (fun y hy _ => ?_) (fun y hy => by simp [hbu y hy]) hf' x hx
    change 0 ≤ (Δ (U - V) : Space → ℝ) y
    rw [(hU y hy).laplacian_sub (hV y hy), he y hy, sub_self]
  intro x hx
  apply le_antisymm
  · exact hle hF hG hΔ hb (fun ε hε => by
      obtain ⟨R, hR⟩ := hf ε hε
      exact ⟨R, fun y hy => (le_abs_self _).trans (hR y hy)⟩) x hx
  · exact hle hG hF (fun y hy => (hΔ y hy).symm) (fun y hy => (hb y hy).symm)
      (fun ε hε => by
        obtain ⟨R, hR⟩ := hf ε hε
        refine ⟨R, fun y hy => ?_⟩
        have hh := (abs_le.mp (hR y hy)).1
        linarith) x hx

theorem SingularProfile.positive_coulomb_tail {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) :
    ∃ q > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → F x = q / ‖x‖ := by
  obtain ⟨R, hR, hr⟩ := h.reaction_vanishes_at_infinity
  let e : Space := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  let y := R • e
  have hy : ‖y‖ = R := by simp [y, norm_smul, he, abs_of_pos hR]
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hy ▸ hR)
  let q := R * F y
  have hq : 0 < q := mul_pos hR (h.pos hd y hy0)
  let G : Space → ℝ := fun x => q * radialPower (-(1 / 2)) x
  have hg (x : Space) : G x = q / ‖x‖ := by
    change q * radialPower (-(1 / 2)) x = _
    rw [radialPower_half_inv, div_eq_mul_inv]
  have hx0 (x : Space) (hx : R ≤ ‖x‖) : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have hreg (x : Space) (hx : R ≤ ‖x‖) : ContDiffAt ℝ 2 G x :=
    contDiffAt_const.mul (radialPower_contDiffAt _ (hx0 x hx))
  have hlap (x : Space) (hx : R ≤ ‖x‖) : Δ G x = 0 := by
    change (Δ (q • (radialPower (-(1 / 2)) : Space → ℝ)) : Space → ℝ) x = 0
    rw [laplacian_smul q (radialPower_contDiffAt _ (hx0 x hx)),
      radial_laplacian_three _ (hx0 x hx)]
    norm_num
  refine ⟨q, hq, R, hR, ?_⟩
  have hEq := exterior_harmonic_unique (a := R)
    (fun x hx => h.regular x (hx0 x hx)) hreg (fun x hx => ?_)
    (fun x hx => ?_) (fun ε hε => ?_)
  · intro x hx
    exact (hEq x hx).trans (hg x)
  · rw [hlap x hx, h.equation x (hx0 x hx), hr x hx]
  · rw [hg, h.radial hd (hx.trans hy.symm)]
    dsimp [q]
    rw [hx, mul_div_cancel_left₀ _ hR.ne']
  · obtain ⟨S, hS, hdec⟩ := h.decay (ε / 2) (by positivity)
    refine ⟨max S (2 * q / ε), ?_⟩
    intro x hx
    have hxS : S ≤ ‖x‖ := (le_max_left _ _).trans hx
    have hxn : 0 < ‖x‖ := hS.trans_le hxS
    have hsmall : q / ‖x‖ ≤ ε / 2 := by
      have hh := (div_le_iff₀ hε).mp ((le_max_right S (2 * q / ε)).trans hx)
      apply (div_le_iff₀ hxn).mpr
      linarith
    have hab : |G x| ≤ ε / 2 := by
      rw [hg, abs_of_nonneg (div_nonneg hq.le hxn.le)]
      exact hsmall
    exact (abs_sub _ _).trans (by linarith [(hdec x hxS).le])

end CoulombPDE

open MeasureTheory Filter
open scoped Topology

end

end OAI
