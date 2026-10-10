import Mathlib
import OAI.Analysis.CoulombRadii.Variational.WeakLaplacian

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def scaledProfile (F : Position → ℝ) (x : Position) : ℝ := (‖x‖^2)^2*F x

theorem continuousOn_scaledProfile {F : Position → ℝ} (hF : ContinuousOn F punctured) :
    ContinuousOn (scaledProfile F) punctured :=
  ((continuous_norm.pow 2).pow 2).continuousOn.mul hF

theorem scaled_reaction {F : Position → ℝ} {x : Position} (hF : 0 ≤ F x) (c : ℝ) :
    (‖x‖^2)^3*(c*F x^(3/2 : ℝ)) = c*(scaledProfile F x)^(3/2 : ℝ) := by
  have hp : ((‖x‖^2)^2)^(3/2 : ℝ) = (‖x‖^2)^3 := by
    rw [← Real.rpow_natCast (‖x‖^2) 2, ← Real.rpow_mul (sq_nonneg ‖x‖)]
    norm_num
  rw [scaledProfile, Real.mul_rpow (sq_nonneg _) hF, hp]
  ring

theorem penalized_max_reaction_bound {F : Position → ℝ} {c δ : ℝ} {x : Position}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hδ : 0 < δ) (hx : x ≠ 0)
    (hm : ∀ y ≠ 0, scaledProfile F y-δ*radialPenalty y ≤ scaledProfile F x-δ*radialPenalty x) :
    c*(scaledProfile F x)^(3/2 : ℝ) ≤ 12*scaledProfile F x+18*(δ*radialPenalty x) := by
  let a := scaledProfile F x-δ*radialPenalty x
  have hbar (y : Position) (hy : y ≠ 0) : F y ≤ radialBarrier a δ y := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)))).mp
    change scaledProfile F y ≤ (‖y‖^2)^2*radialBarrier a δ y
    rw [radialBarrier_scaled hy]
    have hh := hm y hy
    dsimp [a, radialPenalty] at *
    linarith
  have he : F x = radialBarrier a δ x := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))
    change scaledProfile F x = (‖x‖^2)^2*radialBarrier a δ x
    rw [radialBarrier_scaled hx]
    simp [a, radialPenalty]
  have hlmax : IsLocalMax (fun y => F y-radialBarrier a δ y) x := by
    filter_upwards [isOpen_punctured.mem_nhds hx] with y hy
    rw [he, sub_self]
    exact sub_nonpos.mpr (hbar y hy)
  have hq : ContinuousOn (fun y => c*F y^(3/2 : ℝ)) punctured :=
    continuousOn_const.mul (hF.rpow_const (fun _ _ => Or.inr (by norm_num)))
  have h := weakLaplacian_le_at_local_max isOpen_punctured hx hF hq
    (contDiffOn_radialBarrier a δ 2) hw hlmax
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (sq_nonneg ‖x‖) 3)
  rw [scaled_reaction (hpos x hx), laplacian_radialBarrier_scaled hx] at hmul
  have hδq : 0 ≤ δ*(‖x‖^2) := mul_nonneg hδ.le (sq_nonneg ‖x‖)
  dsimp [a, radialPenalty] at *
  nlinarith

theorem penalized_min_reaction_bound {F : Position → ℝ} {c δ : ℝ} {x : Position}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hδ : 0 < δ) (hx : x ≠ 0)
    (hm : ∀ y ≠ 0, scaledProfile F x+δ*radialPenalty x ≤ scaledProfile F y+δ*radialPenalty y) :
    12*scaledProfile F x-18*(δ*radialPenalty x) ≤ c*(scaledProfile F x)^(3/2 : ℝ) := by
  let a := scaledProfile F x+δ*radialPenalty x
  have hbar (y : Position) (hy : y ≠ 0) : radialBarrier a (-δ) y ≤ F y := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)))).mp
    change (‖y‖^2)^2*radialBarrier a (-δ) y ≤ scaledProfile F y
    rw [radialBarrier_scaled hy]
    have hh := hm y hy
    dsimp [a, radialPenalty] at *
    linarith
  have he : F x = radialBarrier a (-δ) x := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))
    change scaledProfile F x = (‖x‖^2)^2*radialBarrier a (-δ) x
    rw [radialBarrier_scaled hx]
    simp [a, radialPenalty]
  have hlmin : IsLocalMin (fun y => F y-radialBarrier a (-δ) y) x := by
    filter_upwards [isOpen_punctured.mem_nhds hx] with y hy
    rw [he, sub_self]
    exact sub_nonneg.mpr (hbar y hy)
  have hq : ContinuousOn (fun y => c*F y^(3/2 : ℝ)) punctured :=
    continuousOn_const.mul (hF.rpow_const (fun _ _ => Or.inr (by norm_num)))
  have h := weakLaplacian_ge_at_local_min isOpen_punctured hx hF hq
    (contDiffOn_radialBarrier a (-δ) 2) hw hlmin
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (sq_nonneg ‖x‖) 3)
  rw [scaled_reaction (hpos x hx), laplacian_radialBarrier_scaled hx] at hmul
  have hδq : 0 ≤ δ*(‖x‖^2) := mul_nonneg hδ.le (sq_nonneg ‖x‖)
  dsimp [a, radialPenalty] at *
  nlinarith

theorem exists_approximate_penalized_max {V : Position → ℝ} {b ε : ℝ}
    (hV : ContinuousOn V punctured) (hb : ∀ x ≠ 0, V x ≤ b)
    (hnear : ∀ e > 0, ∃ x ≠ 0, b-e < V x) (hε : 0 < ε) :
    ∃ δ > 0, ∃ x ≠ 0,
      (∀ y ≠ 0, V y-δ*radialPenalty y ≤ V x-δ*radialPenalty x) ∧
      b-ε < V x ∧ δ*radialPenalty x < ε := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := hnear (ε/2) (by positivity)
  let δ := (ε/2)/radialPenalty x₀
  have hδ : 0 < δ := div_pos (by positivity) (radialPenalty_pos hx₀)
  have hδ₀ : δ*radialPenalty x₀ = ε/2 := div_mul_cancel₀ _ (radialPenalty_pos hx₀).ne'
  obtain ⟨x, hx, hxm⟩ := exists_penalized_max hV hb hδ hx₀
  have hh := hxm x₀ hx₀
  rw [hδ₀] at hh
  have hM : b-ε < V x-δ*radialPenalty x := by linarith
  refine ⟨δ, hδ, x, hx, hxm, ?_, ?_⟩
  · have hp := mul_pos hδ (radialPenalty_pos hx)
    linarith
  · linarith [hb x hx]

theorem exists_approximate_penalized_min {V : Position → ℝ} {b ε : ℝ}
    (hV : ContinuousOn V punctured) (hb : ∀ x ≠ 0, b ≤ V x)
    (hnear : ∀ e > 0, ∃ x ≠ 0, V x < b+e) (hε : 0 < ε) :
    ∃ δ > 0, ∃ x ≠ 0,
      (∀ y ≠ 0, V x+δ*radialPenalty x ≤ V y+δ*radialPenalty y) ∧
      V x < b+ε ∧ δ*radialPenalty x < ε := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := hnear (ε/2) (by positivity)
  let δ := (ε/2)/radialPenalty x₀
  have hδ : 0 < δ := div_pos (by positivity) (radialPenalty_pos hx₀)
  have hδ₀ : δ*radialPenalty x₀ = ε/2 := div_mul_cancel₀ _ (radialPenalty_pos hx₀).ne'
  obtain ⟨x, hx, hxm⟩ := exists_penalized_min hV hb hδ hx₀
  have hh := hxm x₀ hx₀
  rw [hδ₀] at hh
  have hM : V x+δ*radialPenalty x < b+ε := by linarith
  refine ⟨δ, hδ, x, hx, hxm, ?_, ?_⟩
  · have hp := mul_pos hδ (radialPenalty_pos hx)
    linarith
  · linarith [hb x hx]

theorem reaction_le_at_supremum {F : Position → ℝ} {c b : ℝ}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hb : ∀ x ≠ 0, scaledProfile F x ≤ b)
    (hnear : ∀ e > 0, ∃ x ≠ 0, b-e < scaledProfile F x) :
    c*b^(3/2 : ℝ) ≤ 12*b := by
  have happ (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, b-ε < t ∧ t ≤ b ∧ c*t^(3/2 : ℝ) ≤ 12*t+18*ε := by
    obtain ⟨δ, hδ, x, hx, hxm, hxb, hδx⟩ :=
      exists_approximate_penalized_max (continuousOn_scaledProfile hF) hb hnear hε
    refine ⟨scaledProfile F x, hxb, hb x hx, ?_⟩
    linarith [penalized_max_reaction_bound hF hpos hw hδ hx hxm]
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose t htl htu htr using fun n => happ (e n) (by dsimp [e]; positivity)
  have ht : Tendsto t atTop (𝓝 b) :=
    (show Tendsto (fun n => b-e n) atTop (𝓝 b) by simpa using tendsto_const_nhds.sub he).squeeze
      tendsto_const_nhds (fun n => (htl n).le) htu
  have hr : Tendsto (fun n => c*(t n)^(3/2 : ℝ)) atTop (𝓝 (c*b^(3/2 : ℝ))) :=
    tendsto_const_nhds.mul (ht.rpow_const (Or.inr (by norm_num)))
  have hs : Tendsto (fun n => 12*t n+18*e n) atTop (𝓝 (12*b)) := by
    simpa using (tendsto_const_nhds.mul ht).add (tendsto_const_nhds.mul he)
  exact le_of_tendsto_of_tendsto' hr hs htr

theorem reaction_ge_at_infimum {F : Position → ℝ} {c b : ℝ}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hb : ∀ x ≠ 0, b ≤ scaledProfile F x)
    (hnear : ∀ e > 0, ∃ x ≠ 0, scaledProfile F x < b+e) :
    12*b ≤ c*b^(3/2 : ℝ) := by
  have happ (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, b ≤ t ∧ t < b+ε ∧ 12*t-18*ε ≤ c*t^(3/2 : ℝ) := by
    obtain ⟨δ, hδ, x, hx, hxm, hxb, hδx⟩ :=
      exists_approximate_penalized_min (continuousOn_scaledProfile hF) hb hnear hε
    refine ⟨scaledProfile F x, hb x hx, hxb, ?_⟩
    linarith [penalized_min_reaction_bound hF hpos hw hδ hx hxm]
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose t htl htu htr using fun n => happ (e n) (by dsimp [e]; positivity)
  have ht : Tendsto t atTop (𝓝 b) := tendsto_const_nhds.squeeze
    (show Tendsto (fun n => b+e n) atTop (𝓝 b) by simpa using tendsto_const_nhds.add he)
      htl (fun n => (htu n).le)
  have hr : Tendsto (fun n => c*(t n)^(3/2 : ℝ)) atTop (𝓝 (c*b^(3/2 : ℝ))) :=
    tendsto_const_nhds.mul (ht.rpow_const (Or.inr (by norm_num)))
  have hs : Tendsto (fun n => 12*t n-18*e n) atTop (𝓝 (12*b)) := by
    simpa using (tendsto_const_nhds.mul ht).sub (tendsto_const_nhds.mul he)
  exact le_of_tendsto_of_tendsto' hs hr htr

theorem scalar_upper_contact {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (h : c*b^(3/2 : ℝ) ≤ 12*b) : b ≤ (12/c)^2 := by
  have hr : b^(3/2 : ℝ) = b*Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hb.le (by norm_num : (1:ℝ)+1/2 ≠ 0)]
    norm_num
  rw [hr] at h
  have hs : c*Real.sqrt b ≤ 12 := by nlinarith
  have hs' : Real.sqrt b ≤ 12/c := (le_div_iff₀ hc).mpr (by nlinarith)
  nlinarith [sq_nonneg (12/c-Real.sqrt b), Real.sq_sqrt hb.le, Real.sqrt_nonneg b]

theorem scalar_lower_contact {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (h : 12*b ≤ c*b^(3/2 : ℝ)) : (12/c)^2 ≤ b := by
  have hr : b^(3/2 : ℝ) = b*Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hb.le (by norm_num : (1:ℝ)+1/2 ≠ 0)]
    norm_num
  rw [hr] at h
  have hs : 12 ≤ c*Real.sqrt b := by nlinarith
  have hs' : 12/c ≤ Real.sqrt b := (div_le_iff₀ hc).mpr (by nlinarith)
  have hp : 0 < 12/c := by positivity
  nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b]

theorem weak_sommerfeld_rigidity {F : Position → ℝ} {c B C : ℝ}
    (hc : 0 < c) (hB : 0 < B)
    (hF : ContinuousOn F punctured)
    (hw : HasWeakLaplacian F punctured (fun x => c*F x^(3/2 : ℝ)))
    (hbounds : ∀ x ≠ 0, B ≤ scaledProfile F x ∧ scaledProfile F x ≤ C) :
    ∀ x ≠ 0, F x = (12/c)^2*radialPower (-2) x := by
  let S : Set ℝ := scaledProfile F '' punctured
  have hx₀ : axis 0 ≠ 0 := by
    intro h
    have h' := congrArg (fun x : Position => x 0) h
    norm_num [axis] at h'
  have hS : S.Nonempty := ⟨scaledProfile F (axis 0), ⟨axis 0, hx₀, rfl⟩⟩
  have hSu : BddAbove S := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).2⟩
  have hSl : BddBelow S := ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).1⟩
  have hmax (x : Position) (hx : x ≠ 0) : scaledProfile F x ≤ sSup S :=
    le_csSup hSu ⟨x, hx, rfl⟩
  have hmin (x : Position) (hx : x ≠ 0) : sInf S ≤ scaledProfile F x :=
    csInf_le hSl ⟨x, hx, rfl⟩
  have hpos (x : Position) (hx : x ≠ 0) : 0 ≤ F x := by
    have hp : 0 ≤ scaledProfile F x := le_trans hB.le (hbounds x hx).1
    exact nonneg_of_mul_nonneg_right hp (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)))
  have hnearU (e : ℝ) (he : 0 < e) : ∃ x ≠ 0, sSup S-e < scaledProfile F x := by
    obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hS (sub_lt_self _ he)
    exact ⟨x, hx, hv⟩
  have hnearL (e : ℝ) (he : 0 < e) : ∃ x ≠ 0, scaledProfile F x < sInf S+e := by
    obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hS (lt_add_of_pos_right _ he)
    exact ⟨x, hx, hv⟩
  have hBp : 0 < sInf S := lt_of_lt_of_le hB (le_csInf hS (by
    rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).1))
  have hCp : 0 < sSup S := lt_of_lt_of_le
    (lt_of_lt_of_le hB (hbounds (axis 0) hx₀).1) (hmax (axis 0) hx₀)
  have hupper := scalar_upper_contact hc hCp (reaction_le_at_supremum hF hpos hw hmax hnearU)
  have hlower := scalar_lower_contact hc hBp (reaction_ge_at_infimum hF hpos hw hmin hnearL)
  intro x hx
  have he : scaledProfile F x = (12/c)^2 := le_antisymm
    (le_trans (hmax x hx) hupper) (le_trans hlower (hmin x hx))
  have hq : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  unfold scaledProfile at he
  have he' : F x = (12/c)^2 / (‖x‖^2)^2 :=
    (eq_div_iff (pow_ne_zero 2 hq)).mpr (by nlinarith [he])
  rw [he']
  norm_num [radialPower, Real.rpow_neg_natCast, div_eq_mul_inv]

theorem WeakLaplacianLower.add_smooth {f b : Position → ℝ}
    {U : Set Position} {c d : ℝ}
    (hf : ∀ x ∈ U, ContinuousAt f x) (hb : ∀ x ∈ U, ContDiffAt ℝ 2 b x)
    (hw : WeakLaplacianLower f U c)
    (hl : ∀ x ∈ U, d ≤ coordinateLaplacian b x) :
    WeakLaplacianLower (fun x => f x+b x) U (c+d) := by
  intro φ hφ hc ht hp
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hφ2 := hφ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)
  have hφl := continuous_coordinateLaplacian hφ2
  have hφlc := hasCompactSupport_coordinateLaplacian hc
  have hif : Integrable (fun x => f x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => hf x (ht (hts hx))) hφl hφlc
  have hib : Integrable (fun x => b x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hb x (ht (hts hx))).continuousAt) hφl hφlc
  have hib' : Integrable (fun x => coordinateLaplacian b x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hb x (ht hx))) hφ.continuous hc
  have hbd : d*(∫ x, φ x) ≤ ∫ x, coordinateLaplacian b x*φ x := by
    rw [← integral_const_mul]
    apply integral_mono ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul d) hib'
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, le_refl]
  simp_rw [add_mul]
  rw [integral_add hif hib, integral_mul_coordinateLaplacian_eq (fun x hx => hb x (ht hx)) hφ hc]
  linarith [hw φ hφ hc ht hp]

theorem weak_maximum_principle_closedBall {f : Position → ℝ} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (Metric.closedBall 0 R))
    (hbdy : ∀ x : Position, ‖x‖ = R → f x ≤ 0)
    (hw : WeakLaplacianLower f (Metric.ball 0 R ∩ {x | 0 < f x}) 0) :
    ∀ x ∈ Metric.closedBall 0 R, f x ≤ 0 := by
  intro x₀ hx₀
  by_contra hn
  have hp : 0 < f x₀ := lt_of_not_ge hn
  let η := f x₀/(2*R^2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηR : η*R^2 = f x₀/2 := by dsimp [η]; field_simp
  let v : Position → ℝ := fun x => f x+η*‖x‖^2
  have hq : ContDiff ℝ 2 (fun x : Position => η*‖x‖^2) := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hv : ContinuousOn v (Metric.closedBall 0 R) := hf.add hq.continuous.continuousOn
  obtain ⟨x, hx, hxm⟩ := (isCompact_closedBall (0 : Position) R).exists_isMaxOn
    ⟨x₀, hx₀⟩ hv
  have hhigh : η*R^2 < v x := by
    have hh := hxm hx₀
    have hq₀ := mul_nonneg hη.le (sq_nonneg ‖x₀‖)
    dsimp [v] at *
    linarith
  have hxnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxint : x ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_zero_right]
    by_contra hn
    have he : ‖x‖ = R := le_antisymm hxnorm (le_of_not_gt hn)
    have hh := hbdy x he
    dsimp [v] at hhigh
    rw [he] at hhigh
    linarith
  have hfx : 0 < f x := by
    have hqle : η*‖x‖^2 ≤ η*R^2 := mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) hR.le |>.mpr hxnorm) hη.le
    dsimp [v] at hhigh
    linarith
  let U := Metric.ball (0 : Position) R ∩ {x | 0 < f x}
  have hcont : ContinuousAt f x := hf.continuousAt
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hxint) Metric.ball_subset_closedBall)
  have hun : U ∈ 𝓝 x := inter_mem (Metric.isOpen_ball.mem_nhds hxint)
    (hcont.eventually (Ioi_mem_nhds hfx))
  obtain ⟨r, hr, hsub⟩ : ∃ r > 0, Metric.closedBall x r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp hun
  have hlocal : WeakLaplacianLower v (Metric.ball x r) (6*η) := by
    have hadd := hw.add_smooth
      (fun y hy => hf.continuousAt (mem_of_superset
        (Metric.isOpen_ball.mem_nhds hy.1) Metric.ball_subset_closedBall))
      (fun y _ => hq.contDiffAt (x := y))
      (d := 6*η) (fun y _ => by
        simpa using (coordinateLaplacian_quadratic 0 y η).ge)
    have hadd' : WeakLaplacianLower v U (6*η) := by simpa [v] using hadd
    exact hadd'.mono (fun y hy => hsub (Metric.ball_subset_closedBall hy))
  exact no_maximum_of_strict_weakLaplacian_local hr (by positivity : 0 < 6*η)
    (hv.mono (fun y hy => Metric.ball_subset_closedBall (hsub hy).1)) hlocal
    (fun y hy => hxm (Metric.ball_subset_closedBall (hsub (Metric.ball_subset_closedBall hy)).1))

def kTF : ℝ := (2:ℝ)^(3/2 : ℝ)/(3*Real.pi^2)
def aTF : ℝ := (12/(4*Real.pi*kTF))^2

theorem kTF_pos : 0 < kTF := by unfold kTF; positivity

theorem aTF_pos : 0 < aTF := by
  have := kTF_pos
  unfold aTF
  positivity

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x^(3/2 : ℝ) = x*Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx (by norm_num : (1:ℝ)+1/2 ≠ 0)]
  norm_num

theorem aTF_value : aTF = 81*Real.pi^2/8 := by
  have htwo : ((2:ℝ)^(3/2 : ℝ))^2 = 8 := by
    rw [rpow_three_halves (by norm_num : (0:ℝ)≤2), mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hk : kTF^2 = 8/(9*Real.pi^4) := by
    unfold kTF
    rw [div_pow, htwo]
    ring
  unfold aTF
  rw [div_pow, mul_pow, mul_pow, hk]
  field_simp
  ring

theorem profile_coefficient : kTF*aTF^(3/2 : ℝ) = 3*aTF/Real.pi := by
  have hk := kTF_pos
  rw [rpow_three_halves aTF_pos.le]
  have hs : Real.sqrt aTF = 12/(4*Real.pi*kTF) := by
    unfold aTF
    rw [Real.sqrt_sq (by positivity : (0:ℝ)≤12/(4*Real.pi*kTF))]
  rw [hs]
  field_simp [ne_of_gt hk]
  ring

theorem weak_sommerfeld_rigidity_exact {F : Position → ℝ} {B C : ℝ}
    (hB : 0 < B) (hF : ContinuousOn F punctured)
    (hw : HasWeakLaplacian F punctured (fun x => 4*Real.pi*kTF*F x^(3/2 : ℝ)))
    (hbounds : ∀ x ≠ 0, B/‖x‖^4 ≤ F x ∧ F x ≤ C/‖x‖^4) :
    ∀ x ≠ 0, F x = (81*Real.pi^2/8)/‖x‖^4 := by
  have hc : 0 < 4*Real.pi*kTF := by have := kTF_pos; positivity
  have hs : ∀ x ≠ 0, B ≤ scaledProfile F x ∧ scaledProfile F x ≤ C := by
    intro x hx
    have hp : 0 < ‖x‖^4 := pow_pos (norm_pos_iff.mpr hx) _
    have hl := (div_le_iff₀ hp).mp (hbounds x hx).1
    have hu := (le_div_iff₀ hp).mp (hbounds x hx).2
    constructor <;> dsimp [scaledProfile] <;> nlinarith
  intro x hx
  have he := weak_sommerfeld_rigidity hc hB hF hw hs x hx
  change F x = aTF*radialPower (-2) x at he
  rw [aTF_value] at he
  convert he using 1
  norm_num [radialPower, Real.rpow_neg_natCast, div_eq_mul_inv, ← pow_mul]

def WeakLaplacianGE (f : Position → ℝ) (U : Set Position) (q : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ x, 0 ≤ φ x) → (∫ x, q x*φ x) ≤ ∫ x, f x*coordinateLaplacian φ x

theorem WeakLaplacianGE.lower_on {f q : Position → ℝ} {U V : Set Position} {c : ℝ}
    (hw : WeakLaplacianGE f U q) (hV : V ⊆ U) (hq : LocallyIntegrableOn q U)
    (hl : ∀ x ∈ V, c ≤ q x) : WeakLaplacianLower f V c := by
  intro φ hφ hc ht hp
  have hiq : Integrable (fun x => q x*φ x) :=
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right q φ).trans (subset_tsupport φ))).mp
      ((hq.integrableOn_compact_subset (ht.trans hV) hc).mul_continuousOn hφ.continuous.continuousOn hc)
  apply le_trans _ (hw φ hφ hc (ht.trans hV) hp)
  rw [← integral_const_mul]
  apply integral_mono ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul c) hiq
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, le_refl]

theorem weak_comparison_closedBall {u F L q : Position → ℝ} {c R : ℝ}
    (hR : 0 < R) (hc : 0 ≤ c)
    (hcont : ContinuousOn (fun x => u x-F x-L x-c) (Metric.closedBall 0 R))
    (hL : ∀ x ∈ Metric.ball 0 R, 0 ≤ L x)
    (hbdy : ∀ x : Position, ‖x‖ = R → u x-F x-L x-c ≤ 0)
    (hw : WeakLaplacianGE (fun x => u x-F x-L x-c) (Metric.ball 0 R) q)
    (hq : LocallyIntegrableOn q (Metric.ball 0 R))
    (hsign : ∀ x ∈ Metric.ball 0 R, F x < u x → 0 ≤ q x) :
    ∀ x ∈ Metric.closedBall 0 R, u x ≤ F x+L x+c := by
  have hw' : WeakLaplacianLower (fun x => u x-F x-L x-c)
      (Metric.ball 0 R ∩ {x | 0 < u x-F x-L x-c}) 0 :=
    hw.lower_on Set.inter_subset_left hq (fun x hx => hsign x hx.1 (by
      have := hL x hx.1
      have hp : 0 < u x-F x-L x-c := hx.2
      linarith))
  intro x hx
  have hh := weak_maximum_principle_closedBall hR hcont hbdy hw' x hx
  linarith

end NeutralAtom
end
end
end

end OAI
