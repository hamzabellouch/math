import OAI.Analysis.NodalLength.Cutoffs

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

namespace SharpNodal
namespace Profiles
open Carleman

lemma tsupport_subset_compl_of_zero {f : Plane → ℝ} {G : Set Plane}
    (hG : IsOpen G) (hf : ∀ x ∈ G, f x = 0) : tsupport f ⊆ Gᶜ := by
  apply closure_minimal _ hG.isClosed_compl
  intro x hx h
  exact hx (hf x h)

lemma partial_tsupport_outside {f : Plane → ℝ} {x₀ : Plane} {r c : ℝ}
    (hf : ∀ x ∈ Metric.ball x₀ r, f x=c) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ (Metric.ball x₀ r)ᶜ := by
  apply tsupport_subset_compl_of_zero Metric.isOpen_ball
  intro x hx
  have he : f =ᶠ[𝓝 x] (fun _ => c) :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hf y hy
  rw [(partial_eventuallyEq he i).eq_of_nhds, partial_const]

lemma laplacian_const (c : ℝ) (x : Plane) : euclideanLaplacian (fun _ => c) x=0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h : coordPartial (fun _ => c) i=(fun _ => 0) := funext (partial_const c i)
  rw [h, partial_const]

lemma laplacian_tsupport_outside {f : Plane → ℝ} {x₀ : Plane} {r c : ℝ}
    (hf : ∀ x ∈ Metric.ball x₀ r, f x=c) :
    tsupport (euclideanLaplacian f) ⊆ (Metric.ball x₀ r)ᶜ := by
  apply tsupport_subset_compl_of_zero Metric.isOpen_ball
  intro x hx
  have he : f =ᶠ[𝓝 x] (fun _ => c) :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hf y hy
  rw [(laplacian_eventuallyEq he).eq_of_nhds]
  exact laplacian_const _ _

lemma laplacian_tsupport_subset (f : Plane → ℝ) :
    tsupport (euclideanLaplacian f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  rw [(laplacian_eventuallyEq he).eq_of_nhds]
  exact laplacian_const _ _

lemma annular_cutoff_support {x₀ : Plane} (a b : ContDiffBump x₀) :
    tsupport (fun x => a x * (1-b x)) ⊆
      Metric.closedBall x₀ a.rOut ∩ (Metric.ball x₀ b.rIn)ᶜ := by
  apply Set.subset_inter
  · exact tsupport_mul_subset_left.trans (by rw [a.tsupport_eq])
  · apply tsupport_subset_compl_of_zero Metric.isOpen_ball
    intro x hx
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)]
    ring

lemma annular_cutoff_one {x₀ x : Plane} (a b : ContDiffBump x₀)
    (ha : dist x x₀ ≤ a.rIn) (hb : b.rOut ≤ dist x x₀) : a x * (1-b x)=1 := by
  rw [a.one_of_mem_closedBall ha, b.zero_of_le_dist hb]
  norm_num

lemma annular_cutoff_bounds {x₀ : Plane} (a b : ContDiffBump x₀) (x : Plane) :
    0 ≤ a x*(1-b x) ∧ a x*(1-b x) ≤ 1 := by
  constructor
  · exact mul_nonneg a.nonneg (sub_nonneg.mpr b.le_one)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ b.nonneg) a.nonneg).trans (by simpa using a.le_one (x:=x))

theorem exists_profile_cutoffs {x₀ : Plane} {r : ℝ} (hr : 0<r) :
    ∃ (ζ θ φ : Plane → ℝ) (ρ : ℝ), 0<ρ ∧
      Smooth ζ ∧ Smooth θ ∧ Smooth φ ∧
      HasCompactSupport ζ ∧ HasCompactSupport θ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r ∧
      tsupport θ ⊆ Metric.ball x₀ r ∧
      tsupport φ ⊆ Metric.ball x₀ r ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧
      (∀ x, 0≤φ x ∧ φ x≤1) ∧
      (∀ i x, x ∈ tsupport (coordPartial ζ i) → θ x=1) ∧
      (∀ x ∈ tsupport θ, φ x=1) ∧
      (∀ x ∈ tsupport (euclideanLaplacian ζ), φ x=1) := by
  let ζ : ContDiffBump x₀ := ⟨r/4, r/3, by positivity, by linarith⟩
  let θo : ContDiffBump x₀ := ⟨r/2, 2*r/3, by positivity, by linarith⟩
  let θi : ContDiffBump x₀ := ⟨r/8, r/4, by positivity, by linarith⟩
  let φo : ContDiffBump x₀ := ⟨3*r/4, 7*r/8, by positivity, by linarith⟩
  let φi : ContDiffBump x₀ := ⟨r/16, r/8, by positivity, by linarith⟩
  let θ : Plane → ℝ := fun x => θo x*(1-θi x)
  let φ : Plane → ℝ := fun x => φo x*(1-φi x)
  have hζ1 : ∀ x ∈ Metric.ball x₀ (r/4), ζ x=1 :=
    fun _ hx => ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hζsup : tsupport (ζ : Plane → ℝ) ⊆ Metric.closedBall x₀ (r/3) := by
    rw [ζ.tsupport_eq]
  have hθsup := annular_cutoff_support θo θi
  have hφsup := annular_cutoff_support φo φi
  refine ⟨ζ, θ, φ, r/4, by positivity, ζ.contDiff,
    θo.contDiff.mul (contDiff_const.sub θi.contDiff),
    φo.contDiff.mul (contDiff_const.sub φi.contDiff),
    ζ.hasCompactSupport, θo.hasCompactSupport.mul_right, φo.hasCompactSupport.mul_right,
    hζsup.trans (Metric.closedBall_subset_ball (by linarith)), ?_, ?_, hζ1, ?_,
    annular_cutoff_bounds φo φi, ?_, ?_, ?_⟩
  · exact (hθsup.trans Set.inter_subset_left).trans (Metric.closedBall_subset_ball (by dsimp [θo]; linarith))
  · exact (hφsup.trans Set.inter_subset_left).trans (Metric.closedBall_subset_ball (by dsimp [φo]; linarith))
  · intro x hx heq
    have hh := (hφsup hx).2
    rw [heq] at hh
    exact hh (Metric.mem_ball_self (by dsimp [φi]; positivity))
  · intro i x hx
    have hu := hζsup (partial_tsupport_subset (ζ : Plane → ℝ) i hx)
    have hl := partial_tsupport_outside hζ1 i hx
    apply annular_cutoff_one θo θi
    · dsimp [θo]; exact hu.trans (by linarith)
    · dsimp [θi]; exact le_of_not_gt hl
  · intro x hx
    obtain ⟨hu, hl⟩ := hθsup hx
    apply annular_cutoff_one φo φi
    · change dist x x₀ ≤ 3*r/4
      change dist x x₀ ≤ 2*r/3 at hu
      linarith
    · exact le_of_not_gt hl
  · intro x hx
    have hu := hζsup (laplacian_tsupport_subset _ hx)
    have hl := laplacian_tsupport_outside hζ1 hx
    apply annular_cutoff_one φo φi
    · dsimp [φo]; exact hu.trans (by linarith)
    · dsimp [φi]; have hh : r/4≤dist x x₀ := le_of_not_gt hl; linarith

lemma exists_abs_bound {f : Plane → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |f x|≤C := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)

lemma exists_partial_abs_bound {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ i x, |coordPartial f i x|≤C := by
  obtain ⟨C₀, h₀, hb₀⟩ := exists_abs_bound (smooth_partial hf 0).continuous (compact_partial hc 0)
  obtain ⟨C₁, h₁, hb₁⟩ := exists_abs_bound (smooth_partial hf 1).continuous (compact_partial hc 1)
  refine ⟨max C₀ C₁, h₀.trans (le_max_left _ _), fun i x => ?_⟩
  fin_cases i
  · exact (hb₀ x).trans (le_max_left _ _)
  · exact (hb₁ x).trans (le_max_right _ _)

lemma exists_partial_abs_bound_on {f : Plane → ℝ} {F : Set Plane}
    (hf : Smooth f) (hF : IsCompact F) :
    ∃ C : ℝ, 0≤C ∧ ∀ i x, x∈F → |coordPartial f i x|≤C := by
  obtain ⟨C₀, hb₀⟩ := hF.exists_bound_of_continuousOn (smooth_partial hf 0).continuous.continuousOn
  obtain ⟨C₁, hb₁⟩ := hF.exists_bound_of_continuousOn (smooth_partial hf 1).continuous.continuousOn
  refine ⟨max (max C₀ C₁) 0, le_max_right _ _, fun i x hx => ?_⟩
  fin_cases i
  · exact (hb₀ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hb₁ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

lemma tilted_gradient_bound {χ : Plane → ℝ} {B : Plane} {S D C : ℝ} {F : Set Plane}
    (hχ : Smooth χ) (hS : 0≤S) (hSD : S≤D) (hBD : ‖B‖≤D) (_hC : 0≤C)
    (hχb : ∀ i x, x∈F → |coordPartial χ i x|≤C) :
    ∀ i x, x∈F → |coordPartial (tiltedWeight B S χ) i x|≤(1+C)*D := by
  intro i x hx
  rw [partial_tiltedWeight _ _ hχ]
  have hB : |B i|≤D := (PiLp.norm_apply_le B i).trans hBD
  calc
    |-B i-S*coordPartial χ i x| ≤ |-B i|+|S*coordPartial χ i x| := abs_sub _ _
    _ = |B i|+S*|coordPartial χ i x| := by rw [abs_neg, abs_mul, abs_of_nonneg hS]
    _ ≤ D+D*C := add_le_add hB (mul_le_mul hSD (hχb i x hx) (abs_nonneg _) (hS.trans hSD))
    _ = (1+C)*D := by ring

theorem cutoff_mass_comparison {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hU : ∀ j, Smooth (U j)) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (ζ φ : Plane → ℝ) (ρ C : ℝ), 0<ρ ∧ 0<C ∧
      Smooth ζ ∧ Smooth φ ∧ HasCompactSupport ζ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r₀ ∧ tsupport φ ⊆ Metric.ball x₀ r₀ ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧ (∀ x, 0≤φ x ∧ φ x≤1) ∧
      ∀ᶠ j in atTop,
        S j*l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(ζ x*U j x)) ≤
        C*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
  have hD (j : ℕ) : S j≤D j := by rw [hDdef]; exact le_add_of_nonneg_right (norm_nonneg _)
  have hBD (j : ℕ) : ‖B j‖≤D j := by rw [hDdef]; exact le_add_of_nonneg_left (hSpos j).le
  have hDpos (j : ℕ) : 0<D j := (hSpos j).trans_le (hD j)
  obtain ⟨r, hr, c, hc, j₀, hcar⟩ := local_carleman hχ hp hr₀ hSpos hS hD hb hd hK hpbound he hpgrad htrace ha
  obtain ⟨ζ, θ, φ, ρ, hρ, hζ, hθ, hφ, hcζ, hcθ, hcφ, hζsup, hθsup, hφsup,
    hζ1, hφaway, hφb, hθ1, hφ1, hφlap⟩ := exists_profile_cutoffs (x₀:=x₀) (lt_min hr hr₀)
  obtain ⟨C₁, hC₁, hζlap⟩ := exists_abs_bound (smooth_laplacian hζ).continuous (compact_laplacian hcζ)
  obtain ⟨C₂, hC₂, hζg⟩ := exists_partial_abs_bound hζ hcζ
  obtain ⟨C₃, hC₃, hθb⟩ := exists_abs_bound hθ.continuous hcθ
  obtain ⟨C₄, hC₄, hθg⟩ := exists_partial_abs_bound hθ hcθ
  obtain ⟨Cχ, hCχ, hχb⟩ := exists_partial_abs_bound_on hχ hcθ
  let Cζ := max C₁ C₂
  let Cθ := max C₃ C₄
  let CP := max Cp 0
  let CT := 1+Cχ
  let P := Cζ^2*(2+16*(2*CP*Cθ^2+16*Cθ^2+16*CT^2*Cθ^2))
  have hCP : 0≤CP := le_max_right _ _
  have hP : 0≤P := by dsimp [P]; positivity
  have hCZ : 0≤Cζ := hC₁.trans (le_max_left _ _)
  have hCT : 0≤Cθ := hC₃.trans (le_max_left _ _)
  have hCt : 0≤CT := by dsimp [CT]; linarith
  have hζr : tsupport ζ ⊆ Metric.ball x₀ r := hζsup.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hζr₀ : tsupport ζ ⊆ Metric.ball x₀ r₀ := hζsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hθr₀ : tsupport θ ⊆ Metric.ball x₀ r₀ := hθsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hφr₀ : tsupport φ ⊆ Metric.ball x₀ r₀ := hφsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  refine ⟨ζ, φ, ρ, P/c^2+1, hρ, by positivity, hζ, hφ, hcζ, hcφ, hζr₀, hφr₀,
    hζ1, hφaway, hφb, ?_⟩
  have heS : ∀ᶠ j in atTop, 1≤S j := hS.eventually (eventually_ge_atTop 1)
  have heK : ∀ᶠ j in atTop, |K j/D j|≤1 := by
    simpa only [abs_zero] using hK.abs.eventually_le_const (by norm_num : |(0:ℝ)|<1)
  filter_upwards [heS, heK, eventually_ge_atTop j₀] with j hSj hKj hj₀
  have hDj : 1≤D j := hSj.trans (hD j)
  have hKsq : (K j)^2≤(D j)^2 := by
    have hh : |K j|≤D j := by simpa only [one_mul] using abs_le_mul_of_div (hDpos j) hKj
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hDpos j).le).mpr hh
  have hTb := tilted_gradient_bound hχ (hSpos j).le (hD j) (hBD j) hCχ hχb
  have herr := weighted_cutoff_residual hζ hθ hφ (smooth_tiltedWeight _ _ hχ) (hU j) (hp j)
    hcζ hcθ hcφ hθ1 hφ1 hφlap hCP hCZ hCT (mul_nonneg hCt (hDpos j).le)
    (fun x => (hζlap x).trans (le_max_left _ _))
    (fun i x => (hζg i x).trans (le_max_right _ _))
    (fun x => (hθb x).trans (le_max_left _ _))
    (fun i x => (hθg i x).trans (le_max_right _ _)) hTb
    (fun x hx => (hpbound j x (hθr₀ hx)).trans (le_max_left _ _))
    (fun x hx => hPDE j x (hζr₀ hx)) (fun x hx => hPDE j x (hθr₀ hx))
  have hpre := cutoff_prefactor_bound (Cp:=CP) (Cζ:=Cζ) (Cθ:=Cθ) (Ct:=CT) hDj hKsq hCP
  have herr' : l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
      (euclideanLaplacian (fun y => ζ y*U j y) x+(K j)^2*p j x*(ζ x*U j x))) ≤
      (P*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)))*(D j)^2 := by
    exact herr.trans ((mul_le_mul_of_nonneg_right hpre (l2sq_nonneg _)).trans_eq (by dsimp [P]; ring))
  have hcar' := hcar j hj₀ (fun x => ζ x*U j x) (hζ.mul (hU j)) hcζ.mul_right
    (tsupport_mul_subset_left.trans hζr)
  have hh := cancel_carleman_frequency (hSpos j).le (hDpos j) hc hcar' herr'
  apply hh.trans
  have hnn := l2sq_nonneg (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x))
  rw [mul_div_right_comm]
  nlinarith only [hnn]

theorem cutoff_mass_comparison_on {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (ζ φ : Plane → ℝ) (ρ C : ℝ), 0<ρ ∧ 0<C ∧
      Smooth ζ ∧ Smooth φ ∧ HasCompactSupport ζ ∧ HasCompactSupport φ ∧
      tsupport ζ ⊆ Metric.ball x₀ r₀ ∧ tsupport φ ⊆ Metric.ball x₀ r₀ ∧
      (∀ x ∈ Metric.ball x₀ ρ, ζ x=1) ∧
      (∀ x ∈ tsupport φ, x≠x₀) ∧ (∀ x, 0≤φ x ∧ φ x≤1) ∧
      ∀ᶠ j in atTop,
        S j*l2sq (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(ζ x*U j x)) ≤
        C*l2sq (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
  obtain ⟨η, rη, hrη, hη, _, hηsub, hη1⟩ := exists_smooth_cutoff (hΩ.mem_nhds hx₀)
  let χ' : Plane → ℝ := fun x => η x*χ x
  let p' : ℕ → Plane → ℝ := fun j x => η x*p j x
  let U' : ℕ → Plane → ℝ := fun j x => η x*U j x
  have hχ' : Smooth χ' := smooth_cutoff_mul hΩ hη hηsub hχ
  have hp' (j : ℕ) : Smooth (p' j) := smooth_cutoff_mul hΩ hη hηsub (hp j)
  have hU' (j : ℕ) : Smooth (U' j) := smooth_cutoff_mul hΩ hη hηsub (hU j)
  have hχeq (x : Plane) (hx : x∈Metric.ball x₀ rη) : χ' x=χ x := by
    dsimp [χ']; rw [hη1 x hx, one_mul]
  have hpeq (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : p' j x=p j x := by
    dsimp [p']; rw [hη1 x hx, one_mul]
  have hUeq (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : U' j x=U j x := by
    dsimp [U']; rw [hη1 x hx, one_mul]
  have hχev : χ' =ᶠ[𝓝 x₀] χ := Filter.Eventually.mono
    (Metric.ball_mem_nhds x₀ hrη) fun x hx => hχeq x hx
  have hpev (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : p' j =ᶠ[𝓝 x] p j :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hpeq j y hy
  have hUev (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ rη) : U' j =ᶠ[𝓝 x] U j :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hUeq j y hy
  have hpb' (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) : |p' j x|≤Cp := by
    rw [hpeq j x (Metric.ball_subset_ball (min_le_left _ _) hx)]
    exact hpbound j x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hpg' (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) :
      |(K j)^2*coordPartial (p' j) i x/(S j*D j)|≤e j := by
    rw [(partial_eventuallyEq (hpev j x (Metric.ball_subset_ball (min_le_left _ _) hx)) i).eq_of_nhds]
    exact hpgrad j i x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hPDE' (j : ℕ) (x : Plane) (hx : x∈Metric.ball x₀ (min rη r₀)) :
      euclideanLaplacian (U' j) x+(K j)^2*p' j x*U' j x=0 := by
    have hxη := Metric.ball_subset_ball (min_le_left rη r₀) hx
    rw [(laplacian_eventuallyEq (hUev j x hxη)).eq_of_nhds, hpeq j x hxη, hUeq j x hxη]
    exact hPDE j x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have htr' : euclideanLaplacian χ' x₀<0 := by
    rw [(laplacian_eventuallyEq hχev).eq_of_nhds]; exact htrace
  have ha' : b+d • coordinateGradient χ' x₀ ≠ 0 := by
    rw [gradient_eq_of_eventuallyEq hχev]; exact ha
  obtain ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ, hζsub, hφsub,
    hζ1, hφaway, hφb, hcomp⟩ := cutoff_mass_comparison hχ' hp' hU' (lt_min hrη hr₀)
      hSpos hS hDdef hb hd hK hpb' he hpg' hPDE' htr' ha'
  refine ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ,
    hζsub.trans (Metric.ball_subset_ball (min_le_right _ _)),
    hφsub.trans (Metric.ball_subset_ball (min_le_right _ _)), hζ1, hφaway, hφb, ?_⟩
  have hweight (a : Plane → ℝ) (hasub : tsupport a ⊆ Metric.ball x₀ (min rη r₀)) (j : ℕ) :
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ' x)*(a x*U' j x)) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(a x*U j x)) := by
    funext x
    by_cases hx : x∈tsupport a
    · have hh := Metric.ball_subset_ball (min_le_left rη r₀) (hasub hx)
      simp only [tiltedWeight, hχeq x hh, hUeq j x hh]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  filter_upwards [hcomp] with j hj
  rw [hweight ζ hζsub] at hj
  have heq : (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ' x)*U' j x)) =
      (fun x => φ x*(Real.exp (tiltedWeight (B j) (S j) χ x)*U j x)) := by
    simpa only [mul_left_comm] using hweight φ hφsub j
  rwa [heq] at hj

end Profiles
end SharpNodal

noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter Set
namespace SharpNodal.Profiles

def logRate (S : ℝ) (m : ℝ≥0∞) : EReal := ((2*S)⁻¹ : ℝ) * m.log

lemma ereal_pos_mul_lt_coe_iff {c : ℝ} (hc : 0<c) (a : EReal) (b : ℝ) :
    (c:EReal)*a < (b:EReal) ↔ a < ((b/c : ℝ):EReal) := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [lt_div_iff₀ hc, mul_comm]

lemma ereal_coe_lt_pos_mul_iff {c : ℝ} (hc : 0<c) (a : EReal) (b : ℝ) :
    (b:EReal) < (c:EReal)*a ↔ ((b/c : ℝ):EReal) < a := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [div_lt_iff₀ hc, mul_comm]

lemma logRate_lt_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m < (a:EReal) ↔ m < ENNReal.ofReal (Real.exp (2*S*a)) := by
  rw [logRate, ereal_pos_mul_lt_coe_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma lt_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) < logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) < m := by
  rw [logRate, ereal_coe_lt_pos_mul_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma logRate_le_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m ≤ (a:EReal) ↔ m ≤ ENNReal.ofReal (Real.exp (2*S*a)) := by
  simpa only [not_lt] using not_congr (lt_logRate_iff (a:=a) hS m)

lemma le_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) ≤ logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) ≤ m := by
  simpa only [not_lt] using not_congr (logRate_lt_iff (a:=a) hS m)

lemma logRate_ofReal_exp {S a : ℝ} (hS : 0<S) :
    logRate S (ENNReal.ofReal (Real.exp (2*S*a)))=(a:EReal) := by
  apply le_antisymm
  · exact (logRate_le_iff hS _).mpr le_rfl
  · exact (le_logRate_iff hS _).mpr le_rfl

lemma logRate_zero {S : ℝ} (hS : 0<S) : logRate S 0=⊥ := by
  rw [logRate, ENNReal.log_zero, EReal.coe_mul_bot_of_pos]
  positivity

lemma logRate_mono {S : ℝ} (hS : 0<S) {m₁ m₂ : ℝ≥0∞} (hm : m₁ ≤ m₂) :
    logRate S m₁≤logRate S m₂ := by
  by_contra hn
  obtain ⟨a, ha, hb⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  exact (not_lt_of_ge hm) (((logRate_lt_iff hS _).mp ha).trans ((lt_logRate_iff hS _).mp hb))

lemma exponential_gap {S : ℕ → ℝ} {a b C : ℝ} (hS : Tendsto S atTop atTop)
    (hgap : a<b) (hC : 0<C) :
    ∀ᶠ j in atTop, C*Real.exp (2*S j*a)<Real.exp (2*S j*b) := by
  have hδ : 0<2*(b-a) := by linarith
  have he : ∀ᶠ j in atTop, Real.log C/(2*(b-a))<S j :=
    hS.eventually (eventually_gt_atTop _)
  filter_upwards [he] with j hj
  have hj' : Real.log C<2*S j*(b-a) := by
    have hh := (div_lt_iff₀ hδ).mp hj
    nlinarith only [hh]
  rw [← Real.exp_log hC, ← Real.exp_add, Real.exp_lt_exp]
  nlinarith only [hj']

lemma no_exponential_gap {S : ℕ → ℝ} {A B : ℕ → ℝ≥0∞} {a b C : ℝ}
    (hS : Tendsto S atTop atTop) (hgap : a<b) (hC : 0<C)
    (hA : ∀ᶠ j in atTop, A j≤ENNReal.ofReal (Real.exp (2*S j*a)))
    (hB : ∀ᶠ j in atTop, ENNReal.ofReal (Real.exp (2*S j*b))≤B j)
    (hcomp : ∀ᶠ j in atTop, B j≤ENNReal.ofReal C*A j) : False := by
  have hg := exponential_gap hS hgap hC
  obtain ⟨j, hAj, hBj, hcj, hgj⟩ := (hA.and (hB.and (hcomp.and hg))).exists
  have hle := hBj.trans (hcj.trans (mul_le_mul' le_rfl hAj))
  rw [← ENNReal.ofReal_mul hC.le] at hle
  have hle' : Real.exp (2*S j*b)≤C*Real.exp (2*S j*a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  exact (not_le_of_gt hgj) hle'

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

def tiltedMass (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ)
    (f : Plane → ℝ) (E : Set Plane) : ℝ≥0∞ :=
  ∫⁻ x in E, ENNReal.ofReal (c*(Real.exp (tiltedWeight B S (fun y => -f y) x)*U x)^2)

lemma tiltedMass_neg (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ)
    (χ : Plane → ℝ) (E : Set Plane) :
    tiltedMass S B U c (fun x => -χ x) E =
      ∫⁻ x in E, ENNReal.ofReal (c*(Real.exp (tiltedWeight B S χ x)*U x)^2) := by
  simp only [tiltedMass, neg_neg]

lemma integral_square_mass {g : Plane → ℝ} {c : ℝ}
    (hg : Integrable (fun x => g x*g x)) (hc : 0≤c) :
    ENNReal.ofReal c*ENNReal.ofReal (l2sq g) = ∫⁻ x, ENNReal.ofReal (c*(g x)^2) := by
  rw [← ENNReal.ofReal_mul hc, l2sq, ← integral_const_mul]
  simpa only [pow_two] using ofReal_integral_eq_lintegral_ofReal (hg.const_mul c)
    (Filter.Eventually.of_forall fun x => mul_nonneg hc (mul_self_nonneg (g x)))

lemma cutoff_square_integrable_on {Ω : Set Plane} {a g : Plane → ℝ}
    (hΩ : IsOpen Ω) (ha : Smooth a) (hca : HasCompactSupport a)
    (haΩ : tsupport a⊆Ω) (hg : ContDiffOn ℝ ∞ g Ω) :
    Integrable (fun x => (a x*g x)*(a x*g x)) := by
  have hsm := smooth_cutoff_mul hΩ ha haΩ hg
  exact (hsm.mul hsm).continuous.integrable_of_hasCompactSupport hca.mul_right.mul_right

lemma cutoff_square_mass_lower {a g : Plane → ℝ} {c : ℝ} {G : Set Plane}
    (hc : 0≤c) (hGm : MeasurableSet G) (hG : ∀ x∈G, a x=1)
    (hi : Integrable (fun x => (a x*g x)*(a x*g x))) :
    (∫⁻ x in G, ENNReal.ofReal (c*(g x)^2)) ≤
      ENNReal.ofReal c*ENNReal.ofReal (l2sq (fun x => a x*g x)) := by
  rw [integral_square_mass hi hc]
  calc
    _ = ∫⁻ x in G, ENNReal.ofReal (c*(a x*g x)^2) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hGm] with x hx
      rw [hG x hx, one_mul]
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma cutoff_square_mass_upper {a g : Plane → ℝ} {c : ℝ}
    (hc : 0≤c) (ha : ∀ x, 0≤a x ∧ a x≤1)
    (hi : Integrable (fun x => (a x*g x)*(a x*g x))) :
    ENNReal.ofReal c*ENNReal.ofReal (l2sq (fun x => a x*g x)) ≤
      ∫⁻ x in tsupport a, ENNReal.ofReal (c*(g x)^2) := by
  rw [integral_square_mass hi hc, ← lintegral_indicator (isClosed_tsupport a).measurableSet]
  apply lintegral_mono
  intro x
  by_cases hx : x∈tsupport a
  · rw [Set.indicator_of_mem hx]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hc
    have hh : (a x)^2≤1 := by nlinarith only [(ha x).1, (ha x).2]
    nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg (g x))]
  · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

lemma smooth_tiltedWeight_on {Ω : Set Plane} {χ : Plane → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ Ω) (B : Plane) (S : ℝ) :
    ContDiffOn ℝ ∞ (tiltedWeight B S χ) Ω := by
  unfold tiltedWeight
  exact (innerSL ℝ B).contDiff.contDiffOn.neg.sub (contDiffOn_const.mul hχ)

theorem tilted_mass_comparison_on {Ω : Set Plane} {p U : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e c : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀∈Ω) (hball : Metric.ball x₀ r₀⊆Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω)
    (hU : ∀ j, ContDiffOn ℝ ∞ (U j) Ω) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hc : ∀ j, 0<c j) (hDdef : ∀ j, D j=S j+‖B j‖)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (hPDE : ∀ j x, x ∈ Metric.ball x₀ r₀ →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ (F G : Set Plane) (C : ℝ), IsCompact F ∧ IsOpen G ∧ 0<C ∧
      F⊆Metric.ball x₀ r₀ ∧ G⊆Metric.ball x₀ r₀ ∧ x₀∉F ∧ x₀∈G ∧
      ∀ᶠ j in atTop,
        tiltedMass (S j) (B j) (U j) (c j) (fun x => -χ x) G ≤
          ENNReal.ofReal C*tiltedMass (S j) (B j) (U j) (c j) (fun x => -χ x) F := by
  obtain ⟨ζ, φ, ρ, C, hρ, hC, hζ, hφ, hcζ, hcφ, hζsub, hφsub,
    hζ1, hφaway, hφb, hcomp⟩ := cutoff_mass_comparison_on hΩ hx₀ hχ hp hU hr₀
      hSpos hS hDdef hb hd hK hpbound he hpgrad hPDE htrace ha
  let G := Metric.ball x₀ (min ρ r₀)
  have hG : G⊆Metric.ball x₀ ρ := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨tsupport φ, G, C, hcφ, Metric.isOpen_ball, hC, hφsub,
    Metric.ball_subset_ball (min_le_right _ _), fun hh => hφaway x₀ hh rfl,
    Metric.mem_ball_self (lt_min hρ hr₀), ?_⟩
  have heS : ∀ᶠ j in atTop, 1≤S j := hS.eventually (eventually_ge_atTop 1)
  filter_upwards [hcomp, heS] with j hj hSj
  let g : Plane → ℝ := fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*U j x
  have hg : ContDiffOn ℝ ∞ g Ω :=
    (smooth_tiltedWeight_on hχ (B j) (S j)).exp.mul (hU j)
  have hiζ := cutoff_square_integrable_on hΩ hζ hcζ (hζsub.trans hball) hg
  have hiφ := cutoff_square_integrable_on hΩ hφ hcφ (hφsub.trans hball) hg
  have hleft := cutoff_square_mass_lower (hc j).le Metric.isOpen_ball.measurableSet (fun x hx => hζ1 x (hG hx)) hiζ
  have hright := cutoff_square_mass_upper (hc j).le hφb hiφ
  have hnorm : l2sq (fun x => ζ x*g x) ≤ C*l2sq (fun x => φ x*g x) := by
    have hj' : S j*l2sq (fun x => ζ x*g x) ≤ C*l2sq (fun x => φ x*g x) := by
      simpa only [g, mul_left_comm] using hj
    exact (le_mul_of_one_le_left (l2sq_nonneg _) hSj).trans hj'
  rw [tiltedMass_neg, tiltedMass_neg]
  apply hleft.trans
  calc
    _ ≤ ENNReal.ofReal (c j)*(ENNReal.ofReal C*ENNReal.ofReal (l2sq (fun x => φ x*g x))) := by
      apply mul_le_mul' le_rfl
      rw [← ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal hnorm
    _ = ENNReal.ofReal C*(ENNReal.ofReal (c j)*ENNReal.ofReal (l2sq (fun x => φ x*g x))) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hright

end SharpNodal.Profiles

end
end
end

end OAI
