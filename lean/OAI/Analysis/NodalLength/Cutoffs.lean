import OAI.Analysis.NodalLength.Carleman

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma smooth_cutoff_mul {Ω : Set Plane} {ζ f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hζ : Smooth ζ) (hsub : tsupport ζ ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) : Smooth (fun x => ζ x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ζ
  · exact hζ.contDiffAt.mul (hf.contDiffAt (hΩ.mem_nhds (hsub hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

lemma exists_smooth_cutoff {Ω : Set Plane} {x₀ : Plane}
    (hΩ : Ω ∈ 𝓝 x₀) : ∃ (ζ : Plane → ℝ) (r : ℝ),
      0<r ∧ Smooth ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ω ∧
      ∀ x ∈ Metric.ball x₀ r, ζ x=1 := by
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hΩ
  let ζ : ContDiffBump x₀ :=
    { rIn := R/4
      rOut := R/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨ζ, R/4, by positivity, ζ.contDiff, ζ.hasCompactSupport, ?_, ?_⟩
  · rw [ζ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [ζ]; linarith)).trans hRsub
  · intro x hx
    exact ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

lemma partial_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 2) : coordPartial f i =ᶠ[𝓝 x] coordPartial g i := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy

lemma laplacian_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) : euclideanLaplacian f =ᶠ[𝓝 x] euclideanLaplacian g := by
  have h₀ := partial_eventuallyEq (partial_eventuallyEq h 0) 0
  have h₁ := partial_eventuallyEq (partial_eventuallyEq h 1) 1
  filter_upwards [h₀, h₁] with y hy₀ hy₁
  simp only [euclideanLaplacian, Fin.sum_univ_two, hy₀, hy₁]

lemma gradient_eq_of_eventuallyEq {f g : Plane → ℝ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) : coordinateGradient f x = coordinateGradient g x := by
  ext i
  exact (partial_eventuallyEq h i).eq_of_nhds

lemma young_pairing {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    -2*(∫ x, f x*g x) ≤ (1/2 : ℝ)*l2sq f+2*l2sq g := by
  have h := l2sq_add (g := fun x => 2*g x) hf (contDiff_const.mul hg) hcf hcg.mul_left
  have hi : (∫ x, f x*(2*g x))=2*(∫ x, f x*g x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [l2sq_const_mul, hi] at h
  linarith only [l2sq_nonneg (fun x => f x+2*g x), h]

lemma weighted_energy_component {η U : Plane → ℝ} (hη : Smooth η) (hU : Smooth U)
    (hc : HasCompactSupport η) (i : Fin 2) :
    l2sq (fun x => η x*coordPartial U i x) =
      -(∫ x, coordPartial (coordPartial U i) i x*(η x*η x*U x))-
      2*(∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
  have h := integral_mul_partial (smooth_partial hU i) ((hη.mul hη).mul hU)
    hc.mul_right.mul_right i
  have hi₁ := integrable_mul_compact_left (hη.mul (smooth_partial hU i))
    (hη.mul (smooth_partial hU i)) hc.mul_right
  have hi₂ := integrable_mul_compact_left (hη.mul (smooth_partial hU i))
    ((smooth_partial hη i).mul hU) hc.mul_right
  have heq : (∫ x, coordPartial U i x*coordPartial (fun y => η y*η y*U y) i x) =
      l2sq (fun x => η x*coordPartial U i x)+
      2*(∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
    calc
      _ = ∫ x, (η x*coordPartial U i x)*(η x*coordPartial U i x)+
          2*((η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [partial_mul (hη.mul hη) hU, partial_mul hη hη]
        ring
      _ = _ := by rw [integral_add hi₁ (hi₂.const_mul 2), integral_const_mul]; rfl
  linarith only [h, heq]

lemma weighted_energy_identity {η U : Plane → ℝ} (hη : Smooth η) (hU : Smooth U)
    (hc : HasCompactSupport η) :
    (∑ i : Fin 2, l2sq (fun x => η x*coordPartial U i x)) =
      -(∫ x, euclideanLaplacian U x*(η x*η x*U x))-
      2*(∑ i : Fin 2, ∫ x, (η x*coordPartial U i x)*(coordPartial η i x*U x)) := by
  rw [show (∫ x, euclideanLaplacian U x*(η x*η x*U x)) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial U i) i x*(η x*η x*U x) from
    integral_sum_mul Finset.univ (fun i _ => smooth_partial (smooth_partial hU i) i)
      ((hη.mul hη).mul hU) hc.mul_right.mul_right]
  simp only [Fin.sum_univ_two, weighted_energy_component hη hU hc]
  ring

theorem caccioppoli {η U p : Plane → ℝ} {K Cp : ℝ}
    (hη : Smooth η) (hU : Smooth U) (hp : Smooth p) (hc : HasCompactSupport η)
    (hCp : 0≤Cp) (hpb : ∀ x ∈ tsupport η, |p x|≤Cp)
    (hPDE : ∀ x ∈ tsupport η, euclideanLaplacian U x+K^2*p x*U x=0) :
    (∑ i : Fin 2, l2sq (fun x => η x*coordPartial U i x)) ≤
      2*K^2*Cp*l2sq (fun x => η x*U x)+
      4*(∑ i : Fin 2, l2sq (fun x => coordPartial η i x*U x)) := by
  have hE := weighted_energy_identity hη hU hc
  have hI : (∫ x, euclideanLaplacian U x*(η x*η x*U x)) =
      -K^2*(∫ x, p x*((η x*U x)*(η x*U x))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport η
    · have hh := hPDE x hx
      calc
        _ = (-K^2*p x*U x)*(η x*η x*U x) := by congr 1; linarith only [hh]
        _ = _ := by ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  rw [hI] at hE
  have hpI := integral_coefficient_square_abs_le hp (hη.mul hU) hc.mul_right hCp
    (fun x hx => hpb x (tsupport_mul_subset_left hx))
  have hpI' : (∫ x, p x*((η x*U x)*(η x*U x))) ≤ Cp*l2sq (fun x => η x*U x) :=
    (le_abs_self _).trans hpI
  have hY (i : Fin 2) := young_pairing (hη.mul (smooth_partial hU i))
    ((smooth_partial hη i).mul hU) hc.mul_right (compact_partial hc i).mul_right
  have hYsum := add_le_add (hY 0) (hY 1)
  simp only [Fin.sum_univ_two] at hE ⊢
  nlinarith only [hE, hYsum, mul_le_mul_of_nonneg_left hpI' (sq_nonneg K)]

open Filter in

theorem local_carleman_on {Ω : Set Plane} {p : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ Ω)
    (hχ : ContDiffOn ℝ ∞ χ Ω) (hp : ∀ j, ContDiffOn ℝ ∞ (p j) Ω) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ r : ℝ, 0<r ∧ ∃ c : ℝ, 0<c ∧ ∃ j₀ : ℕ, ∀ j≥j₀, ∀ w : Plane → ℝ,
      Smooth w → HasCompactSupport w → tsupport w ⊆ Metric.ball x₀ r →
      c*Real.sqrt (S j)*D j*l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) ≤
        l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
          (euclideanLaplacian w x+(K j)^2*p j x*w x)) := by
  obtain ⟨ζ, rζ, hrζ, hζ, _, hζsub, hζ1⟩ := exists_smooth_cutoff (hΩ.mem_nhds hx₀)
  let χ' : Plane → ℝ := fun x => ζ x*χ x
  let p' : ℕ → Plane → ℝ := fun j x => ζ x*p j x
  have hχ' : Smooth χ' := smooth_cutoff_mul hΩ hζ hζsub hχ
  have hp' (j : ℕ) : Smooth (p' j) := smooth_cutoff_mul hΩ hζ hζsub (hp j)
  have hχeq (x : Plane) (hx : x ∈ Metric.ball x₀ rζ) : χ' x=χ x := by
    dsimp [χ']; rw [hζ1 x hx, one_mul]
  have hpeq (j : ℕ) (x : Plane) (hx : x ∈ Metric.ball x₀ rζ) : p' j x=p j x := by
    dsimp [p']; rw [hζ1 x hx, one_mul]
  have hχev : χ' =ᶠ[𝓝 x₀] χ := Filter.Eventually.mono (Metric.ball_mem_nhds x₀ hrζ) fun x hx => hχeq x hx
  have hpev (j : ℕ) (x : Plane) (hx : x ∈ Metric.ball x₀ rζ) : p' j =ᶠ[𝓝 x] p j :=
    Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) fun y hy => hpeq j y hy
  have hpb' (j : ℕ) (x : Plane) (hx : x ∈ Metric.ball x₀ (min rζ r₀)) : |p' j x|≤Cp := by
    rw [hpeq j x (Metric.ball_subset_ball (min_le_left _ _) hx)]
    exact hpbound j x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hpg' (j : ℕ) (i : Fin 2) (x : Plane) (hx : x ∈ Metric.ball x₀ (min rζ r₀)) :
      |(K j)^2*coordPartial (p' j) i x/(S j*D j)|≤e j := by
    rw [(partial_eventuallyEq (hpev j x (Metric.ball_subset_ball (min_le_left _ _) hx)) i).eq_of_nhds]
    exact hpgrad j i x (Metric.ball_subset_ball (min_le_right _ _) hx)
  have htr' : euclideanLaplacian χ' x₀<0 := by
    rw [(laplacian_eventuallyEq hχev).eq_of_nhds]; exact htrace
  have ha' : b+d • coordinateGradient χ' x₀ ≠ 0 := by
    rw [gradient_eq_of_eventuallyEq hχev]; exact ha
  obtain ⟨r, hr, c, hc, j₀, hcar⟩ := local_carleman hχ' hp' (lt_min hrζ hr₀)
    hSpos hS hD hb hd hK hpb' he hpg' htr' ha'
  refine ⟨min r rζ, lt_min hr hrζ, c, hc, j₀, ?_⟩
  intro j hj w hw hcw hsup
  have hsup' : tsupport w ⊆ Metric.ball x₀ r := hsup.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hsupζ : tsupport w ⊆ Metric.ball x₀ rζ := hsup.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hweight : (fun x => Real.exp (tiltedWeight (B j) (S j) χ' x)*w x) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) := by
    funext x
    by_cases hx : x ∈ tsupport w
    · simp only [tiltedWeight, hχeq x (hsupζ hx)]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hop : (fun x => Real.exp (tiltedWeight (B j) (S j) χ' x)*
      (euclideanLaplacian w x+(K j)^2*p' j x*w x)) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
      (euclideanLaplacian w x+(K j)^2*p j x*w x)) := by
    funext x
    by_cases hx : x ∈ tsupport w
    · simp only [tiltedWeight, hχeq x (hsupζ hx), hpeq j x (hsupζ hx)]
    · have hlap : euclideanLaplacian w x=0 := by
        unfold euclideanLaplacian
        apply Finset.sum_eq_zero
        intro i _
        exact image_eq_zero_of_notMem_tsupport (fun hh => hx (partial_tsupport_subset w i (partial_tsupport_subset (coordPartial w i) i hh)))
      simp only [image_eq_zero_of_notMem_tsupport hx, hlap, mul_zero, add_zero]
  simpa only [hweight, hop] using hcar j hj w hw hcw hsup'

lemma l2sq_cutoff_comparison {a φ F : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hφ : Smooth φ) (hF : Smooth F) (hcφ : HasCompactSupport φ)
    (hC : 0≤C) (haC : ∀ x, |a x|≤C) (hφ1 : ∀ x ∈ tsupport a, φ x=1) :
    l2sq (fun x => a x*F x) ≤ C ^ 2*l2sq (fun x => φ x*F x) := by
  have heq : (fun x => a x*F x)=(fun x => a x*(φ x*F x)) := by
    funext x
    by_cases hx : a x=0
    · simp only [hx, zero_mul]
    · rw [hφ1 x (subset_closure hx), one_mul]
  rw [heq]
  exact l2sq_coefficient_mul_le ha (hφ.mul hF) hcφ.mul_right hC (fun x _ => haC x)

theorem exponential_caccioppoli {θ φ T U p : Plane → ℝ} {K Cp Cθ Ct : ℝ}
    (hθ : Smooth θ) (hφ : Smooth φ) (hT : Smooth T) (hU : Smooth U) (hp : Smooth p)
    (hcθ : HasCompactSupport θ) (hcφ : HasCompactSupport φ)
    (hφ1 : ∀ x ∈ tsupport θ, φ x=1)
    (hCp : 0≤Cp) (hCθ : 0≤Cθ) (hCt : 0≤Ct)
    (hθb : ∀ x, |θ x|≤Cθ) (hθg : ∀ i x, |coordPartial θ i x|≤Cθ)
    (hTb : ∀ i x, x ∈ tsupport θ → |coordPartial T i x|≤Ct)
    (hpb : ∀ x ∈ tsupport θ, |p x|≤Cp)
    (hPDE : ∀ x ∈ tsupport θ, euclideanLaplacian U x+K^2*p x*U x=0) :
    (∑ i : Fin 2, l2sq (fun x => (Real.exp (T x)*θ x)*coordPartial U i x)) ≤
      (2*K^2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2)*
        l2sq (fun x => φ x*(Real.exp (T x)*U x)) := by
  let η : Plane → ℝ := fun x => Real.exp (T x)*θ x
  let M := l2sq (fun x => φ x*(Real.exp (T x)*U x))
  have hη : Smooth η := hT.exp.mul hθ
  have hcη : HasCompactSupport η := hcθ.mul_left
  have hsupη : tsupport η ⊆ tsupport θ := tsupport_mul_subset_right
  have hηbound : l2sq (fun x => η x*U x) ≤ Cθ^2*M := by
    have hh := l2sq_cutoff_comparison hθ hφ (hT.exp.mul hU) hcφ hCθ hθb hφ1
    simpa only [η, M, mul_left_comm, mul_assoc, mul_comm] using hh
  have hpartbound (i : Fin 2) : l2sq (fun x => coordPartial η i x*U x) ≤
      (2*Cθ^2+2*Ct^2*Cθ^2)*M := by
    have heq : (fun x => coordPartial η i x*U x)=
        (fun x => coordPartial θ i x*(Real.exp (T x)*U x)+coordPartial T i x*(η x*U x)) := by
      funext x
      dsimp [η]
      rw [partial_exp_mul hT hθ]
      ring
    rw [heq]
    have hsum := l2sq_add_le ((smooth_partial hθ i).mul (hT.exp.mul hU))
      ((smooth_partial hT i).mul (hη.mul hU)) (compact_partial hcθ i).mul_right hcη.mul_right.mul_left
    have hfirst := l2sq_cutoff_comparison (smooth_partial hθ i) hφ (hT.exp.mul hU) hcφ hCθ
      (hθg i) (fun x hx => hφ1 x (partial_tsupport_subset θ i hx))
    have hsecond := l2sq_coefficient_mul_le (smooth_partial hT i) (hη.mul hU) hcη.mul_right hCt
      (fun x hx => hTb i x (hsupη (tsupport_mul_subset_left hx)))
    have hh := mul_le_mul_of_nonneg_left hηbound (sq_nonneg Ct)
    dsimp [M] at hηbound ⊢
    nlinarith only [hsum, hfirst, hsecond, hh]
  have hbasic := caccioppoli hη hU hp hcη hCp
    (fun x hx => hpb x (hsupη hx)) (fun x hx => hPDE x (hsupη hx))
  have hpotential := mul_le_mul_of_nonneg_left hηbound
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) (sq_nonneg K)) hCp)
  have h₀ := hpartbound 0
  have h₁ := hpartbound 1
  simp only [Fin.sum_univ_two] at hbasic ⊢
  dsimp [η] at hbasic
  dsimp [M] at hpotential h₀ h₁
  nlinarith only [hbasic, hpotential, h₀, h₁]

lemma partial2_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => f y*g y) i) i x =
      coordPartial (coordPartial f i) i x*g x+2*coordPartial f i x*coordPartial g i x+
      f x*coordPartial (coordPartial g i) i x := by
  rw [show coordPartial (fun y => f y*g y) i =
      (fun y => coordPartial f i y*g y+f y*coordPartial g i y) from funext (partial_mul hf hg i)]
  rw [partial_add ((smooth_partial hf i).mul hg) (hf.mul (smooth_partial hg i)),
    partial_mul (smooth_partial hf i) hg, partial_mul hf (smooth_partial hg i)]
  ring

lemma laplacian_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun y => f y*g y) x =
      euclideanLaplacian f x*g x+2*(∑ i : Fin 2, coordPartial f i x*coordPartial g i x)+
      f x*euclideanLaplacian g x := by
  simp only [euclideanLaplacian, Fin.sum_univ_two, partial2_mul hf hg]
  ring

lemma cutoff_residual {ζ U p : Plane → ℝ} {K : ℝ} (hζ : Smooth ζ) (hU : Smooth U)
    (hPDE : ∀ x ∈ tsupport ζ, euclideanLaplacian U x+K^2*p x*U x=0) (x : Plane) :
    euclideanLaplacian (fun y => ζ y*U y) x+K^2*p x*(ζ x*U x) =
      euclideanLaplacian ζ x*U x+2*(∑ i : Fin 2, coordPartial ζ i x*coordPartial U i x) := by
  rw [laplacian_mul hζ hU]
  have hz : ζ x*(euclideanLaplacian U x+K^2*p x*U x)=0 := by
    by_cases hx : x ∈ tsupport ζ
    · rw [hPDE x hx, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  nlinarith only [hz]

lemma weighted_cutoff_residual {ζ θ φ T U p : Plane → ℝ} {K Cp Cζ Cθ Ct : ℝ}
    (hζ : Smooth ζ) (hθ : Smooth θ) (hφ : Smooth φ) (hT : Smooth T) (hU : Smooth U)
    (hp : Smooth p) (hcζ : HasCompactSupport ζ) (hcθ : HasCompactSupport θ)
    (hcφ : HasCompactSupport φ)
    (hθ1 : ∀ i x, x ∈ tsupport (coordPartial ζ i) → θ x=1)
    (hφ1 : ∀ x ∈ tsupport θ, φ x=1)
    (hφlap : ∀ x ∈ tsupport (euclideanLaplacian ζ), φ x=1)
    (hCp : 0≤Cp) (hCζ : 0≤Cζ) (hCθ : 0≤Cθ) (hCt : 0≤Ct)
    (hζlap : ∀ x, |euclideanLaplacian ζ x|≤Cζ)
    (hζg : ∀ i x, |coordPartial ζ i x|≤Cζ)
    (hθb : ∀ x, |θ x|≤Cθ) (hθg : ∀ i x, |coordPartial θ i x|≤Cθ)
    (hTb : ∀ i x, x ∈ tsupport θ → |coordPartial T i x|≤Ct)
    (hpb : ∀ x ∈ tsupport θ, |p x|≤Cp)
    (hPDEζ : ∀ x ∈ tsupport ζ, euclideanLaplacian U x+K^2*p x*U x=0)
    (hPDEθ : ∀ x ∈ tsupport θ, euclideanLaplacian U x+K^2*p x*U x=0) :
    l2sq (fun x => Real.exp (T x)*(euclideanLaplacian (fun y => ζ y*U y) x+
      K^2*p x*(ζ x*U x))) ≤
      Cζ^2*(2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2))*
        l2sq (fun x => φ x*(Real.exp (T x)*U x)) := by
  let a : Plane → ℝ := fun x => euclideanLaplacian ζ x*(Real.exp (T x)*U x)
  let b : Fin 2 → Plane → ℝ := fun i x => coordPartial ζ i x*(Real.exp (T x)*coordPartial U i x)
  let M := l2sq (fun x => φ x*(Real.exp (T x)*U x))
  have ha : Smooth a := (smooth_laplacian hζ).mul (hT.exp.mul hU)
  have hb (i : Fin 2) : Smooth (b i) := (smooth_partial hζ i).mul (hT.exp.mul (smooth_partial hU i))
  have hca : HasCompactSupport a := (compact_laplacian hcζ).mul_right
  have hcb (i : Fin 2) : HasCompactSupport (b i) := (compact_partial hcζ i).mul_right
  have heq : (fun x => Real.exp (T x)*(euclideanLaplacian (fun y => ζ y*U y) x+
      K^2*p x*(ζ x*U x)))=(fun x => a x+2*(b 0 x+b 1 x)) := by
    funext x
    rw [cutoff_residual hζ hU hPDEζ, Fin.sum_univ_two]
    dsimp [a, b]; ring
  rw [heq]
  have hsum := l2sq_add_le (g := fun x => 2*(b 0 x+b 1 x)) ha (contDiff_const.mul ((hb 0).add (hb 1))) hca
    ((hcb 0).add (hcb 1)).mul_left
  rw [l2sq_const_mul] at hsum
  have hsum' := l2sq_add_le (hb 0) (hb 1) (hcb 0) (hcb 1)
  have haM : l2sq a≤Cζ^2*M :=
    l2sq_cutoff_comparison (smooth_laplacian hζ) hφ (hT.exp.mul hU) hcφ hCζ hζlap hφlap
  have hbM (i : Fin 2) : l2sq (b i)≤Cζ^2*l2sq (fun x => (Real.exp (T x)*θ x)*coordPartial U i x) := by
    have hh := l2sq_cutoff_comparison (smooth_partial hζ i) hθ
      (hT.exp.mul (smooth_partial hU i)) hcθ hCζ (hζg i) (hθ1 i)
    simpa only [b, mul_left_comm, mul_assoc, mul_comm] using hh
  have hcac := exponential_caccioppoli hθ hφ hT hU hp hcθ hcφ hφ1 hCp hCθ hCt
    hθb hθg hTb hpb hPDEθ
  have hh := mul_le_mul_of_nonneg_left hcac (sq_nonneg Cζ)
  have hb0 := hbM 0
  have hb1 := hbM 1
  simp only [Fin.sum_univ_two] at hh
  dsimp [M] at haM
  nlinarith only [hsum, hsum', haM, hb0, hb1, hh]

lemma cutoff_prefactor_bound {K D Cp Cζ Cθ Ct : ℝ}
    (hD : 1≤D) (hK : K^2≤D^2) (hCp : 0≤Cp) :
    Cζ^2*(2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*(Ct*D)^2*Cθ^2)) ≤
      (Cζ^2*(2+16*(2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2)))*D^2 := by
  have hDsq : 1≤D^2 := by nlinarith only [hD]
  have h1 := mul_le_mul_of_nonneg_right hK
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) hCp) (sq_nonneg Cθ))
  have h2 := mul_le_mul_of_nonneg_left hDsq (sq_nonneg Cθ)
  apply (mul_le_mul_of_nonneg_left (show
    2+16*(2*K^2*Cp*Cθ^2+16*Cθ^2+16*(Ct*D)^2*Cθ^2) ≤
    (2+16*(2*Cp*Cθ^2+16*Cθ^2+16*Ct^2*Cθ^2))*D^2 from by
      nlinarith only [h1, h2, hDsq]) (sq_nonneg Cζ)).trans_eq
  ring

lemma cancel_carleman_frequency {S D c C : ℝ} {f g : Plane → ℝ}
    (hS : 0≤S) (hD : 0<D) (hc : 0<c)
    (hcar : c*Real.sqrt S*D*l2norm f≤l2norm g)
    (herror : l2sq g≤C*D^2) : S*l2sq f≤C/c^2 := by
  have hleft : 0≤c*Real.sqrt S*D*l2norm f := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _)) hD.le)
      (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mpr hcar
  have heq : (c*Real.sqrt S*D*l2norm f)^2=c^2*S*D^2*l2sq f := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hS, l2norm_sq]
  change (c*Real.sqrt S*D*l2norm f)^2 ≤ (l2norm g)^2 at hsq
  rw [heq, l2norm_sq] at hsq
  have hh : (c^2*(S*l2sq f))*D^2≤C*D^2 := by nlinarith only [hsq, herror]
  have hh' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp hh
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith only [hh']

end Carleman
end SharpNodal

end

end OAI
