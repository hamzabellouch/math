import OAI.Geometry.Perimeter.Regularity.EllipticLocalExtension
import OAI.Geometry.Perimeter.Regularity.EllipticFamilyEstimate
import OAI.Geometry.Perimeter.Regularity.EllipticSecantBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 def quotientSteps (r : ℝ) (e : Euc n) (i : ℕ) : ℝ :=
  (r/(‖e‖+1))*(1/((i:ℝ)+1))

 theorem quotientSteps_pos {r : ℝ} (hr : 0<r) (e : Euc n) (i : ℕ) :
    0<quotientSteps r e i := by unfold quotientSteps; positivity

 theorem quotientSteps_shift_lt {r : ℝ} (hr : 0<r) (e : Euc n) (i : ℕ) :
    ‖quotientSteps r e i•e‖<r := by
  rw [norm_smul,Real.norm_of_nonneg (quotientSteps_pos hr e i).le]
  have hi : (1:ℝ)/((i:ℝ)+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simp
  have hh : quotientSteps r e i ≤ r/(‖e‖+1) := by
    unfold quotientSteps
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ r/(‖e‖+1))
  apply (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_lt
  have he : r/(‖e‖+1)*‖e‖<r := by
    rw [div_mul_eq_mul_div,div_lt_iff₀ (by positivity : 0<‖e‖+1)]
    nlinarith
  exact he

 theorem quotientSteps_tendsto {r : ℝ} (hr : 0<r) (e : Euc n) :
    Tendsto (quotientSteps r e) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun i : ℕ ↦ (r/(‖e‖+1))*(1/((i:ℝ)+1))) atTop (𝓝 0)
    simpa only [mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r/(‖e‖+1))
  · exact Eventually.of_forall (fun i ↦ (quotientSteps_pos hr e i).ne')

 theorem nonlinear_directional_gain {θ δ K : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {G : Euc n → Euc n} (hG : ContDiff ℝ 2 G)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (heq : WeakFluxEquation (fun x ↦ G (gradient f x)) U)
    (hmod : GeometricHolderAt θ (gradient f) p)
    (hnear : ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ G (gradient f p)‖ < min δ (1/2))
    (e : Euc n) :
    ∃ r : ℝ, 0<r ∧ Metric.ball p r⊆U ∧
      ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ f x e) (Metric.ball p r) ∧
      GeometricHolderAt θ (gradient (fun x ↦ fderiv ℝ f x e)) p := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hDG : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  obtain ⟨ρ,L,hρ,hL,hLip⟩ := contDiff_local_lipschitz hDG (gradient f p)
  have hcn : ContinuousAt (fun z ↦ ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ G z‖)
      (gradient f p) := (continuousAt_const.sub hDG.continuous.continuousAt).norm
  obtain ⟨τ,hτ,hτn⟩ := Metric.eventually_nhds_iff.mp (hcn.eventually (gt_mem_nhds hnear))
  let κ := min ρ τ
  have hκ : 0<κ := lt_min hρ hτ
  have hgc := gradient_continuous_C1 hf
  obtain ⟨s,hs,hsg⟩ := Metric.continuousAt_iff.mp hgc.continuousAt κ hκ
  obtain ⟨S,hS,hSU⟩ := Metric.isOpen_iff.mp hU p hp
  let a := 1/(32*K^2)
  have ha : 0<a := by dsimp [a]; positivity
  let ε := a/(2*(L+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨b,hb,hbs,hbm⟩ := hmod.shrink_amplitude hθ hε (lt_min hs hS)
  let r := b/8
  have hr : 0<r := by dsimp [r]; positivity
  have hrb : 5*r<b := by dsimp [r]; linarith
  have hbS : b ≤ S := hbs.trans (min_le_right _ _)
  have hbs' : b ≤ s := hbs.trans (min_le_left _ _)
  have him (x : Euc n) (hx : x∈Metric.ball p b) : gradient f x∈Metric.ball (gradient f p) κ :=
    Metric.mem_ball.mpr (hsg ((Metric.mem_ball.mp hx).trans_le hbs'))
  have hshift (i : ℕ) (R : ℝ) (x : Euc n) (hx : x∈Metric.ball p R) :
      x+quotientSteps r e i•e∈Metric.ball p (R+r) := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : x+quotientSteps r e i•e-p=(x-p)+quotientSteps r e i•e := by abel
    rw [he]
    have hh := norm_add_le (x-p) (quotientSteps r e i•e)
    have hd := Metric.mem_ball.mp hx
    rw [dist_eq_norm] at hd
    linarith [quotientSteps_shift_lt hr e i]
  let A : ℕ → Euc n → Euc n →L[ℝ] Euc n := fun i x ↦
    derivativeSecant G (gradient f x) (gradient f (x+quotientSteps r e i•e))
  let v : ℕ → Euc n → ℝ := fun i ↦ differenceQuotient f e (quotientSteps r e i)
  have hA (i : ℕ) : Continuous (A i) := (derivativeSecant_continuous hG1).comp
    (hgc.prodMk (hgc.comp (continuous_id.add continuous_const)))
  have hv (i : ℕ) : ContDiff ℝ 1 (v i) := differenceQuotient_contDiff hf e _
  have h4b : Metric.ball p (4*r)⊆Metric.ball p b := Metric.ball_subset_ball (by linarith)
  have h4U : Metric.ball p (4*r)⊆U := h4b.trans ((Metric.ball_subset_ball hbS).trans hSU)
  have hE (i : ℕ) : WeakLinearEquation (A i) (v i) (fun _ ↦ 0) (Metric.ball p (4*r)) :=
    weak_nonlinear_difference hG1 hf heq h4U e _ (fun x hx ↦
      hSU (Metric.ball_subset_ball (by linarith : 4*r+r ≤ S) (hshift i (4*r) x hx)))
  have hN (i : ℕ) (x : Euc n) (hx : x∈Metric.ball p (4*r)) :
      ‖ContinuousLinearMap.id ℝ (Euc n)-A i x‖ ≤ min δ (1/2) := by
    apply derivativeSecant_near hG1
    intro t ht
    have hh := segment_in_ball (him x (h4b hx))
      (him _ (Metric.ball_subset_ball (by linarith : 4*r+r ≤ b) (hshift i (4*r) x hx))) ht
    exact (hτn ((Metric.mem_ball.mp hh).trans_le (min_le_right _ _))).le
  have hosc (i : ℕ) (x : Euc n) (hx : x∈Metric.closedBall p r) (j : ℕ)
      (y : Euc n) (hy : y∈Metric.ball x (θ^j*r)) :
      ‖A i x-A i y‖ ≤ a*(1/2)^j ∧ ‖(0:Euc n)-0‖ ≤ (0:ℝ)*(1/2)^j := by
    have hj : θ^j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
    have hx2 : x∈Metric.ball p (2*r) := Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    have hy2 : y∈Metric.ball p (2*r) := by
      have hd := dist_triangle y x p
      have hdx := Metric.mem_closedBall.mp hx
      have hdy := Metric.mem_ball.mp hy
      have hrj := mul_le_mul_of_nonneg_right hj hr.le
      rw [Metric.mem_ball]
      linarith
    have h2b : Metric.ball p (2*r)⊆Metric.ball p b := Metric.ball_subset_ball (by linarith)
    have hx' : x+quotientSteps r e i•e∈Metric.ball p b :=
      Metric.ball_subset_ball (by linarith : 2*r+r ≤ b) (hshift i (2*r) x hx2)
    have hy' : y+quotientSteps r e i•e∈Metric.ball p b :=
      Metric.ball_subset_ball (by linarith : 2*r+r ≤ b) (hshift i (2*r) y hy2)
    have hd : dist x y ≤ θ^j*b := by
      rw [dist_comm]
      exact (Metric.mem_ball.mp hy).le.trans (mul_le_mul_of_nonneg_left (by dsimp [r]; linarith) (pow_nonneg hθ.le _))
    have hg₁ := hbm j x (h2b hx2) y (h2b hy2) hd
    have hg₂ := hbm j _ hx' _ hy' (by simpa only [dist_add_right] using hd)
    rw [dist_eq_norm] at hg₁ hg₂
    have he := derivativeSecant_lipschitz_ball hG1 hL
      (Metric.ball_subset_ball (min_le_left _ _) (him x (h2b hx2)))
      (Metric.ball_subset_ball (min_le_left _ _) (him _ hx'))
      (Metric.ball_subset_ball (min_le_left _ _) (him y (h2b hy2)))
      (Metric.ball_subset_ball (min_le_left _ _) (him _ hy')) hLip
    have hεeq : 2*(L+1)*ε=a := by dsimp [ε]; field_simp
    constructor
    · apply he.trans
      have hh := mul_le_mul_of_nonneg_left (add_le_add hg₁ hg₂) hL
      have hpos : 0 ≤ (1/2:ℝ)^j*ε := mul_nonneg (by positivity) hε.le
      nlinarith
    · simp
  obtain ⟨B₀,hB₀,hbound⟩ := compact_C1_gradient_bound hf hfc
  obtain ⟨hg,hgmod⟩ := linear_family_C1_limit hθ hθ1 hK hc ha.le (by norm_num : (0:ℝ) ≤ 0)
    hr (by dsimp [a]; field_simp; norm_num) hA hv (fun _ ↦ continuous_const) hE hN hosc
    (fun i x ↦ differenceQuotient_bound (hf.differentiable (by simp)) hB₀ hbound e _ x)
    (by intro i x; simp : ∀ i x, ‖(fun _ : Euc n ↦ (0:Euc n)) x‖ ≤ 0)
    (fun x _ ↦ (differenceQuotient_tendsto (hf.differentiable (by simp)) e x).comp (quotientSteps_tendsto hr e))
  exact ⟨r,hr,(Metric.ball_subset_ball (by linarith : r ≤ 4*r)).trans h4U,hg,hgmod⟩

end RPISingularHarnack

end

end OAI
