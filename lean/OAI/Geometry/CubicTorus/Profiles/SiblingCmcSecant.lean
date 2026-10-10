import Mathlib
import OAI.Geometry.CubicTorus.Profiles.SiblingPlaneCarlemanS

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeBentWeight_outside_ball {a x n y : Plane} {R ℓ : ℝ}
    (hR : 0 < R) (hn : ‖n‖=1) (hx : x-a=R • n) (hℓ : 0 < ℓ)
    (hy : R ≤ ‖y-a‖) (hsmall : ℓ*‖y-x‖ ≤ 1) :
    planeBentWeight x n ℓ (4/R) y ≤  -(‖y-x‖^2/R) := by
  let s : ℝ := ⟪n,y-x⟫
  let q : ℝ := ‖y-x‖^2
  have hsq : R^2 ≤ ‖y-a‖^2 := by nlinarith [norm_nonneg (y-a)]
  have hid : ‖y-a‖^2=q+2*R*s+R^2 := by
    have he : y-a=(y-x)+R • n := by rw [← hx]; abel
    rw [he,norm_add_sq_real,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hn,mul_one,
      real_inner_smul_right]
    have hi : ⟪y-x,n⟫=⟪n,y-x⟫ := real_inner_comm _ _
    rw [hi]
    dsimp [s,q]
    ring
  have hb : -(q/(2*R)) ≤ s := by
    rw [← neg_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
    linarith
  have hsabs : |s| ≤ ‖y-x‖ := by
    simpa only [s,hn,one_mul] using abs_real_inner_le_norm n (y-x)
  have hls : ℓ*|s| ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hsabs hℓ.le) hsmall
  have hq : 0 ≤ q := sq_nonneg _
  rw [planeBentWeight_formula]
  change -s+(ℓ/2)*s^2-((4/R)/2)*q ≤  -(q/R)
  have hden : 0 < R := hR
  have hqr : 0 ≤ q/R := div_nonneg hq hR.le
  have hfour : (4/R)/2=2/R := by ring
  rw [hfour]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs] at hls
    have hh := mul_le_mul_of_nonneg_right hls hs
    have he : (2/R)*q=2*(q/R) := by ring
    rw [he]
    nlinarith
  · have hs' : s < 0 := lt_of_not_ge hs
    rw [abs_of_neg hs'] at hls
    have hh := mul_le_mul_of_nonneg_right hls (neg_nonneg.mpr hs'.le)
    have he : (2/R)*q=2*(q/R) := by ring
    have he' : q/(2*R)=(q/R)/2 := by ring
    rw [he'] at hb
    rw [he]
    nlinarith

lemma planeBentWeight_lower_near (x n : Plane) (ℓ M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ,0 < r ∧ ∀ y∈Metric.ball x r,-δ ≤ planeBentWeight x n ℓ M y := by
  have hh : ∀ᶠ y in 𝓝 x,-δ ≤ planeBentWeight x n ℓ M y :=
    ((planeBentWeight_contDiff x n ℓ M).continuous.continuousAt.eventually
      (lt_mem_nhds (by rw [planeBentWeight_center]; linarith :
        -δ < planeBentWeight x n ℓ M x))).mono (fun _ h ↦ h.le)
  obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp hh
  exact ⟨r,hr,fun y hy ↦ hh (Metric.mem_ball.mp hy)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_square_integrable {f : Plane → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun y ↦ (f y)^2) := by
  have hf2 : Continuous (fun y ↦ (f y)^2) := hf.pow 2
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by norm_num)
  exact hf2.integrable_of_hasCompactSupport hc2

lemma weighted_square_integrable {φ f : Plane → ℝ} (hφ : Continuous φ)
    (hf : Continuous f) (hc : HasCompactSupport f) (τ : ℝ) :
    Integrable (fun y ↦ (Real.exp (τ*φ y)*f y)^2) := by
  have hw : Continuous (fun y ↦ Real.exp (τ*φ y)*f y) :=
    (Real.continuous_exp.comp (continuous_const.mul hφ)).mul hf
  exact continuous_square_integrable hw hc.mul_left

lemma weighted_square_lower {φ f : Plane → ℝ} {W : Set Plane} {c τ : ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hW : MeasurableSet W) (ht : 0 ≤ τ) (hl : ∀ y∈W,c ≤ φ y) :
    (Real.exp (τ*c))^2*(∫ y in W,(f y)^2) ≤ ∫ y,(Real.exp (τ*φ y)*f y)^2 := by
  have hi : Integrable (fun y ↦ (f y)^2) :=
    continuous_square_integrable hf hc
  have hw := weighted_square_integrable hφ hf hc τ
  calc
    _=∫ y in W,(Real.exp (τ*c))^2*(f y)^2 := (integral_const_mul _ _).symm
    _≤∫ y in W,(Real.exp (τ*φ y)*f y)^2 := by
      apply integral_mono_ae ((hi.const_mul _).integrableOn) hw.integrableOn
      apply (ae_restrict_iff' hW).mpr
      exact ae_of_all _ (fun y hy ↦ by
        dsimp only
        rw [mul_pow]
        gcongr
        exact hl y hy)
    _≤_ := setIntegral_le_integral hw (ae_of_all _ (fun y ↦ sq_nonneg _))

lemma weighted_square_upper {φ e : Plane → ℝ} {c τ : ℝ}
    (hφ : Continuous φ) (he : Continuous e) (hc : HasCompactSupport e)
    (ht : 0 ≤ τ) (hb : ∀ y,e y≠0 → φ y ≤ c) :
    (∫ y,(Real.exp (τ*φ y)*e y)^2) ≤ (Real.exp (τ*c))^2*(∫ y,(e y)^2) := by
  have hi : Integrable (fun y ↦ (e y)^2) :=
    continuous_square_integrable he hc
  rw [← integral_const_mul]
  apply integral_mono (weighted_square_integrable hφ he hc τ) (hi.const_mul _)
  intro y
  by_cases hy : e y=0
  · simp [hy]
  · dsimp only
    rw [mul_pow]
    gcongr
    exact hb y hy

lemma carleman_polynomial_mass_zero {J E T : ℝ} (hJ : 0 ≤ J)
    (hbound : ∀ τ : ℝ,max 1 T ≤ τ → τ^3*J ≤ E) : J=0 := by
  by_contra hn
  have hp : 0 < J := lt_of_le_of_ne hJ (Ne.symm hn)
  let τ := max (max 1 T) (E/J+1)
  have hτ : max 1 T ≤ τ := le_max_left _ _
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτE : E/J+1 ≤ τ := le_max_right _ _
  have hcube : τ ≤ τ^3 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hτ1) (by linarith : 0 ≤ τ+1)
    have h2 := mul_nonneg h1 (by linarith : 0 ≤ τ)
    nlinarith only [h2]
  have hb := hbound τ hτ
  have hmul := mul_le_mul_of_nonneg_right hcube hJ
  have hfinal := mul_le_mul_of_nonneg_right hτE hJ
  have heq : (E/J+1)*J=E+J := by field_simp
  rw [heq] at hfinal
  linarith

theorem carleman_zero_on_open {φ f e : Plane → ℝ} {W : Set Plane} {c T : ℝ}
    (hφ : Continuous φ) (hf : Continuous f) (he : Continuous e)
    (hfc : HasCompactSupport f) (hec : HasCompactSupport e) (hW : IsOpen W)
    (hl : ∀ y∈W,c ≤ φ y) (hb : ∀ y,e y≠0 → φ y ≤ c)
    (hest : ∀ τ : ℝ,T ≤ τ →
      τ^3*(∫ y,(Real.exp (τ*φ y)*f y)^2) ≤ ∫ y,(Real.exp (τ*φ y)*e y)^2) :
    ∀ y∈W,f y=0 := by
  let J := ∫ y in W,(f y)^2
  let E := ∫ y,(e y)^2
  have hJ : 0 ≤ J := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hz : J=0 := carleman_polynomial_mass_zero hJ (T := T) (by
    intro τ hτ
    have ht : 0 ≤ τ := le_trans (by norm_num) ((le_max_left _ _).trans hτ)
    have hlw := weighted_square_lower hφ hf hfc hW.measurableSet ht hl
    have huw := weighted_square_upper hφ he hec ht hb
    have hh := hest τ ((le_max_right _ _).trans hτ)
    have hm := mul_le_mul_of_nonneg_left hlw (pow_nonneg ht 3)
    have hpos : 0 < (Real.exp (τ*c))^2 := sq_pos_of_pos (Real.exp_pos _)
    apply (mul_le_mul_iff_right₀ hpos).mp
    change (Real.exp (τ*c))^2*(τ^3*J) ≤ (Real.exp (τ*c))^2*E
    nlinarith only [hm,hh,huw])
  have hi : Integrable (fun y ↦ (f y)^2) := continuous_square_integrable hf hfc
  have hae : (fun y ↦ (f y)^2)=ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _ ↦ sq_nonneg _)) hi.integrableOn).mp hz
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hW
    (hf.pow 2).continuousOn continuousOn_const
  intro y hy
  have hh := heq hy
  simpa only [Pi.zero_apply,pow_eq_zero_iff (by norm_num : (2 : ℕ)≠0)] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeElliptic_germ {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    {y : Plane} (he : f=ᶠ[𝓝 y] g) : sibling_planeElliptic A f y=sibling_planeElliptic A g y := by
  have hp : (fun z ↦ A z (gradient f z))=ᶠ[𝓝 y] (fun z ↦ A z (gradient g z)) :=
    he.gradient.mono (fun z hz ↦ congrArg (A z) hz)
  simp only [sibling_planeElliptic,planeDivergence,hp.fderiv_eq]

lemma sibling_planeElliptic_zero (A : Plane → Plane →L[ℝ] Plane) (y : Plane) :
    sibling_planeElliptic A (fun _ ↦ 0) y=0 := by
  simp [sibling_planeElliptic,planeDivergence,gradient_fun_const]

lemma planeElliptic_zero_on {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    {O : Set Plane} (hO : IsOpen O) (hz : ∀ z∈O,f z=0) {y : Plane} (hy : y∈O) :
    sibling_planeElliptic A f y=0 := by
  have he : f=ᶠ[𝓝 y] (fun _ ↦ 0) := by
    filter_upwards [hO.mem_nhds hy] with z h
    exact hz z h
  rw [planeElliptic_germ he,sibling_planeElliptic_zero]

lemma planeElliptic_support {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ} :
    tsupport (sibling_planeElliptic A f)⊆tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hn
  have he0 : f=ᶠ[𝓝 y] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  have he := planeElliptic_germ (A := A) he0
  simp only [sibling_planeElliptic_zero] at he
  exact hy he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeBumpCutoff_eq {x : Plane} (b : ContDiffBump x) (u : Plane → ℝ)
    {y : Plane} (hy : y∈Metric.closedBall x b.rIn) : b y*u y=u y := by
  rw [b.one_of_mem_closedBall hy,one_mul]

lemma planeBumpCutoff_germ {x : Plane} (b : ContDiffBump x) (u : Plane → ℝ)
    {y : Plane} (hy : y∈Metric.ball x b.rIn) : (fun z ↦ b z*u z)=ᶠ[𝓝 y] u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
  exact planeBumpCutoff_eq b u (Metric.ball_subset_closedBall hz)

lemma planeBumpCutoff_error {A : Plane → Plane →L[ℝ] Plane} {x : Plane}
    (b : ContDiffBump x) (u : Plane → ℝ) {O : Set Plane} (hO : IsOpen O)
    (hz : ∀ z∈O,u z=0) (hLu : ∀ z∈Metric.ball x b.rIn,sibling_planeElliptic A u z=0)
    {y : Plane} (hy : sibling_planeElliptic A (fun z ↦ b z*u z) y≠0) :
    y∈Metric.closedBall x b.rOut ∧ y∉Metric.ball x b.rIn ∧ y∉O := by
  have hs : y∈tsupport (sibling_planeElliptic A (fun z ↦ b z*u z)) := subset_closure hy
  have hbs : y∈tsupport (fun z ↦ b z*u z) := planeElliptic_support hs
  refine ⟨?_,?_,?_⟩
  · have hh : y∈tsupport (b : Plane → ℝ) := tsupport_mul_subset_left hbs
    simpa only [b.tsupport_eq] using hh
  · intro hh
    apply hy
    rw [planeElliptic_germ (planeBumpCutoff_germ b u hh)]
    exact hLu y hh
  · intro hh
    apply hy
    exact planeElliptic_zero_on hO (fun z h ↦ by rw [hz z h,mul_zero]) hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_elliptic_zero_ball_extension {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ z v w,⟪v,A z w⟫=⟪w,A z v⟫)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {a x n : Plane} {R m s : ℝ} (hR : 0 < R) (hn : ‖n‖=1)
    (hx : x-a=R • n) (hm : 0 < m) (hs : 0 < s)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫)
    (hLu : ∀ y∈Metric.ball x s,sibling_planeElliptic A u y=0)
    (hzero : ∀ y∈Metric.ball a R,u y=0) :
    ∃ r : ℝ,0 < r ∧ ∀ y∈Metric.ball x r,u y=0 := by
  obtain ⟨ℓ,hℓ,T,r,hr,hcar⟩ := plane_weighted_carleman_near hA hAs x n hn hm hco
    (4/R) (by positivity)
  let ρ : ℝ := min (min (r/2) (s/2)) (1/(2*ℓ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r := (min_le_left _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith : r/2 < r))
  have hρs : ρ < s := (min_le_left _ _).trans_lt
    ((min_le_right _ _).trans_lt (by linarith : s/2 < s))
  have hρℓ : ℓ*ρ ≤ 1 := by
    have hh : ρ ≤ 1/(2*ℓ) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*ℓ)).mp hh
    have hlp : 0 ≤ ℓ*ρ := mul_nonneg hℓ.le hρ.le
    nlinarith
  let b : ContDiffBump x :=
    { rIn := ρ/2
      rOut := ρ
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let f : Plane → ℝ := fun y ↦ b y*u y
  let φ := planeBentWeight x n ℓ (4/R)
  let e := sibling_planeElliptic A f
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul hu
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_right
  have hfs : tsupport f⊆Metric.ball x r := by
    apply tsupport_mul_subset_left.trans
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hρr
  have he : ContDiff ℝ (⊤ : ℕ∞) e := sibling_planeElliptic_contDiff hA hf
  have hec : HasCompactSupport e := sibling_planeElliptic_compact hfc
  let δ : ℝ := (ρ/2)^2/R
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (by positivity)) hR
  have heb : ∀ y,e y≠0 → φ y ≤ -δ := by
    intro y hy
    obtain ⟨hyc,hyi,hyo⟩ := planeBumpCutoff_error b u Metric.isOpen_ball hzero
      (fun z hz ↦ hLu z ((Metric.ball_subset_ball (by dsimp [b]; linarith : b.rIn ≤ s)) hz)) hy
    have hyn : ‖y-x‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm,b] using hyc
    have hyi' : ρ/2 ≤ ‖y-x‖ := by
      simpa only [Metric.mem_ball,dist_eq_norm,b,not_lt] using hyi
    have hyo' : R ≤ ‖y-a‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hyo
    have hsmall : ℓ*‖y-x‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hyn hℓ.le).trans hρℓ
    have hbd := planeBentWeight_outside_ball hR hn hx hℓ hyo' hsmall
    have hq : δ ≤ ‖y-x‖^2/R := by
      dsimp [δ]
      gcongr
    exact hbd.trans (neg_le_neg hq)
  obtain ⟨r₁,hr₁,hlower⟩ := planeBentWeight_lower_near x n ℓ (4/R) hδ
  let r₂ := min r₁ (ρ/2)
  have hr₂ : 0 < r₂ := lt_min hr₁ (by positivity)
  have hz : ∀ y∈Metric.ball x r₂,f y=0 := carleman_zero_on_open
    (planeBentWeight_contDiff x n ℓ (4/R)).continuous hf.continuous he.continuous hfc hec
    Metric.isOpen_ball
    (fun y hy ↦ hlower y ((Metric.ball_subset_ball (min_le_left _ _)) hy)) heb
    (fun τ hτ ↦ hcar f hf hfc hfs τ hτ)
  refine ⟨r₂,hr₂,?_⟩
  intro y hy
  have hb1 : y∈Metric.closedBall x b.rIn :=
    Metric.ball_subset_closedBall ((Metric.ball_subset_ball (min_le_right r₁ (ρ/2))) hy)
  have heq := planeBumpCutoff_eq b u hb1
  exact heq.symm.trans (hz y hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_interior_tangent_ball {O : Set Plane} (hO : IsOpen O)
    (hcl : (0 : Plane)∈closure O) (hzero : (0 : Plane)∉O)
    {s : ℝ} (hs : 0<s) :
    ∃ a x : Plane,∃ R : ℝ,0<R ∧ ‖x-a‖=R ∧ x∈closure O ∧ x∉O ∧
      Metric.ball a R⊆O ∧ Metric.closedBall a R⊆Metric.ball 0 s := by
  obtain ⟨a,ha,han⟩ := Metric.mem_closure_iff.mp hcl (s/4) (by positivity)
  have hnc : Oᶜ.Nonempty := ⟨0,hzero⟩
  let R := Metric.infDist a Oᶜ
  have hR : 0<R := (hO.isClosed_compl.notMem_iff_infDist_pos hnc).mp (not_not.mpr ha)
  have hRa : R≤‖a‖ := by
    simpa only [dist_zero_right] using (Metric.infDist_le_dist_of_mem (x := a) (show (0 : Plane)∈Oᶜ from hzero))
  have haN : ‖a‖<s/4 := by simpa only [dist_zero_left] using han
  obtain ⟨x,hx,hRx⟩ := hO.isClosed_compl.exists_infDist_eq_dist hnc a
  have hxR : ‖x-a‖=R := by simpa only [R,dist_comm a x,dist_eq_norm] using hRx.symm
  have hball : Metric.ball a R⊆O := Metric.ball_infDist_compl_subset
  have hxcl : x∈closure O := by
    apply closure_mono hball
    rw [closure_ball a hR.ne']
    simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]
  refine ⟨a,x,R,hR,hxR,hxcl,hx,hball,?_⟩
  intro y hy
  have hyn : ‖y-a‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hnorm : ‖y‖≤‖y-a‖+‖a‖ := by simpa only [sub_add_cancel] using norm_add_le (y-a) a
  simp only [Metric.mem_ball,dist_zero_right]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_interior_tangent_ball_at {O : Set Plane} (hO : IsOpen O)
    {z : Plane} (hcl : z∈closure O) (hzero : z∉O) {s : ℝ} (hs : 0 < s) :
    ∃ a x : Plane,∃ R : ℝ,0 < R ∧ ‖x-a‖=R ∧ x∈closure O ∧ x∉O ∧
      Metric.ball a R⊆O ∧ Metric.closedBall a R⊆Metric.ball z s := by
  obtain ⟨a,ha,han⟩ := Metric.mem_closure_iff.mp hcl (s/4) (by positivity)
  have hnc : Oᶜ.Nonempty := ⟨z,hzero⟩
  let R := Metric.infDist a Oᶜ
  have hR : 0 < R := (hO.isClosed_compl.notMem_iff_infDist_pos hnc).mp (not_not.mpr ha)
  have hRa : R ≤ dist a z := Metric.infDist_le_dist_of_mem hzero
  have haN : dist a z < s/4 := by simpa only [dist_comm z a] using han
  obtain ⟨x,hx,hRx⟩ := hO.isClosed_compl.exists_infDist_eq_dist hnc a
  have hxR : ‖x-a‖=R := by simpa only [R,dist_comm a x,dist_eq_norm] using hRx.symm
  have hball : Metric.ball a R⊆O := Metric.ball_infDist_compl_subset
  have hxcl : x∈closure O := by
    apply closure_mono hball
    rw [closure_ball a hR.ne']
    simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]
  refine ⟨a,x,R,hR,hxR,hxcl,hx,hball,?_⟩
  intro y hy
  have hyn : dist y a ≤ R := hy
  have htri := dist_triangle y a z
  change dist y z < s
  linarith

theorem plane_elliptic_unique_continuation {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ z v w,⟪v,A z w⟫=⟪w,A z v⟫)
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hpos : ∀ x∈Ω,∃ m : ℝ,0 < m ∧ ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫)
    (hLu : ∀ x∈Ω,sibling_planeElliptic A u x=0)
    (hzero : (Ω∩interior {x | u x=0}).Nonempty) : ∀ x∈Ω,u x=0 := by
  let O := Ω∩interior {x | u x=0}
  have hO : IsOpen O := hΩ.inter isOpen_interior
  have hsub : Ω⊆O := hc.subset_of_closure_inter_subset hO
    (by rcases hzero with ⟨x,hx⟩; exact ⟨x,hx.1,hx⟩) (by
      rintro z ⟨hzcl,hzΩ⟩
      by_contra hzO
      obtain ⟨s,hs,hsΩ⟩ := Metric.isOpen_iff.mp hΩ z hzΩ
      obtain ⟨a,x,R,hR,hxR,hxcl,hxO,hball,hclosed⟩ :=
        plane_interior_tangent_ball_at hO hzcl hzO hs
      have hxΩ : x∈Ω := hsΩ (hclosed (by
        simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]))
      obtain ⟨s₁,hs₁,hs₁Ω⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
      obtain ⟨m,hm,hco⟩ := hpos x hxΩ
      let n : Plane := R⁻¹ • (x-a)
      have hn : ‖n‖=1 := by simp only [n,norm_smul,Real.norm_eq_abs,abs_inv,
        abs_of_pos hR,hxR,inv_mul_cancel₀ hR.ne']
      have hxn : x-a=R • n := by simp only [n,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
      obtain ⟨r,hr,huz⟩ := plane_elliptic_zero_ball_extension hA hAs hu hR hn hxn hm hs₁
        hco (fun y hy ↦ hLu y (hs₁Ω hy)) (fun y hy ↦ show y∈{z | u z=0} from interior_subset (hball hy).2)
      apply hxO
      refine ⟨hxΩ,?_⟩
      exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
        (Metric.ball_mem_nhds x hr) huz))
  intro x hx
  exact show x∈{z | u z=0} from interior_subset (hsub hx).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_cmcSecant (p q : Plane) : Plane →L[ℝ] Plane :=
  (2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))⁻¹ •
    ((cmcWeight p+cmcWeight q)^2 • ContinuousLinearMap.id ℝ Plane -
      (innerSL ℝ (p+q)).smulRight (p+q))

lemma sibling_cmcSecant_apply (p q v : Plane) :
    sibling_cmcSecant p q v=(2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q))⁻¹ •
      ((cmcWeight p+cmcWeight q)^2 • v-⟪p+q,v⟫ • (p+q)) := by
  simp only [sibling_cmcSecant,smul_apply,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]

lemma sibling_cmcSecant_symmetric (p q v w : Plane) :
    ⟪v,sibling_cmcSecant p q w⟫=⟪w,sibling_cmcSecant p q v⟫ := by
  simp only [sibling_cmcSecant_apply,inner_smul_right,inner_sub_right]
  rw [real_inner_comm v w,real_inner_comm v (p+q),real_inner_comm w (p+q)]
  ring

lemma cmcSecant_self (p q v : Plane) :
    ⟪v,sibling_cmcSecant p q v⟫=
      ((cmcWeight p+cmcWeight q)^2*‖v‖^2-⟪p+q,v⟫^2)/
        (2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q)) := by
  simp only [sibling_cmcSecant_apply,inner_smul_right,inner_sub_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm v (p+q)]
  ring

lemma cmcSecant_positive (p q : Plane) :
    ∃ m : ℝ,0 < m ∧ ∀ v : Plane,m*‖v‖^2 ≤ ⟪v,sibling_cmcSecant p q v⟫ := by
  have hp := cmcWeight_pos p
  have hq := cmcWeight_pos q
  have hpn : ‖p‖ < cmcWeight p := by nlinarith [cmcWeight_sq p,norm_nonneg p]
  have hqn : ‖q‖ < cmcWeight q := by nlinarith [cmcWeight_sq q,norm_nonneg q]
  have hn : ‖p+q‖ < cmcWeight p+cmcWeight q :=
    (norm_add_le p q).trans_lt (add_lt_add hpn hqn)
  let D := 2*cmcWeight p*cmcWeight q*(cmcWeight p+cmcWeight q)
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < (cmcWeight p+cmcWeight q)^2-‖p+q‖^2 := by
    nlinarith [norm_nonneg (p+q)]
  refine ⟨((cmcWeight p+cmcWeight q)^2-‖p+q‖^2)/D,div_pos hd hD,?_⟩
  intro v
  rw [cmcSecant_self,div_mul_eq_mul_div,div_le_div_iff_of_pos_right hD]
  have hcs := real_inner_mul_inner_self_le (p+q) v
  simp only [real_inner_self_eq_norm_sq] at hcs
  nlinarith only [hcs]

lemma cmcSecant_flux_difference (p q : Plane) :
    sibling_cmcSecant p q (p-q)=cmcFlux p-cmcFlux q := by
  have hp := (cmcWeight_pos p).ne'
  have hq := (cmcWeight_pos q).ne'
  have hpq : cmcWeight p+cmcWeight q≠0 := (add_pos (cmcWeight_pos p) (cmcWeight_pos q)).ne'
  have hi : ⟪p+q,p-q⟫=(cmcWeight p)^2-(cmcWeight q)^2 := by
    rw [inner_add_left,inner_sub_right,inner_sub_right,real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq,real_inner_comm q p,cmcWeight_sq,cmcWeight_sq]
    ring
  rw [sibling_cmcSecant_apply,hi]
  change _=(cmcWeight p)⁻¹ • p-(cmcWeight q)⁻¹ • q
  ext i
  simp only [PiLp.smul_apply,PiLp.sub_apply,PiLp.add_apply,smul_eq_mul]
  field_simp
  ring

lemma sibling_cmcSecant_contDiff {p q : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ sibling_cmcSecant (p y) (q y)) := by
  have hwp := cmcWeight_contDiff.comp hp
  have hwq := cmcWeight_contDiff.comp hq
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦
      2*cmcWeight (p y)*cmcWeight (q y)*(cmcWeight (p y)+cmcWeight (q y))) :=
    ((contDiff_const.mul hwp).mul hwq).mul (hwp.add hwq)
  have hDn : ∀ y,2*cmcWeight (p y)*cmcWeight (q y)*
      (cmcWeight (p y)+cmcWeight (q y))≠0 := by
    intro y
    exact (mul_pos (mul_pos (mul_pos (by norm_num) (cmcWeight_pos _)) (cmcWeight_pos _))
      (add_pos (cmcWeight_pos _) (cmcWeight_pos _))).ne'
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ innerSL ℝ (p y+q y)) :=
    (innerSL ℝ).contDiff.comp (hp.add hq)
  exact (hD.inv hDn).smul (((hwp.add hwq).pow 2).smul contDiff_const |>.sub
    (hinner.smulRight (hp.add hq)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCMC (g : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun y ↦ cmcFlux (gradient g y))

lemma sibling_planeDivergence_sub {F G : Plane → Plane} {x : Plane}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    planeDivergence (fun y ↦ F y-G y) x=planeDivergence F x-planeDivergence G x := by
  simp only [planeDivergence,fderiv_fun_sub hF hG,sub_apply,PiLp.sub_apply]
  ring

lemma planeCMC_germ {g h : Plane → ℝ} {x : Plane} (he : g=ᶠ[𝓝 x] h) :
    planeCMC g x=planeCMC h x := by
  have he' : (fun y ↦ cmcFlux (gradient g y))=ᶠ[𝓝 x] (fun y ↦ cmcFlux (gradient h y)) :=
    he.gradient.mono (fun _ hy ↦ congrArg cmcFlux hy)
  simp only [planeCMC,planeDivergence,he'.fderiv_eq]

lemma cmcSecant_equation {g h : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x : Plane) :
    sibling_planeElliptic (fun y ↦ sibling_cmcSecant (gradient g y) (gradient h y)) (g-h) x=
      planeCMC g x-planeCMC h x := by
  unfold sibling_planeElliptic
  have he : (fun y ↦ sibling_cmcSecant (gradient g y) (gradient h y) (gradient (g-h) y))=
      fun y ↦ cmcFlux (gradient g y)-cmcFlux (gradient h y) := by
    funext y
    rw [C1_gradient_sub (hg.of_le (by simp)) (hh.of_le (by simp)),Pi.sub_apply,
      cmcSecant_flux_difference]
  rw [he]
  exact sibling_planeDivergence_sub
    ((cmcFlux_contDiff.comp (plane_gradient_contDiff hg)).differentiable (by simp) x)
    ((cmcFlux_contDiff.comp (plane_gradient_contDiff hh)).differentiable (by simp) x)

theorem smooth_CMC_graph_coincidence {g h : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hcmc : ∀ x∈Ω,planeCMC g x=planeCMC h x)
    (he : (Ω∩interior {x | g x=h x}).Nonempty) : ∀ x∈Ω,g x=h x := by
  have hA := sibling_cmcSecant_contDiff (plane_gradient_contDiff hg) (plane_gradient_contDiff hh)
  have hzero : (Ω∩interior {x | (g-h) x=0}).Nonempty := by
    simpa only [Pi.sub_apply,sub_eq_zero] using he
  have hz := plane_elliptic_unique_continuation hA
    (fun x v w ↦ sibling_cmcSecant_symmetric _ _ v w) (hg.sub hh) hΩ hc
    (fun x _ ↦ cmcSecant_positive _ _) (fun x hx ↦ by
      change sibling_planeElliptic (fun y ↦ sibling_cmcSecant (gradient g y) (gradient h y)) (g-h) x=0
      rw [cmcSecant_equation hg hh,hcmc x hx,sub_self]) hzero
  intro x hx
  exact sub_eq_zero.mp (hz x hx)

lemma plane_local_smooth_extension {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Plane → F} {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {x : Plane} (hx : x∈Ω) :
    ∃ (G : Plane → F) (r : ℝ),0 < r ∧ Metric.ball x r⊆Ω ∧
      ContDiff ℝ (⊤ : ℕ∞) G ∧ EqOn G g (Metric.ball x r) := by
  obtain ⟨s,hs,hsΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  let b : ContDiffBump x := ⟨s/4,s/2,by positivity,by linarith⟩
  have hts : tsupport (b : Plane → ℝ)⊆Ω := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [b]; linarith : b.rOut < s)).trans hsΩ
  refine ⟨fun y ↦ b y • g y,s/4,by positivity,
    (Metric.ball_subset_ball (by linarith : s/4 ≤ s)).trans hsΩ,
    contDiff_local_vector_cutoff hΩ hg b.contDiff hts,?_⟩
  intro y hy
  dsimp only
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]

theorem CMC_graph_coincidence {g h : Plane → ℝ} {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Ω)
    (hcmc : ∀ x∈Ω,planeCMC g x=planeCMC h x)
    (he : (Ω∩interior {x | g x=h x}).Nonempty) : ∀ x∈Ω,g x=h x := by
  let O := Ω∩interior {x | g x=h x}
  have hO : IsOpen O := hΩ.inter isOpen_interior
  have hsub : Ω⊆O := hc.subset_of_closure_inter_subset hO
    (by rcases he with ⟨x,hx⟩; exact ⟨x,hx.1,hx⟩) (by
      rintro x ⟨hxcl,hxΩ⟩
      obtain ⟨G,r₁,hr₁,hr₁Ω,hG,hGg⟩ := plane_local_smooth_extension hΩ hg hxΩ
      obtain ⟨H,r₂,hr₂,hr₂Ω,hH,hHh⟩ := plane_local_smooth_extension hΩ hh hxΩ
      let r := min r₁ r₂
      have hr : 0 < r := lt_min hr₁ hr₂
      have hr1 : Metric.ball x r⊆Metric.ball x r₁ := Metric.ball_subset_ball (min_le_left _ _)
      have hr2 : Metric.ball x r⊆Metric.ball x r₂ := Metric.ball_subset_ball (min_le_right _ _)
      have heG : ∀ y∈Metric.ball x r,G=ᶠ[𝓝 y] g := fun y hy ↦
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (hr1 hy)) hGg
      have heH : ∀ y∈Metric.ball x r,H=ᶠ[𝓝 y] h := fun y hy ↦
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (hr2 hy)) hHh
      have heq : ∀ y∈Metric.ball x r,G y=H y := smooth_CMC_graph_coincidence hG hH
        Metric.isOpen_ball (convex_ball x r).isPreconnected (fun y hy ↦ by
          rw [planeCMC_germ (heG y hy),planeCMC_germ (heH y hy)]
          exact hcmc y (hr₁Ω (hr1 hy))) (by
          obtain ⟨y,hyO,hyx⟩ := Metric.mem_closure_iff.mp hxcl r hr
          have hy : y∈Metric.ball x r := by simpa only [Metric.mem_ball,dist_comm x y] using hyx
          refine ⟨y,hy,mem_interior_iff_mem_nhds.mpr ?_⟩
          filter_upwards [heG y hy,heH y hy,hO.mem_nhds hyO] with z hzG hzH hzO
          rw [hzG,hzH]
          exact show z∈{z | g z=h z} from interior_subset hzO.2)
      refine ⟨hxΩ,mem_interior_iff_mem_nhds.mpr ?_⟩
      filter_upwards [Metric.ball_mem_nhds x hr] with y hy
      exact (hGg (hr1 hy)).symm.trans ((heq y hy).trans (hHh (hr2 hy))))
  intro x hx
  exact show x∈{z | g z=h z} from interior_subset (hsub hx).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_tangent_normal {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    ⟪graphSlopeNormal n (gradient g y),fderiv ℝ (normalGraph n g) y v⟫=0 := by
  rw [graphSlopeNormal_weight hn,normalGraph_fderiv_apply hg,real_inner_smul_left]
  have he := (normalPlaneLinearIsometry n).inner_map_map (gradient g y) v
  change ⟪normalPlaneEmbedding n (gradient g y),normalPlaneEmbedding n v⟫=⟪gradient g y,v⟫ at he
  have ho : ⟪normalPlaneEmbedding n (gradient g y),n⟫=0 := by
    rw [real_inner_comm]; exact normalPlaneEmbedding_inner hn _
  simp only [inner_sub_left,inner_add_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,he,mul_one,
    ho,mul_zero]
  ring

lemma graph_projection_injective {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Plane}
    (ht : ⟪graphSlopeNormal n (gradient g y),m⟫≠0) :
    Function.Injective ((normalPlaneCoordinates m).comp (fderiv ℝ (normalGraph n g) y)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let w := fderiv ℝ (normalGraph n g) y v
  have hw : w=⟪m,w⟫ • m := by
    have hr := normalPlaneCoordinates_reconstruct hm w
    change normalPlaneCoordinates m w=0 at hv
    rw [hv] at hr
    change (normalPlaneLinearIsometry m) 0+⟪m,w⟫ • m=w at hr
    simpa only [map_zero,zero_add] using hr.symm
  have ho := normalGraph_tangent_normal hn hg y v
  change ⟪graphSlopeNormal n (gradient g y),w⟫=0 at ho
  rw [hw,real_inner_smul_right] at ho
  have hz : w=0 := by rw [hw,(mul_eq_zero.mp ho).resolve_right ht,zero_smul]
  have hh := congrArg (normalPlaneCoordinates n) hz
  dsimp [w] at hh
  rw [normalGraph_fderiv_apply hg,map_add,map_smul,normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn,smul_zero,add_zero,map_zero] at hh
  exact hh

def graphProjectionEquiv {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Plane}
    (ht : ⟪graphSlopeNormal n (gradient g y),m⟫≠0) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.ofBijective (((normalPlaneCoordinates m).comp
    (fderiv ℝ (normalGraph n g) y)).toLinearMap)
      ⟨graph_projection_injective hn hm hg ht,
        (LinearMap.injective_iff_surjective).mp (graph_projection_injective hn hm hg ht)⟩).toContinuousLinearEquiv

lemma graphProjectionEquiv_coe {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : Plane}
    (ht : ⟪graphSlopeNormal n (gradient g y),m⟫≠0) :
    (graphProjectionEquiv hn hm hg ht : Plane →L[ℝ] Plane)=
      (normalPlaneCoordinates m).comp (fderiv ℝ (normalGraph n g) y) := rfl

lemma normalGraph_contDiff {n : Cover} {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (normalGraph n g) :=
  (normalPlaneLinearIsometry n).toContinuousLinearMap.contDiff.add (hg.smul_const n)

theorem sibling_normalGraph_regraph {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : g 0=0)
    (ht : ⟪graphSlopeNormal n (gradient g 0),m⟫≠0) :
    ∃ (h : Plane → ℝ) (I : Plane → Plane),ContDiff ℝ (⊤ : ℕ∞) h ∧ h 0=0 ∧
      ContinuousAt I 0 ∧ I 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),normalGraph m h y=normalGraph n g (I y)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),
        (normalGraph m h (normalPlaneCoordinates m v)=v ↔
          normalGraph n g (normalPlaneCoordinates n v)=v) := by
  let G := normalGraph n g
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := normalGraph_contDiff hg
  have hG0 : G 0=0 := by
    change (normalPlaneLinearIsometry n) 0+g 0 • n=0
    rw [map_zero,hg0,zero_smul,add_zero]
  let F : Plane → Plane := fun y ↦ normalPlaneCoordinates m (G y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (normalPlaneCoordinates m).contDiff.comp hG
  have hF0 : F 0=0 := by simp [F,hG0]
  have hdF (y : Plane) : HasFDerivAt F
      ((normalPlaneCoordinates m).comp (fderiv ℝ G y)) y :=
    (normalPlaneCoordinates m).hasFDerivAt.comp y (hG.differentiable (by simp) y).hasFDerivAt
  have hd0 : HasFDerivAt F (graphProjectionEquiv hn hm hg ht : Plane →L[ℝ] Plane) 0 := hdF 0
  let e := hF.contDiffAt.toOpenPartialHomeomorph F hd0 (by simp)
  have he : (e : Plane → Plane)=F := rfl
  have h0s : (0 : Plane)∈e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd0 (by simp)
  have h0t : (0 : Plane)∈e.target := by simpa only [he,hF0] using e.map_source h0s
  have hI0 : e.symm 0=0 := by simpa only [he,hF0] using e.left_inv h0s
  have hIc : ContinuousAt e.symm 0 := e.continuousAt_symm h0t
  have htrans : IsOpen {y : Plane | ⟪graphSlopeNormal n (gradient g y),m⟫≠0} := by
    exact isOpen_ne_fun (((graphSlopeNormal_contDiff hn).comp (plane_gradient_contDiff hg)).continuous.inner continuous_const) continuous_const
  let U := e.target∩e.symm ⁻¹' {y : Plane | ⟪graphSlopeNormal n (gradient g y),m⟫≠0}
  have hU : IsOpen U := e.continuousOn_symm.isOpen_inter_preimage e.open_target htrans
  have h0U : (0 : Plane)∈U := ⟨h0t,by simpa only [mem_preimage,mem_ofPred_eq,hI0] using ht⟩
  have hIs : ContDiffOn ℝ (⊤ : ℕ∞) e.symm U := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy.1 (f₀' := graphProjectionEquiv hn hm hg hy.2)
    · exact hdF _
    · exact hF.contDiffAt
  let k : Plane → ℝ := fun y ↦ ⟪m,G (e.symm y)⟫
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) k U :=
    ContDiffOn.inner ℝ contDiffOn_const (hG.comp_contDiffOn hIs)
  obtain ⟨h,r,hr,hrU,hh,hhe⟩ := plane_local_smooth_extension hU hk h0U
  have hhr : h=ᶠ[𝓝 (0 : Plane)] k := Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) hhe
  have hh0 : h 0=0 := by rw [hhr.eq_of_nhds]; simp only [k,hI0,hG0,inner_zero_right]
  have hmatch : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m h y=G (e.symm y) := by
    filter_upwards [hhr,e.open_target.mem_nhds h0t] with y hy hyt
    have hi : normalPlaneCoordinates m (G (e.symm y))=y := e.right_inv hyt
    rw [normalGraph,hy]
    have hr := normalPlaneCoordinates_reconstruct hm (G (e.symm y))
    rwa [hi] at hr
  have hleft : ∀ᶠ z in 𝓝 (0 : Plane),e.symm (F z)=z :=
    Filter.mem_of_superset (e.open_source.mem_nhds h0s) (fun z hz ↦ e.left_inv hz)
  refine ⟨h,e.symm,hh,hh0,hIc,hI0,hmatch,?_⟩
  have hmc : Tendsto (normalPlaneCoordinates m) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates m).continuous.tendsto (0 : Cover)
  have hnc : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  filter_upwards [hmc.eventually hmatch,hnc.eventually hleft] with v hv hl
  constructor
  · intro heq
    rw [hv] at heq
    have hcoords := congrArg (normalPlaneCoordinates n) heq
    rw [normalPlaneCoordinates_graph hn] at hcoords
    exact hcoords ▸ heq
  · intro heq
    rw [hv]
    have heF : F (normalPlaneCoordinates n v)=normalPlaneCoordinates m v := by
      dsimp [F,G]; rw [heq]
    rw [← heF,hl]
    exact heq

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_normal_tangent_vector_eq {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) {v : Cover}
    (ht : ∀ w : Plane,⟪v,fderiv ℝ (normalGraph n g) y w⟫=0) :
    v=⟪graphSlopeNormal n (gradient g y),v⟫ • graphSlopeNormal n (gradient g y) := by
  have hz : normalPlaneCoordinates n v+⟪n,v⟫ • gradient g y=0 := by
    apply ext_inner_right ℝ
    intro w
    have hw := ht w
    rw [normalGraph_fderiv_apply hg,inner_add_right,real_inner_smul_right] at hw
    rw [inner_zero_left,inner_add_left,real_inner_smul_left]
    rw [real_inner_comm (normalPlaneEmbedding n w) v,normalPlaneEmbedding_inner_coordinates hn,
      real_inner_comm n v] at hw
    rw [real_inner_comm w (normalPlaneCoordinates n v)]
    linarith
  have he := graph_metric_projection hn (gradient g y) v
  rw [hz,map_zero] at he
  change (normalPlaneLinearIsometry n) 0+⟪gradient g y,(0 : Plane)⟫ • n=_ at he
  simp only [map_zero,inner_zero_right,zero_smul,add_zero] at he
  exact (sub_eq_zero.mp he.symm)

lemma graph_normal_tangent_positive {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) {v : Cover} (hv : ‖v‖=1)
    (ht : ∀ w : Plane,⟪v,fderiv ℝ (normalGraph n g) y w⟫=0)
    (hp : 0<⟪graphSlopeNormal n (gradient g y),v⟫) :
    v=graphSlopeNormal n (gradient g y) := by
  have he := graph_normal_tangent_vector_eq hn hg y ht
  have hc := congrArg norm he
  rw [hv,norm_smul,Real.norm_of_nonneg hp.le,graphSlopeNormal_unit hn,mul_one] at hc
  rw [← hc,one_smul] at he
  exact he

lemma normalGraph_gradient_zero_of_normal {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane)
    (ht : ∀ w : Plane,⟪n,fderiv ℝ (normalGraph n g) y w⟫=0) : gradient g y=0 := by
  apply ext_inner_left ℝ
  intro w
  have hw := ht w
  rw [normalGraph_fderiv_apply hg,inner_add_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow,mul_one,zero_add] at hw
  simpa only [inner_zero_right,real_inner_comm w] using hw

end CubicTorus
end
end
end

end OAI
