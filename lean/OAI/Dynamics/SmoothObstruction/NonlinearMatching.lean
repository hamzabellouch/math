import OAI.Dynamics.SmoothObstruction.BoundaryMatching

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.SmoothRemainder
open Set Metric
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def remainder (f : E → F) (x u : E) : F :=
  f (x+u)-f x-(fderiv ℝ f x) u

@[simp] lemma remainder_zero (f : E → F) (x : E) : remainder f x 0=0 := by
  simp [remainder]

/-- The actual, rather than hypothesized, nonlinear remainder has the
small Lipschitz constant needed by the boundary contraction. -/
theorem remainder_lipschitz (f : E → F) {x : E} {δ C : ℝ}
    (hC : 0≤C)
    (hf : ∀ y∈closedBall x δ,DifferentiableAt ℝ f y)
    (hder : ∀ y∈closedBall x δ,‖fderiv ℝ f y-fderiv ℝ f x‖≤C*‖y-x‖)
    {u v : E} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖remainder f x u-remainder f x v‖≤C*δ*‖u-v‖ := by
  have hmem (w : E) (hw : w∈closedBall (0 : E) δ) : x+w∈closedBall x δ := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
  have hr (w : E) (hw : w∈closedBall (0 : E) δ) : HasFDerivWithinAt
      (remainder f x) (fderiv ℝ f (x+w)-fderiv ℝ f x) (closedBall (0 : E) δ) w := by
    have h := (((hf (x+w) (hmem w hw)).hasFDerivAt.comp w
      ((hasFDerivAt_id w).const_add x)).sub_const (f x)).sub
        ((fderiv ℝ f x).hasFDerivAt)
    change HasFDerivAt (remainder f x) _ w at h
    simpa only [ContinuousLinearMap.comp_id] using h.hasFDerivWithinAt
  have hb (w : E) (hw : w∈closedBall (0 : E) δ) :
      ‖fderiv ℝ f (x+w)-fderiv ℝ f x‖≤C*δ := by
    have hh := hder _ (hmem w hw)
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hw) hC)
  exact (convex_closedBall (0 : E) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hr hb
    (by simpa only [mem_closedBall,dist_zero_right] using hv)
    (by simpa only [mem_closedBall,dist_zero_right] using hu)

variable [FiniteDimensional ℝ E]

/-- On a compact set strictly inside a C² coordinate domain, one common
radius and one common constant work for all actual Taylor remainders.
The estimate is uniform in the center and in the smaller tube radius. -/
theorem uniform_on_compact (f : E → F) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K⊆U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ r C : ℝ,0<r ∧ 0<C ∧ ∀ x∈K,∀ δ : ℝ,δ≤r →
      (∀ u v : E,‖u‖≤δ → ‖v‖≤δ →
        ‖remainder f x u-remainder f x v‖≤C*δ*‖u-v‖) ∧
      (∀ u : E,‖u‖≤δ → ‖remainder f x u‖≤C*‖u‖^2) := by
  obtain ⟨r,hr,hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hf' : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hf'' : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
    hf'.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨C,hC⟩ := (hK.cthickening (r:=r)).exists_bound_of_continuousOn (f:=fderiv ℝ (fderiv ℝ f)) (hf''.mono hrU)
  let D := max C 1
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hder (x : E) (hx : x∈K) : ∀ y∈closedBall x r,
      ‖fderiv ℝ f y-fderiv ℝ f x‖≤D*‖y-x‖ := by
    have hs : closedBall x r⊆cthickening r K := closedBall_subset_cthickening hx r
    apply fun y hy => (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hf'.contDiffAt (hU.mem_nhds (hrU (hs hz)))).differentiableAt (by norm_num))
      (fun z hz => (hC z (hs hz)).trans (le_max_left _ _))
      (mem_closedBall_self hr.le) hy
  refine ⟨r,D,hr,hD,?_⟩
  intro x hx δ hδ
  have hfd : ∀ y∈closedBall x r,DifferentiableAt ℝ f y := fun y hy =>
    (hf.contDiffAt (hU.mem_nhds (hrU (closedBall_subset_cthickening hx r hy)))).differentiableAt (by norm_num)
  refine ⟨?_,?_⟩
  · intro u v hu hv
    exact remainder_lipschitz f hD.le
      (fun y hy => hfd y (closedBall_subset_closedBall hδ hy))
      (fun y hy => hder x hx y (closedBall_subset_closedBall hδ hy)) hu hv
  · intro u hu
    have hnr : ‖u‖≤r := hu.trans hδ
    have hh := remainder_lipschitz f hD.le
      (fun y hy => hfd y (closedBall_subset_closedBall hnr hy))
      (fun y hy => hder x hx y (closedBall_subset_closedBall hnr hy))
      (le_refl ‖u‖) (show ‖(0 : E)‖≤‖u‖ by simp)
    simpa only [remainder_zero,sub_zero,pow_two,mul_assoc] using hh

end SmoothObstruction.SmoothRemainder

namespace SmoothObstruction.ArrayRemainder
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H]
  [NormedAddCommGroup G]
  {n₁ n₂ : ℕ}

abbrev Paths (E : Type*) (n₁ n₂ : ℕ) := (Fin (n₁+1) → E) × (Fin (n₂+1) → E)
abbrev Data (E H G : Type*) (n₁ n₂ : ℕ) :=
  (Fin n₁ → E) × (Fin n₂ → E) × E × H × G

/-- Actual one-step Taylor residuals. The affine matching and terminal
constraints really have zero residual. -/
noncomputable def residual (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E)
    (v : Paths E n₁ n₂) : Data E H G n₁ n₂ :=
  (fun t => SmoothRemainder.remainder (f₁ t) (x₁ t) (v.1 t.castSucc),
    fun t => SmoothRemainder.remainder (f₂ t) (x₂ t) (v.2 t.castSucc),0,0,0)

@[simp] lemma residual_zero (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) :
    residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ 0=0 := by
  simp [residual,funext_iff]

theorem residual_lipschitz (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (h₁ : ∀ t,∀ u v : E,‖u‖≤δ → ‖v‖≤δ →
      ‖SmoothRemainder.remainder (f₁ t) (x₁ t) u-
        SmoothRemainder.remainder (f₁ t) (x₁ t) v‖≤C*δ*‖u-v‖)
    (h₂ : ∀ t,∀ u v : E,‖u‖≤δ → ‖v‖≤δ →
      ‖SmoothRemainder.remainder (f₂ t) (x₂ t) u-
        SmoothRemainder.remainder (f₂ t) (x₂ t) v‖≤C*δ*‖u-v‖)
    {u v : Paths E n₁ n₂} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ u-residual f₁ f₂ x₁ x₂ v‖≤C*δ*‖u-v‖ := by
  have hpos : 0≤C*δ*‖u-v‖ := by positivity
  have hu₁ (t : Fin (n₁+1)) : ‖u.1 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_fst_le u).trans hu)
  have hv₁ (t : Fin (n₁+1)) : ‖v.1 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_fst_le v).trans hv)
  have hu₂ (t : Fin (n₂+1)) : ‖u.2 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_snd_le u).trans hu)
  have hv₂ (t : Fin (n₂+1)) : ‖v.2 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_snd_le v).trans hv)
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hpos).mpr
    intro t
    apply (h₁ t _ _ (hu₁ t.castSucc) (hv₁ t.castSucc)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hδ)
    exact (norm_le_pi_norm (u.1-v.1) t.castSucc).trans (norm_fst_le (u-v))
  · rw [Prod.norm_def,max_le_iff]
    constructor
    · apply (pi_norm_le_iff_of_nonneg hpos).mpr
      intro t
      apply (h₂ t _ _ (hu₂ t.castSucc) (hv₂ t.castSucc)).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hδ)
      exact (norm_le_pi_norm (u.2-v.2) t.castSucc).trans (norm_snd_le (u-v))
    · simpa only [residual,Prod.snd_sub,Prod.snd,sub_self,norm_zero] using hpos

/-- One common compact-domain Taylor estimate gives a residual Lipschitz
constant independent of the number of orbit steps. -/
theorem residual_from_derivative (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,DifferentiableAt ℝ (f₂ t) y)
    (h₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t)‖≤C*‖y-x₁ t‖)
    (h₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t)‖≤C*‖y-x₂ t‖)
    {u v : Paths E n₁ n₂} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ u-residual f₁ f₂ x₁ x₂ v‖≤C*δ*‖u-v‖ :=
  residual_lipschitz f₁ f₂ x₁ x₂ hC hδ
    (fun t _ _ hu hv => SmoothRemainder.remainder_lipschitz (f₁ t) hC (hd₁ t) (h₁ t) hu hv)
    (fun t _ _ hu hv => SmoothRemainder.remainder_lipschitz (f₂ t) hC (hd₂ t) (h₂ t) hu hv) hu hv

/-- The nonlinear recurrence is exactly the actual coordinate orbit equation,
not just a formal shadowing sequence. -/
theorem genuine_step (f : E → E) (x x' v v' : E) (hbase : f x=x')
    (heq : v'-(fderiv ℝ f x) v=SmoothRemainder.remainder f x v) :
    f (x+v)=x'+v' := by
  unfold SmoothRemainder.remainder at heq
  rw [hbase] at heq
  have h := congrArg (fun z => z+(fderiv ℝ f x) v) heq
  simp only [sub_add_cancel] at h
  rw [h]
  abel

end SmoothObstruction.ArrayRemainder

namespace SmoothObstruction.NonlinearBoundary
open Metric Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The boundary-inverse contraction from source section4. The ambient
space can be a finite array with its supremum norm: no step-count factor
is introduced. Uniqueness is on the larger radius δ, not just the sharp
shadowing radius. -/
theorem solve (L : E ≃L[ℝ] F) (R : E → F) (a : F)
    {Q C r δ : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ Q)
    (ha : ‖a‖ ≤ C*r) (hR0 : R 0 = 0)
    (hR : ∀ u ∈ closedBall (0 : E) δ, ∀ v ∈ closedBall (0 : E) δ,
      ‖R u-R v‖ ≤ C*δ*‖u-v‖)
    (hsmall : Q*C*δ ≤ 1/4) (hdata : Q*C*r ≤ δ/4) :
    ∃ v : E, ‖v‖ ≤ δ/2 ∧ ‖v‖ ≤ 2*C*Q*r ∧ L v = a+R v ∧
      ∀ u : E, ‖u‖ ≤ δ → L u = a+R u → u=v := by
  let f : E → E := fun v => L.symm (a+R v)
  have hz : (0 : E) ∈ closedBall (0 : E) δ := by simpa using hδ.le
  have hbound (u : E) (hu : u ∈ closedBall (0 : E) δ) :
      ‖f u‖ ≤ Q*C*r+(1/4:ℝ)*‖u‖ := by
    have hRu : ‖R u‖ ≤ C*δ*‖u‖ := by simpa only [hR0,sub_zero] using hR u hu 0 hz
    calc
      _ ≤ Q*‖a+R u‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ ≤ Q*(C*r+C*δ*‖u‖) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add ha hRu)) hQ
      _ = Q*C*r+(Q*C*δ)*‖u‖ := by ring
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)) _
  have hmap : MapsTo f (closedBall (0 : E) δ) (closedBall (0 : E) δ) := by
    intro u hu
    rw [mem_closedBall,dist_zero_right]
    have hu' : ‖u‖ ≤ δ := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hb := hbound u hu
    linarith
  have hdist (u v : E) (hu : u ∈ closedBall (0 : E) δ) (hv : v ∈ closedBall (0 : E) δ) :
      dist (f u) (f v) ≤ (1/4:ℝ)*dist u v := by
    simp only [dist_eq_norm,f,←map_sub,add_sub_add_left_eq_sub]
    calc
      _ ≤ Q*‖R u-R v‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ ≤ Q*(C*δ*‖u-v‖) := mul_le_mul_of_nonneg_left (hR u hu v hv) hQ
      _ = (Q*C*δ)*‖u-v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hcontract : ContractingWith (1/4 : NNReal) (hmap.restrict f _ _) := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    exact hdist u v u.property v.property
  obtain ⟨v,hv,hfix,-, -⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hz (edist_ne_top _ _)
  have hvnorm : ‖v‖ ≤ δ := by simpa only [mem_closedBall,dist_zero_right] using hv
  have hb := hbound v hv
  have hfv : f v=v := hfix
  rw [hfv] at hb
  refine ⟨v,by linarith,?_,?_,?_⟩
  · have hp : 0 ≤ Q*C*r := mul_nonneg (mul_nonneg hQ hC) hr
    nlinarith
  · have hh := congrArg L hfv
    simpa only [f,L.apply_symm_apply] using hh.symm
  · intro u hu heq
    have humem : u ∈ closedBall (0 : E) δ := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hfu : f u=u := by dsimp [f]; rw [←heq,L.symm_apply_apply]
    have hh := hdist u v humem hv
    rw [hfu,hfv] at hh
    exact dist_eq_zero.mp (by linarith [dist_nonneg (x:=u) (y:=v)])

omit [CompleteSpace E] in
/-- The nonlinear correction differs quadratically from the linear
solution, with the exact inverse cost. This is the source estimate used
for ideal coordinate exchange, once the sharp norm bound is inserted. -/
theorem nonlinear_linear_error (L : E ≃L[ℝ] F) {R : E → F} {a : F}
    {v : E} {Q C : ℝ} (hL : ‖L.symm.toContinuousLinearMap‖ ≤ Q)
    (_hC : 0 ≤ C) (hR : ‖R v‖ ≤ C*‖v‖^2) (heq : L v=a+R v) :
    ‖v-L.symm a‖ ≤ Q*C*‖v‖^2 := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hL
  have hv : v=L.symm (a+R v) := by rw [←heq,L.symm_apply_apply]
  calc
    _ = ‖L.symm (a+R v)-L.symm a‖ := congrArg (fun w => ‖w-L.symm a‖) hv
    _ = ‖L.symm (R v)‖ := by rw [map_add,add_sub_cancel_left]
    _ ≤ Q*‖R v‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    _ ≤ Q*(C*‖v‖^2) := mul_le_mul_of_nonneg_left hR hQ
    _ = _ := by ring
end SmoothObstruction.NonlinearBoundary

namespace SmoothObstruction.FiniteGreen.Matching
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- The finite boundary inverse and actual Taylor residual yield a genuine
pair of nonlinear coordinate orbits, with a common middle point. All
terminal equations remain exact. The derivative and propagation estimates
are precisely the finite-window inputs, not the desired orbit conclusion. -/
theorem nonlinear_orbits (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K C r δ : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin (n₁+1) → E) (x₂ : Fin (n₂+1) → E)
    (hx₁ : ∀ t,f₁ t (x₁ t.castSucc)=x₁ t.succ)
    (hx₂ : ∀ t,f₂ t (x₂ t.castSucc)=x₂ t.succ)
    (hA₁ : ∀ t : Fin n₁,fderiv ℝ (f₁ t) (x₁ t.castSucc)=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n₂,fderiv ℝ (f₂ t) (x₂ t.castSucc)=A₂.map (t+1) t)
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,DifferentiableAt ℝ (f₂ t) y)
    (hder₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,
      ‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t.castSucc)‖≤C*‖y-x₁ t.castSucc‖)
    (hder₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,
      ‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t.castSucc)‖≤C*‖y-x₂ t.castSucc‖)
    (hnear : ‖x₂ 0-x₁ 0‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ v : Paths E n₁ n₂,‖v‖≤δ/2 ∧ ‖v‖≤2*C*Q*r ∧
      (∀ t,f₁ t (x₁ t.castSucc+v.1 t.castSucc)=x₁ t.succ+v.1 t.succ) ∧
      (∀ t,f₂ t (x₂ t.castSucc+v.2 t.castSucc)=x₂ t.succ+v.2 t.succ) ∧
      x₁ 0+v.1 0=x₂ 0+v.2 0 ∧
      C₁.P (v.1 (Fin.last n₁))=0 ∧ C₂.P (v.2 (Fin.last n₂))=0 := by
  classical
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  let a : Data E H G n₁ n₂ := (0,0,x₂ 0-x₁ 0,0,0)
  let R := ArrayRemainder.residual (H:=H) (G:=G) f₁ f₂
    (fun t => x₁ t.castSucc) (fun t => x₂ t.castSucc)
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hQ : 0≤Q := by dsimp [Q,D]; positivity
  have hb : ‖V.symm.toContinuousLinearMap‖≤Q := boundary_inverse_norm C₁ C₂ L hL hU hK
    hsmall hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
  have ha : ‖a‖≤C*r := by simpa [a,Prod.norm_def] using hnear
  have hR : ∀ u∈closedBall (0 : Paths E n₁ n₂) δ,
      ∀ v∈closedBall (0 : Paths E n₁ n₂) δ,‖R u-R v‖≤C*δ*‖u-v‖ := by
    intro u hu v hv
    apply ArrayRemainder.residual_from_derivative f₁ f₂ _ _ hC hδ.le
      hd₁ hd₂ hder₁ hder₂
    · simpa using hu
    · simpa using hv
  obtain ⟨v,hv,hv',heq,-⟩ := NonlinearBoundary.solve V R a hQ hC hr hδ hb ha
    (ArrayRemainder.residual_zero _ _ _ _) hR hcontract hdata
  refine ⟨v,hv,hv',?_,?_,?_,?_,?_⟩
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₁ t)
    rw [hA₁]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₂ t)
    rw [hA₂]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.1) heq
    change v.1 0-v.2 0=x₂ 0-x₁ 0+0 at h
    rw [add_zero] at h
    have h' := congrArg (fun z => x₁ 0+z+v.2 0) h
    simpa [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h'
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.1) heq
    change C₁.P _=0+0 at h
    simpa using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.2) heq
    change C₂.P _=0+0 at h
    simpa using h
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.FiniteGreen.Matching
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- The finite boundary inverse and actual Taylor residual yield a genuine
pair of nonlinear coordinate orbits, with a common middle point. All
terminal equations remain exact. The derivative and propagation estimates
are precisely the finite-window inputs, not the desired orbit conclusion. -/
theorem nonlinear_orbits_unique (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K C r δ : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin (n₁+1) → E) (x₂ : Fin (n₂+1) → E)
    (hx₁ : ∀ t,f₁ t (x₁ t.castSucc)=x₁ t.succ)
    (hx₂ : ∀ t,f₂ t (x₂ t.castSucc)=x₂ t.succ)
    (hA₁ : ∀ t : Fin n₁,fderiv ℝ (f₁ t) (x₁ t.castSucc)=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n₂,fderiv ℝ (f₂ t) (x₂ t.castSucc)=A₂.map (t+1) t)
    (hC : 0≤C) (hr : 0≤r) (hδ : 0<δ)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,DifferentiableAt ℝ (f₂ t) y)
    (hder₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,
      ‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t.castSucc)‖≤C*‖y-x₁ t.castSucc‖)
    (hder₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,
      ‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t.castSucc)‖≤C*‖y-x₂ t.castSucc‖)
    (hnear : ‖x₂ 0-x₁ 0‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ v : Paths E n₁ n₂,‖v‖≤δ/2 ∧ ‖v‖≤2*C*Q*r ∧
      (∀ t,f₁ t (x₁ t.castSucc+v.1 t.castSucc)=x₁ t.succ+v.1 t.succ) ∧
      (∀ t,f₂ t (x₂ t.castSucc+v.2 t.castSucc)=x₂ t.succ+v.2 t.succ) ∧
      x₁ 0+v.1 0=x₂ 0+v.2 0 ∧
      C₁.P (v.1 (Fin.last n₁))=0 ∧ C₂.P (v.2 (Fin.last n₂))=0 ∧
      ∀ u : Paths E n₁ n₂,‖u‖≤δ →
        (∀ t,f₁ t (x₁ t.castSucc+u.1 t.castSucc)=x₁ t.succ+u.1 t.succ) →
        (∀ t,f₂ t (x₂ t.castSucc+u.2 t.castSucc)=x₂ t.succ+u.2 t.succ) →
        x₁ 0+u.1 0=x₂ 0+u.2 0 →
        C₁.P (u.1 (Fin.last n₁))=0 → C₂.P (u.2 (Fin.last n₂))=0 → u=v := by
  classical
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  let a : Data E H G n₁ n₂ := (0,0,x₂ 0-x₁ 0,0,0)
  let R := ArrayRemainder.residual (H:=H) (G:=G) f₁ f₂
    (fun t => x₁ t.castSucc) (fun t => x₂ t.castSucc)
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hQ : 0≤Q := by dsimp [Q,D]; positivity
  have hb : ‖V.symm.toContinuousLinearMap‖≤Q := boundary_inverse_norm C₁ C₂ L hL hU hK
    hsmall hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
  have ha : ‖a‖≤C*r := by simpa [a,Prod.norm_def] using hnear
  have hR : ∀ u∈closedBall (0 : Paths E n₁ n₂) δ,
      ∀ v∈closedBall (0 : Paths E n₁ n₂) δ,‖R u-R v‖≤C*δ*‖u-v‖ := by
    intro u hu v hv
    apply ArrayRemainder.residual_from_derivative f₁ f₂ _ _ hC hδ.le
      hd₁ hd₂ hder₁ hder₂
    · simpa using hu
    · simpa using hv
  obtain ⟨v,hv,hv',heq,huniq⟩ := NonlinearBoundary.solve V R a hQ hC hr hδ hb ha
    (ArrayRemainder.residual_zero _ _ _ _) hR hcontract hdata
  refine ⟨v,hv,hv',?_,?_,?_,?_,?_,?_⟩
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₁ t)
    rw [hA₁]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₂ t)
    rw [hA₂]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.1) heq
    change v.1 0-v.2 0=x₂ 0-x₁ 0+0 at h
    rw [add_zero] at h
    have h' := congrArg (fun z => x₁ 0+z+v.2 0) h
    simpa [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h'
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.1) heq
    change C₁.P _=0+0 at h
    simpa using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.2) heq
    change C₂.P _=0+0 at h
    simpa using h
  · intro u hu hs₁ hs₂ hm hp₁ hp₂
    apply huniq u hu
    apply Prod.ext
    · funext t
      change u.1 t.succ-A₁.map (t+1) t (u.1 t.castSucc)=
        0+(f₁ t (x₁ t.castSucc+u.1 t.castSucc)-f₁ t (x₁ t.castSucc)-
          (fderiv ℝ (f₁ t) (x₁ t.castSucc)) (u.1 t.castSucc))
      rw [hs₁ t,hx₁ t,hA₁ t,zero_add]
      abel
    · apply Prod.ext
      · funext t
        change u.2 t.succ-A₂.map (t+1) t (u.2 t.castSucc)=
          0+(f₂ t (x₂ t.castSucc+u.2 t.castSucc)-f₂ t (x₂ t.castSucc)-
            (fderiv ℝ (f₂ t) (x₂ t.castSucc)) (u.2 t.castSucc))
        rw [hs₂ t,hx₂ t,hA₂ t,zero_add]
        abel
      · apply Prod.ext
        · change u.1 0-u.2 0=(x₂ 0-x₁ 0)+0
          have hh := congrArg (fun z => z-x₁ 0-u.2 0) hm
          simpa only [add_zero] using (by convert hh using 1 <;> abel)
        · apply Prod.ext
          · change C₁.P (u.1 (Fin.last n₁))=0+0
            simpa only [add_zero] using hp₁
          · change C₂.P (u.2 (Fin.last n₂))=0+0
            simpa only [add_zero] using hp₂
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.IdealExchange
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Orthogonal gap control followed by an oblique complementary projector.
This retains the reference inverse cost instead of silently treating the
nonorthogonal slow/fast decomposition as orthogonal. -/
lemma annihilator_bound (U V : Submodule ℝ E) (Q : E →L[ℝ] E)
    {ε G : ℝ} (hG : 0≤G) (_hε : 0≤ε)
    (hclose : ‖U.starProjection-V.starProjection‖≤ε)
    (hQ : ‖Q‖≤G) (hzero : ∀ v∈V,Q v=0) (x : U) :
    ‖Q (x:E)‖≤G*ε*‖x‖ := by
  have he : Q (x:E)=Q ((x:E)-V.starProjection (x:E)) := by
    rw [map_sub,hzero _ (V.starProjection_apply_mem _),sub_zero]
  rw [he]
  have hdist : ‖(x:E)-V.starProjection (x:E)‖≤ε*‖x‖ := by
    have hh := (U.starProjection-V.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,U.starProjection_eq_self_iff.mpr x.property] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg x))
  exact ((Q.le_opNorm _).trans (mul_le_mul hQ hdist (norm_nonneg _) hG)).trans_eq (by ring)

/-- A pair of small endpoint graphs over nearby complementary spaces gives
ideal exchange at time zero; the large full-window shadowing cost does not
multiply the space-comparison error. -/
theorem graph_exchange_error {A₀ : FiniteGreen.Evolution E}
    (B₀ : FiniteGreen.Splitting A₀) (U V : Submodule ℝ E)
    (C D : E →L[ℝ] E) (a : U) (b : V) (m : E)
    {ε κ G R : ℝ} (hε : 0≤ε) (hκ : 0≤κ) (hG : 0≤G) (_hR : 0≤R)
    (hcU : ‖U.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hcV : ‖V.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hC : ‖C‖≤κ) (hD : ‖D‖≤κ)
    (hP : ‖B₀.slow 0‖≤G) (hQ : ‖B₀.fast 0‖≤G)
    (ha : ‖a‖≤R) (hb : ‖b‖≤R)
    (hm : (a:E)+C a-((b:E)+D b)=m) :
    ‖((a:E)+C a)-B₀.slow 0 m‖≤2*G*(ε+κ)*R := by
  have hQa : ‖B₀.fast 0 (a:E)‖≤G*ε*R :=
    (annihilator_bound U (B₀.slow 0).range (B₀.fast 0) hG hε hcU hQ
      (by rintro v ⟨w,rfl⟩; exact B₀.fast_slow 0 w) a).trans
        (mul_le_mul_of_nonneg_left ha (by positivity))
  have hPb : ‖B₀.slow 0 (b:E)‖≤G*ε*R :=
    (annihilator_bound V (B₀.fast 0).range (B₀.slow 0) hG hε hcV hP
      (by rintro v ⟨w,rfl⟩; exact B₀.slow_fast 0 w) b).trans
        (mul_le_mul_of_nonneg_left hb (by positivity))
  have bound (Q C : E →L[ℝ] E) (v : E) (hQ : ‖Q‖≤G) (hC : ‖C‖≤κ) (hv : ‖v‖≤R) :
      ‖Q (C v)‖≤G*κ*R := by
    apply (Q.le_opNorm _).trans
    apply (mul_le_mul hQ ((C.le_opNorm _).trans
      (mul_le_mul hC hv (norm_nonneg _) hκ)) (norm_nonneg _) hG).trans_eq
    ring
  have he : ((a:E)+C a)-B₀.slow 0 m=
      B₀.fast 0 (a:E)+B₀.fast 0 (C a)+(B₀.slow 0 (b:E)+B₀.slow 0 (D b)) := by
    rw [←hm,map_sub,map_add,map_add]
    have hh := B₀.add_apply 0 ((a:E)+C a)
    rw [map_add,map_add] at hh
    rw [←hh]
    abel
  rw [he]
  calc
    _ ≤ (‖B₀.fast 0 (a:E)‖+‖B₀.fast 0 (C a)‖)+
        (‖B₀.slow 0 (b:E)‖+‖B₀.slow 0 (D b)‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ (G*ε*R+G*κ*R)+(G*ε*R+G*κ*R) :=
      add_le_add (add_le_add hQa (bound _ _ _ hQ hC ha))
        (add_le_add hPb (bound _ _ _ hP hD hb))
    _ = _ := by ring
end SmoothObstruction.IdealExchange

namespace SmoothObstruction.FiniteGreen.Matching
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- Quantitative ideal exchange for the actual zero-forcing boundary inverse.
The middle cost is O(exp(C b n)), separate from full-orbit exp(C g n). -/
theorem linear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (v₁ v₂ : ℕ → E) (m : E)
    (hv₁ : ∀ t<n₁,v₁ (t+1)=A₁.map (t+1) t (v₁ t))
    (hv₂ : ∀ t<n₂,v₂ (t+1)=A₂.map (t+1) t (v₂ t))
    (he₁ : C₁.P (v₁ n₁)=0) (he₂ : C₂.P (v₂ n₂)=0)
    (hm : v₁ 0-v₂ 0=m) :
    ‖v₁ 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖ := by
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) (hsmall.trans_lt (by norm_num))
  let a : B₁.initialSpace := ⟨B₁.slow 0 (v₁ 0),⟨v₁ 0,rfl⟩⟩
  let b : B₂.initialSpace := ⟨B₂.slow 0 (v₂ 0),⟨v₂ 0,rfl⟩⟩
  have hg₁ := C₁.trajectory_unique (fun _ => 0) a (B₁.slow_initial a) 0 v₁
    (by simpa only [add_zero] using hv₁) rfl he₁
  have hg₂ := C₂.trajectory_unique (fun _ => 0) b (B₂.slow_initial b) 0 v₂
    (by simpa only [add_zero] using hv₂) rfl he₂
  have h0₁ : v₁ 0=(a:E)+C₁.kernel a := by
    rw [hg₁ 0 (Nat.zero_le n₁),C₁.trajectory_initial _ _ (B₁.slow_initial a),
      C₁.trajectory_zero]
    simp
  have h0₂ : v₂ 0=(b:E)+C₂.kernel b := by
    rw [hg₂ 0 (Nat.zero_le n₂),C₂.trajectory_initial _ _ (B₂.slow_initial b),
      C₂.trajectory_zero]
    simp
  have hMa : M (a,b)=m := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    rw [h0₁,h0₂] at hm
    calc
      _ = (a:E)+C₁.kernel a-((b:E)+C₂.kernel b) := by abel
      _ = m := hm
  have hn : ‖(a,b)‖≤(2*K)*‖m‖ := by
    have hi := BoundaryNeumann.inverse_norm L (correction C₁ C₂) hK hsmall
    have ha : M.symm m=(a,b) := M.symm_apply_eq.mpr hMa.symm
    rw [←ha]
    exact (M.symm.toContinuousLinearMap.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg m))
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  rw [h0₁]
  apply (IdealExchange.graph_exchange_error B₀ B₁.initialSpace B₂.initialSpace
    C₁.kernel C₂.kernel a b m hε hκ hP (by positivity) hc₁ hc₂ hk₁ hk₂ hs hf
    ((norm_fst_le (a,b)).trans hn) ((norm_snd_le (a,b)).trans hn)
    (by rwa [h0₁,h0₂] at hm)).trans_eq
  ring
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.ArrayRemainder
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n₁ n₂ : ℕ}

omit [NormedSpace ℝ H] [NormedSpace ℝ G] in
/-- The actual array residual is quadratic in the sup norm, with a constant
independent of either window length. The smaller radius is the array norm. -/
theorem residual_quadratic (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,DifferentiableAt ℝ (f₂ t) y)
    (h₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t)‖≤C*‖y-x₁ t‖)
    (h₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t)‖≤C*‖y-x₂ t‖)
    {v : Paths E n₁ n₂} (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ v‖≤C*‖v‖^2 := by
  have hh := residual_from_derivative (H:=H) (G:=G) f₁ f₂ x₁ x₂ hC (norm_nonneg v)
    (fun t y hy => hd₁ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => hd₂ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => h₁ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => h₂ t y (closedBall_subset_closedBall hv hy))
    (le_refl ‖v‖) (show ‖(0 : Paths E n₁ n₂)‖≤‖v‖ by simp)
  simpa only [residual_zero,sub_zero,pow_two,mul_assoc] using hh
end SmoothObstruction.ArrayRemainder

namespace SmoothObstruction.FiniteGreen.Matching
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

theorem array_linear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (v : Paths E n₁ n₂) (m : E) (hv : boundary C₁ C₂ v=(0,0,m,0,0)) :
    ‖v.1 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖ := by
  have h₁ : ∀ t<n₁,extend v.1 (t+1)=A₁.map (t+1) t (extend v.1 t) := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hv
    change v.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (v.1 ⟨t,by omega⟩)=0 at h
    simpa only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega)]
      using sub_eq_zero.mp h
  have h₂ : ∀ t<n₂,extend v.2 (t+1)=A₂.map (t+1) t (extend v.2 t) := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hv
    change v.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (v.2 ⟨t,by omega⟩)=0 at h
    simpa only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega)]
      using sub_eq_zero.mp h
  have he₁ : C₁.P (extend v.1 n₁)=0 := by
    change C₁.P (extend v.1 (Fin.last n₁))=0
    rw [extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hv
  have he₂ : C₂.P (extend v.2 n₂)=0 := by
    change C₂.P (extend v.2 (Fin.last n₂))=0
    rw [extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hv
  have hm : extend v.1 0-extend v.2 0=m := by
    change extend v.1 (0 : Fin (n₁+1))-extend v.2 (0 : Fin (n₂+1))=m
    rw [extend_apply,extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hv
  have hh := linear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hsmall hc₁ hc₂
    hk₁ hk₂ hs hf (extend v.1) (extend v.2) m h₁ h₂ he₁ he₂ hm
  change ‖extend v.1 (0 : Fin (n₁+1))-B₀.slow 0 m‖≤_ at hh
  rwa [extend_apply] at hh

/-- Linear graph-space error and nonlinear residual have DIFFERENT costs.
In particular, no full-window inverse multiplies the common-bin gap error. -/
theorem array_nonlinear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ Q C : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ) (hC : 0≤C)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (R : Paths E n₁ n₂ → Data E H G n₁ n₂) (v : Paths E n₁ n₂) (m : E)
    (hR : ‖R v‖≤C*‖v‖^2)
    (heq : boundary C₁ C₂ v=(0,0,m,0,0)+R v)
    (hQ : ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤Q) :
    ‖v.1 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖+Q*C*‖v‖^2 := by
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let w := V.symm (0,0,m,0,0)
  have hw : boundary C₁ C₂ w=(0,0,m,0,0) := V.apply_symm_apply _
  have he := NonlinearBoundary.nonlinear_linear_error V hQ hC hR heq
  have hl := array_linear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hsmall hc₁ hc₂
    hk₁ hk₂ hs hf w m hw
  calc
    _ ≤ ‖w.1 0-B₀.slow 0 m‖+‖v.1 0-w.1 0‖ := by
      convert norm_add_le (w.1 0-B₀.slow 0 m) (v.1 0-w.1 0) using 1
      congr 1
      abel
    _ ≤ _ := add_le_add hl (((norm_le_pi_norm (v.1-w.1) 0).trans (norm_fst_le (v-w))).trans he)
end SmoothObstruction.FiniteGreen.Matching

end

end OAI
