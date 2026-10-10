import OAI.Analysis.LienardCycles.Model

namespace OAI

universe uE uι

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow

abbrev UnitInterval := Icc (-1 : ℝ) 1
abbrev Path (E : Type uE) [TopologicalSpace E] := C(UnitInterval, E)

noncomputable def clamp (t : ℝ) : UnitInterval := projIcc (-1) 1 (by norm_num) t

@[simp] lemma clamp_val (t : UnitInterval) : clamp t = t := by
  simp [clamp]

lemma continuous_clamp : Continuous clamp := by
  exact continuous_projIcc (h := by norm_num)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def extend (u : Path E) : ℝ → E := fun t => u (clamp t)

omit [NormedSpace ℝ E] in
lemma continuous_extend (u : Path E) : Continuous (extend u) :=
  u.continuous.comp continuous_clamp

omit [NormedSpace ℝ E] in
@[simp] lemma extend_val (u : Path E) (t : UnitInterval) : extend u t = u t := by
  simp [extend]

omit [NormedSpace ℝ E] in
@[simp] lemma extend_add (u v : Path E) : extend (u+v) = extend u + extend v := rfl
@[simp] lemma extend_smul (c : ℝ) (u : Path E) : extend (c • u) = c • extend u := rfl

noncomputable def primitive (u : Path E) : Path E where
  toFun t := ∫ s in (0:ℝ)..(t:ℝ), extend u s
  continuous_toFun := by
    have hc : Continuous (fun t : ℝ => ∫ s in (0:ℝ)..t, extend u s) :=
      intervalIntegral.continuous_primitive (continuous_extend u).intervalIntegrable 0
    exact hc.comp continuous_subtype_val

@[simp] lemma primitive_apply (u : Path E) (t : UnitInterval) :
    primitive u t = ∫ s in (0:ℝ)..(t:ℝ), extend u s := rfl

lemma norm_primitive_le (u : Path E) : ‖primitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  calc
    ‖primitive u t‖ ≤ ‖u‖ * |(t:ℝ)-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => u.norm_coe_le_norm (clamp s)
    _ ≤ ‖u‖ := by
      have ht : |(t:ℝ)| ≤ 1 := abs_le.mpr t.property
      simpa using mul_le_mul_of_nonneg_left ht (norm_nonneg u)

noncomputable def primitiveCLM : Path E →L[ℝ] Path E :=
  LinearMap.mkContinuous
    { toFun := primitive
      map_add' := by
        intro u v
        ext t
        simp only [primitive_apply, ContinuousMap.add_apply, extend_add, Pi.add_apply]
        exact intervalIntegral.integral_add ((continuous_extend u).intervalIntegrable _ _)
          ((continuous_extend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        simp [primitive_apply, intervalIntegral.integral_smul] }
    1 (by intro u; simpa using norm_primitive_le u)

@[simp] lemma primitiveCLM_apply (u : Path E) : primitiveCLM u = primitive u := rfl

noncomputable def constCLM : E →L[ℝ] Path E :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.const UnitInterval
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro c x; ext; rfl }
    1 (by
      intro x
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg x)).mpr (fun _ => le_rfl))

@[simp] lemma constCLM_apply (x : E) (t : UnitInterval) : constCLM x t = x := rfl

theorem exists_contDiff_picard [CompleteSpace E] (W : Path E → Path E) (x₀ : E)
    (hW : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ U : E × ℝ → Path E,
      ContDiffAt ℝ ω U (x₀,0) ∧ U (x₀,0) = constCLM x₀ ∧
      (∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        U p = constCLM p.1 + p.2 • primitiveCLM (W (U p))) ∧
      ∀ᶠ p in 𝓝 ((x₀,(0:ℝ)),constCLM x₀),
        p.2 = constCLM p.1.1 + p.1.2 • primitiveCLM (W p.2) → U p.1 = p.2 := by
  let Φ : (E × ℝ) × Path E → Path E :=
    fun p => p.2 - constCLM p.1.1 - p.1.2 • primitiveCLM (W p.2)
  have hΦ : ContDiffAt ℝ ω Φ ((x₀,0),constCLM x₀) := by
    apply ContDiffAt.sub
    · exact contDiffAt_snd.sub ((constCLM (E := E)).contDiff.contDiffAt.comp ((x₀,0),constCLM x₀) (contDiffAt_fst.fst))
    · exact contDiffAt_fst.snd.smul
        ((primitiveCLM (E := E)).contDiff.contDiffAt.comp ((x₀,0),constCLM x₀) (hW.comp ((x₀,0),constCLM x₀) contDiffAt_snd))
  have hpartial : fderiv ℝ Φ ((x₀,0),constCLM x₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) (Path E) = ContinuousLinearMap.id ℝ (Path E) := by
    have hd := (hΦ.differentiableAt (by simp)).hasFDerivAt.comp (constCLM x₀)
      ((hasFDerivAt_const (x₀,(0:ℝ)) (constCLM x₀)).prodMk (hasFDerivAt_id (constCLM x₀)))
    have he : HasFDerivAt (fun u : Path E => Φ ((x₀,0),u))
        (ContinuousLinearMap.id ℝ (Path E)) (constCLM x₀) := by
      simpa [Φ] using (hasFDerivAt_id (constCLM x₀)).sub_const (constCLM x₀)
    convert hd.unique he using 1; ext u; simp
  have hinv : (fderiv ℝ Φ ((x₀,0),constCLM x₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) (Path E)).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  let U := hΦ.implicitFunction (by simp) hinv
  refine ⟨U, hΦ.contDiffAt_implicitFunction (by simp) hinv,
    hΦ.implicitFunction_apply_self (by simp) hinv, ?_⟩
  constructor
  · filter_upwards [hΦ.eventually_apply_implicitFunction (by simp) hinv] with p hp
    change Φ (p,U p) = Φ ((x₀,0),constCLM x₀) at hp
    simp only [Φ, sub_self, zero_smul] at hp
    simpa [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hp)
  · filter_upwards [hΦ.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with p hp
    intro he
    apply hp.mp
    change p.2 - constCLM p.1.1 - p.1.2 • primitiveCLM (W p.2) = _
    rw [sub_sub, sub_eq_zero.mpr he]
    simp [Φ]

@[simp] lemma extend_const (x : E) : extend (constCLM x) = fun _ => x := rfl

@[simp] lemma primitive_zero (u : Path E) : extend (primitive u) 0 = 0 := by
  simp [extend, primitive_apply, clamp, projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)]

lemma hasDerivAt_extend_primitive [CompleteSpace E] (u : Path E) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extend (primitive u)) (extend u s) s := by
  have hd := (continuous_extend u).integral_hasStrictDerivAt 0 s
  apply hd.hasDerivAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  simp [extend, primitive_apply, clamp, projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (Ioo_subset_Icc_self ht)]

lemma picard_initial (W : Path E → Path E) {x : E} {t : ℝ} {u : Path E}
    (hu : u = constCLM x + t • primitiveCLM (W u)) : extend u 0 = x := by
  have he := congrArg (fun u : Path E => extend u 0) hu
  simpa [extend_add, extend_smul, primitiveCLM_apply] using he

lemma picard_derivative [CompleteSpace E] (W : Path E → Path E)
    {x : E} {t : ℝ} {u : Path E}
    (hu : u = constCLM x + t • primitiveCLM (W u))
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extend u) (t • extend (W u) s) s := by
  nth_rw 1 [hu]
  simpa only [extend_add, extend_smul, primitiveCLM_apply, extend_const,
    Pi.add_apply, Pi.smul_apply, zero_add] using
    (hasDerivAt_const s x).add ((hasDerivAt_extend_primitive (W u) hs).const_smul t)

noncomputable def reparam (u : Path E) (q : ℝ) : Path E where
  toFun s := extend u (q * s)
  continuous_toFun := (continuous_extend u).comp (continuous_const.mul continuous_subtype_val)

omit [NormedSpace ℝ E] in
@[simp] lemma reparam_apply (u : Path E) (q : ℝ) (s : UnitInterval) :
    reparam u q s = extend u (q * s) := rfl

lemma dist_reparam_const_le (u : Path E) (q : ℝ) (x : E) :
    dist (reparam u q) (constCLM x) ≤ dist u (constCLM x) := by
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (f := u) (g := constCLM x) (clamp (q * s))

lemma abs_mul_lt_one {q s : ℝ} (hq : |q| < 1) (hs : |s| ≤ 1) :
    q * s ∈ Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  calc
    |q * s| = |q| * |s| := abs_mul _ _
    _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ < 1 := by simpa using hq

lemma picard_rescale [CompleteSpace E] (W : Path E → Path E) (V : E → E)
    {x : E} {t q : ℝ} {u : Path E}
    (hWu : ∀ s, W u s = V (u s))
    (hWr : ∀ s, W (reparam u q) s = V (reparam u q s))
    (hu : u = constCLM x + t • primitiveCLM (W u)) (hq : |q| < 1) :
    reparam u q = constCLM x + (t*q) • primitiveCLM (W (reparam u q)) := by
  ext s
  let f : ℝ → E := fun y => extend u (q*y)
  let g : ℝ → E := fun y => (t*q) • extend (W (reparam u q)) y
  have hd (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) : HasDerivAt f (g y) y := by
    have hqy := abs_mul_lt_one hq (abs_le.mpr hy)
    have hder := (picard_derivative W hu hqy).scomp y ((hasDerivAt_id y).const_mul q)
    simpa [f, g, Function.comp_def, extend, hWu, hWr, reparam_apply, clamp,
      projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hy, smul_smul, mul_comm]
      using hder
  have hgi : IntervalIntegrable g volume 0 s :=
    ((continuous_extend (W (reparam u q))).const_smul (t*q)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y ?_) hgi
  · have hf0 : f 0 = x := by simpa [f] using picard_initial W hu
    have hes : (∫ y in (0:ℝ)..(s:ℝ), g y) = (t*q) • primitive (W (reparam u q)) s := by
      simp [g, primitive_apply, intervalIntegral.integral_smul]
    rw [hf0, hes] at he
    change f s = x + (t*q) • primitive (W (reparam u q)) s
    exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)
  · exact uIcc_subset_Icc (by norm_num) s.property hy

theorem exists_analytic_local_flow_eventually [CompleteSpace E] (W : Path E → Path E)
    (V : E → E) (x₀ : E) (hW : ∀ᶠ u in 𝓝 (constCLM x₀), ∀ s, W u s = V (u s))
    (hsmooth : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        f (p.1,0) = p.1 ∧ HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2 := by
  obtain ⟨U,hU,hU₀,hEq,hUnique⟩ := exists_contDiff_picard W x₀ hsmooth
  obtain ⟨ε₀,hε₀,huniq⟩ := Metric.mem_nhds_iff.mp hUnique
  obtain ⟨η,hη,hWnear⟩ := Metric.mem_nhds_iff.mp hW
  let ε := min ε₀ η
  have hε : 0 < ε := lt_min hε₀ hη
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hUc : Tendsto U (𝓝 (x₀,(0:ℝ))) (𝓝 (constCLM x₀)) := by
    have hc := hU.continuousAt
    rw [ContinuousAt, hU₀] at hc
    exact hc
  have hnear := hEq.and (hUc.eventually (Metric.ball_mem_nhds (constCLM x₀) hε))
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  let τ := δ/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτδ : τ < δ := by dsimp [τ]; linarith
  let r := min δ (min ε τ)
  have hr : 0 < r := lt_min hδ (lt_min hε hτ)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrε : r ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hτnear (x : E) (hx : dist x x₀ < r) :
      U (x,τ) = constCLM x + τ • primitiveCLM (W (U (x,τ))) ∧
        dist (U (x,τ)) (constCLM x₀) < ε := by
    apply hδnear
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    exact ⟨hx.trans_le hrδ, by simpa [abs_of_pos hτ] using hτδ⟩
  let e : UnitInterval := ⟨1,by norm_num⟩
  let f : E × ℝ → E := fun p => U p e
  have hf : ContDiffAt ℝ ω f (x₀,0) :=
    (ContinuousMap.evalCLM ℝ e : Path E →L[ℝ] E).contDiff.contDiffAt.comp (x₀,0) hU
  have hrep (x : E) (t : ℝ) (hx : dist x x₀ < r) (ht : |t| < r) :
      f (x,t) = extend (U (x,τ)) (t/τ) := by
    have hqt : |t/τ| < 1 := by
      rw [abs_div, abs_of_pos hτ, div_lt_one hτ]
      exact ht.trans_le hrτ
    have hWu := hWnear (show U (x,τ) ∈ Metric.ball (constCLM x₀) η from
      (hτnear x hx).2.trans_le hεη)
    have hWr := hWnear (show reparam (U (x,τ)) (t/τ) ∈ Metric.ball (constCLM x₀) η from
      (dist_reparam_const_le _ _ _).trans_lt ((hτnear x hx).2.trans_le hεη))
    have he := picard_rescale W V hWu hWr (hτnear x hx).1 hqt
    have hmul : τ * (t/τ) = t := by field_simp
    rw [hmul] at he
    have hev : U (x,t) = reparam (U (x,τ)) (t/τ) := by
      apply huniq (a := ((x,t),reparam (U (x,τ)) (t/τ))) _ he
      simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      exact ⟨⟨(hx.trans_le hrε).trans_le hε₀le, (ht.trans_le hrε).trans_le hε₀le⟩,
        (dist_reparam_const_le _ _ _).trans_lt ((hτnear x hx).2.trans_le hε₀le)⟩
    simp [f, hev, e]
  refine ⟨f,hf,?_⟩
  filter_upwards [Metric.ball_mem_nhds (x₀,(0:ℝ)) hr] with p hp
  have hp' : dist p.1 x₀ < r ∧ |p.2| < r := by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using hp
  have hint : p.2/τ ∈ Ioo (-1 : ℝ) 1 := by
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hτ, div_lt_one hτ]
    exact hp'.2.trans_le hrτ
  constructor
  · rw [hrep p.1 0 hp'.1 (by simpa using hr), zero_div]
    exact picard_initial W (hτnear p.1 hp'.1).1
  · have hd := (picard_derivative W (hτnear p.1 hp'.1).1 hint).scomp p.2
        ((hasDerivAt_id p.2).div_const τ)
    have hder : HasDerivAt (fun t => extend (U (p.1,τ)) (t/τ)) (V (f p)) p.2 := by
      rw [hrep p.1 p.2 hp'.1 hp'.2]
      have hWu := hWnear (show U (p.1,τ) ∈ Metric.ball (constCLM x₀) η from
        (hτnear p.1 hp'.1).2.trans_le hεη)
      change ∀ s, W (U (p.1,τ)) s = V (U (p.1,τ) s) at hWu
      simpa [Function.comp_def, extend, hWu, smul_smul, ne_of_gt hτ] using hd
    apply hder.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hp'.2).1 (abs_lt.mp hp'.2).2] with t ht
    exact hrep p.1 t hp'.1 (abs_lt.mpr ht)

theorem exists_analytic_local_flow [CompleteSpace E] (W : Path E → Path E)
    (V : E → E) (x₀ : E) (hW : ∀ u s, W u s = V (u s))
    (hsmooth : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        f (p.1,0) = p.1 ∧ HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2 :=
  exists_analytic_local_flow_eventually W V x₀ (Filter.Eventually.of_forall hW) hsmooth

section PolynomialFields
variable {ι : Type uι} [Fintype ι]

noncomputable def coordinate (i : ι) : Path (ι → ℝ) →L[ℝ] Path ℝ :=
  ContinuousLinearMap.compLeftContinuous ℝ UnitInterval (ContinuousLinearMap.proj i)

omit [Fintype ι] in
@[simp] lemma coordinate_apply (i : ι) (u : Path (ι → ℝ)) (s : UnitInterval) :
    coordinate i u s = u s i := rfl

noncomputable def assemble : (ι → Path ℝ) →L[ℝ] Path (ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.pi
      map_add' := by intro u v; ext s i; rfl
      map_smul' := by intro c u; ext s i; rfl }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
      intro s
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
      intro i
      exact (u i).norm_coe_le_norm s |>.trans (norm_le_pi_norm u i))

@[simp] lemma assemble_apply (u : ι → Path ℝ) (s : UnitInterval) (i : ι) :
    assemble u s i = u i s := rfl

noncomputable def scalarPolynomial (p : MvPolynomial ι ℝ) (u : Path (ι → ℝ)) : Path ℝ :=
  MvPolynomial.eval₂ (algebraMap ℝ (Path ℝ)) (fun i => coordinate i u) p

omit [Fintype ι] in
lemma scalarPolynomial_eval (p : MvPolynomial ι ℝ) (u : Path (ι → ℝ)) (s : UnitInterval) :
    scalarPolynomial p u s = MvPolynomial.eval (u s) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [scalarPolynomial]
  | add p q hp hq => simpa [scalarPolynomial, MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    simpa [scalarPolynomial, MvPolynomial.eval₂_mul] using congrArg (· * u s i) hp

lemma contDiff_scalarPolynomial (p : MvPolynomial ι ℝ) :
    ContDiff ℝ ω (scalarPolynomial p) := by
  unfold scalarPolynomial
  induction p using MvPolynomial.induction_on with
  | C a => simpa [scalarPolynomial] using (contDiff_const : ContDiff ℝ ω (fun _ : Path (ι → ℝ) => algebraMap ℝ (Path ℝ) a))
  | add p q hp hq => simpa [scalarPolynomial, MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp =>
    simpa [scalarPolynomial, MvPolynomial.eval₂_mul] using hp.mul (coordinate i).contDiff

theorem polynomial_local_flow (P : ι → MvPolynomial ι ℝ) (x₀ : ι → ℝ) :
    ∃ f : (ι → ℝ) × ℝ → (ι → ℝ), ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), f (p.1,0) = p.1 ∧
        HasDerivAt (fun t => f (p.1,t)) (fun i => MvPolynomial.eval (f p) (P i)) p.2 := by
  let W : Path (ι → ℝ) → Path (ι → ℝ) := fun u => assemble (fun i => scalarPolynomial (P i) u)
  have hW : ContDiff ℝ ω W :=
    (assemble (ι := ι)).contDiff.comp (contDiff_pi.mpr (fun i => contDiff_scalarPolynomial (P i)))
  apply exists_analytic_local_flow W (fun x i => MvPolynomial.eval x (P i)) x₀
  · intro u s
    ext i
    exact scalarPolynomial_eval (P i) u s
  · exact hW.contDiffAt

end PolynomialFields

inductive RationalExpr (ι : Type uι) where
  | const : ℝ → RationalExpr ι
  | coord : ι → RationalExpr ι
  | add : RationalExpr ι → RationalExpr ι → RationalExpr ι
  | mul : RationalExpr ι → RationalExpr ι → RationalExpr ι
  | inv : RationalExpr ι → RationalExpr ι

namespace RationalExpr
variable {ι : Type uι} [Fintype ι]

noncomputable def eval : RationalExpr ι → (ι → ℝ) → ℝ
  | const a, _ => a
  | coord i, x => x i
  | add p q, x => eval p x+eval q x
  | mul p q, x => eval p x*eval q x
  | inv p, x => (eval p x)⁻¹

def RegularAt : RationalExpr ι → (ι → ℝ) → Prop
  | const _, _ => True
  | coord _, _ => True
  | add p q, x => RegularAt p x ∧ RegularAt q x
  | mul p q, x => RegularAt p x ∧ RegularAt q x
  | inv p, x => RegularAt p x ∧ eval p x ≠ 0

theorem eval_contDiffAt (p : RationalExpr ι) {x : ι → ℝ} (hp : p.RegularAt x) :
    ContDiffAt ℝ ω p.eval x := by
  induction p with
  | const a => exact contDiffAt_const
  | coord i => exact (contDiff_apply ℝ ℝ i).contDiffAt
  | add p q ihp ihq => exact (ihp hp.1).add (ihq hp.2)
  | mul p q ihp ihq => exact (ihp hp.1).mul (ihq hp.2)
  | inv p ih => exact (ih hp.1).inv hp.2

theorem regular_eventually (p : RationalExpr ι) {x : ι → ℝ} (hp : p.RegularAt x) :
    ∀ᶠ y in 𝓝 x, p.RegularAt y := by
  induction p with
  | const a => exact Filter.Eventually.of_forall (fun _ => trivial)
  | coord i => exact Filter.Eventually.of_forall (fun _ => trivial)
  | add p q ihp ihq => exact (ihp hp.1).and (ihq hp.2)
  | mul p q ihp ihq => exact (ihp hp.1).and (ihq hp.2)
  | inv p ih => exact (ih hp.1).and ((p.eval_contDiffAt hp.1).continuousAt.eventually_ne hp.2)

theorem regular_isOpen (p : RationalExpr ι) : IsOpen {x | p.RegularAt x} :=
  isOpen_iff_mem_nhds.mpr (fun _ hx => p.regular_eventually hx)

noncomputable def onPaths : RationalExpr ι → Path (ι → ℝ) → Path ℝ
  | const a, _ => constCLM a
  | coord i, u => coordinate i u
  | add p q, u => onPaths p u+onPaths q u
  | mul p q, u => onPaths p u*onPaths q u
  | inv p, u => Ring.inverse (onPaths p u)

lemma inverse_eval (u : Path ℝ) (hu : IsUnit u) (s : UnitInterval) :
    (Ring.inverse u) s = (u s)⁻¹ := by
  have he := congrArg (fun v : Path ℝ => v s) (Ring.inverse_mul_cancel u hu)
  change (Ring.inverse u) s * u s = 1 at he
  have hne := (u.isUnit_iff_forall_ne_zero.mp hu) s
  apply (mul_right_cancel₀ hne)
  rw [he,inv_mul_cancel₀ hne]

theorem path_properties (p : RationalExpr ι) {x : ι → ℝ} (hp : p.RegularAt x) :
    onPaths p (constCLM x) = constCLM (p.eval x) ∧
    ContDiffAt ℝ ω (onPaths p) (constCLM x) ∧
    ∀ᶠ u in 𝓝 (constCLM x), ∀ s, onPaths p u s = p.eval (u s) := by
  induction p with
  | const a => exact ⟨rfl,contDiffAt_const,Filter.Eventually.of_forall (fun _ _ => rfl)⟩
  | coord i => exact ⟨rfl,(coordinate i).contDiff.contDiffAt,Filter.Eventually.of_forall (fun _ _ => rfl)⟩
  | add p q ihp ihq =>
    obtain ⟨hp0,hpc,hpe⟩ := ihp hp.1
    obtain ⟨hq0,hqc,hqe⟩ := ihq hp.2
    refine ⟨?_,hpc.add hqc,?_⟩
    · simp only [onPaths,hp0,hq0]; ext s; rfl
    · filter_upwards [hpe,hqe] with u hu hv s
      exact congrArg₂ (·+·) (hu s) (hv s)
  | mul p q ihp ihq =>
    obtain ⟨hp0,hpc,hpe⟩ := ihp hp.1
    obtain ⟨hq0,hqc,hqe⟩ := ihq hp.2
    refine ⟨?_,hpc.mul hqc,?_⟩
    · simp only [onPaths,hp0,hq0]; ext s; rfl
    · filter_upwards [hpe,hqe] with u hu hv s
      exact congrArg₂ (·*·) (hu s) (hv s)
  | inv p ih =>
    obtain ⟨hp0,hpc,hpe⟩ := ih hp.1
    have hunit : IsUnit (onPaths p (constCLM x)) := by
      rw [hp0]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr (fun _ => hp.2)
    have hinv : ContDiffAt ℝ ω Ring.inverse (onPaths p (constCLM x)) := by
      have hh := contDiffAt_ringInverse ℝ (n := ω) hunit.unit
      rw [hunit.unit_spec] at hh
      exact hh
    refine ⟨?_,hinv.comp _ hpc,?_⟩
    · ext s
      rw [onPaths,inverse_eval _ hunit,hp0]
      rfl
    · have hu : ∀ᶠ u in 𝓝 (constCLM x), IsUnit (onPaths p u) :=
        hpc.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
      filter_upwards [hpe,hu] with u he hunit s
      rw [onPaths,inverse_eval _ hunit,he s]
      rfl

theorem local_flow (P : ι → RationalExpr ι) (x₀ : ι → ℝ)
    (hP : ∀ i, (P i).RegularAt x₀) :
    ∃ f : (ι → ℝ) × ℝ → (ι → ℝ), ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), f (p.1,0) = p.1 ∧
        HasDerivAt (fun t => f (p.1,t)) (fun i => (P i).eval (f p)) p.2 := by
  let W : Path (ι → ℝ) → Path (ι → ℝ) := fun u => assemble (fun i => onPaths (P i) u)
  have hW : ContDiffAt ℝ ω W (constCLM x₀) :=
    (assemble (ι := ι)).contDiff.contDiffAt.comp _
      (contDiffAt_pi.mpr (fun i => (path_properties (P i) (hP i)).2.1))
  apply exists_analytic_local_flow_eventually W (fun x i => (P i).eval x) x₀ _ hW
  have he : ∀ᶠ u in 𝓝 (constCLM x₀), ∀ i, ∀ s, onPaths (P i) u s = (P i).eval (u s) :=
    (Filter.eventually_all).mpr (fun i => (path_properties (P i) (hP i)).2.2)
  filter_upwards [he] with u hu s
  ext i
  exact hu i s

end RationalExpr

end QuinticLienard.SmoothFlow

end OAI
