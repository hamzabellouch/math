import OAI.Geometry.ProjectionBodies.FixedPointCalculus

namespace OAI

universe uE

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiffAt_rayRetraction {f : E → E} {x : E} (hf : ContDiffAt ℝ 1 f x)
    (hc : ‖f x‖<1) (hne : x≠f x) :
    ContDiffAt ℝ 1 (fun y => rayRetraction (f y) y) x := by
  have hv : ContDiffAt ℝ 1 (fun y => y-f y) x := contDiffAt_id.sub hf
  have ha : ContDiffAt ℝ 1 (fun y => ‖y-f y‖^2) x := hv.norm_sq (𝕜 := ℝ)
  have hb : ContDiffAt ℝ 1 (fun y => ⟪f y,y-f y⟫) x := hf.inner ℝ hv
  have hc2 : ContDiffAt ℝ 1 (fun y => ‖f y‖^2) x := hf.norm_sq (𝕜 := ℝ)
  have ha0 : 0<‖x-f x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hcc : ‖f x‖^2<1 := by nlinarith [norm_nonneg (f x)]
  have hd0 : 0<⟪f x,x-f x⟫^2+‖x-f x‖^2*(1-‖f x‖^2) := by
    nlinarith [sq_nonneg ⟪f x,x-f x⟫]
  have hroot := (((hb.pow 2).add (ha.mul (contDiffAt_const.sub hc2))).sqrt
    (ne_of_gt hd0)).sub hb
  have ht := hroot.div ha (ne_of_gt ha0)
  exact hf.add (ht.smul hv)

lemma smooth_fixedPoint_ball [FiniteDimensional ℝ E] {f : E → E}
    (hf : ContDiff ℝ 1 f) (hb : ∀ x∈closedBall (0:E) 1, ‖f x‖<1) :
    ∃ x∈closedBall (0:E) 1, f x=x := by
  by_contra h
  have hne (x : E) (hx : x∈closedBall (0:E) 1) : x≠f x := by
    intro he
    exact h ⟨x,hx,he.symm⟩
  let r : E → E := fun x => rayRetraction (f x) x
  have hr (x : E) (hx : x∈closedBall (0:E) 1) : ContDiffAt ℝ 1 r x :=
    contDiffAt_rayRetraction hf.contDiffAt (hb x hx) (hne x hx)
  borelize E
  apply no_smooth_retraction (.addHaar : Measure E)
    (r' := fderiv ℝ r)
    (fun x hx => ((hr x hx).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => ((hr x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  · intro x hx
    exact rayRetraction_norm (hb x hx) (hne x hx)
  · intro x hx
    exact rayRetraction_boundary (hb x (by simpa only [mem_closedBall,dist_zero_right,hx] using le_rfl (a := (1:ℝ)))) hx

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Topology
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E]
section Approximation
variable [NormedSpace ℝ E]

lemma scaled_approximation {u v : E} {ε : ℝ} (hε : 0<ε) (hv : ‖v‖≤1)
    (huv : dist u v<ε) :
    ‖(1+ε)⁻¹ • u‖<1 ∧ dist ((1+ε)⁻¹ • u) v<2*ε := by
  let a : ℝ := (1+ε)⁻¹
  have hden : 0<1+ε := by linarith
  have ha : 0<a := inv_pos.mpr hden
  have hae : a*(1+ε)=1 := inv_mul_cancel₀ (ne_of_gt hden)
  have ha1 : a≤1 := by nlinarith
  have hae2 : 1-a≤ε := by nlinarith
  have hua : ‖u‖<1+ε := by
    have hh := norm_le_norm_add_norm_sub v u
    rw [← dist_eq_norm,dist_comm v u] at hh
    linarith
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    nlinarith
  · have ht : dist (a • u) (a • v) < ε := by
      rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos ha]
      nlinarith [dist_nonneg (x := u) (y := v)]
    have hs : dist (a • v) v≤ε := by
      rw [dist_eq_norm]
      have he : a • v-v=(a-1) • v := by rw [sub_smul,one_smul]
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr ha1)]
      nlinarith [norm_nonneg v]
    have htri := dist_triangle (a • u) (a • v) v
    change dist (a • u) v<2*ε
    linarith

end Approximation

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma uniformlyContinuous_ball_extension {f : E → E}
    (hf : ContinuousOn f (closedBall (0:E) 1)) :
    UniformContinuous (fun x => f (ballNearest x)) := by
  let : CompactSpace (closedBall (0:E) 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hfc : Continuous (fun x : closedBall (0:E) 1 => f x) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  have hp : UniformContinuous (fun x : E => (⟨ballNearest x,ballNearest_mem x⟩ : closedBall (0:E) 1)) :=
    ballNearest_lipschitz.uniformContinuous.subtype_mk _
  exact (CompactSpace.uniformContinuous_of_continuous hfc).comp hp

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Topology
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full continuous finite-dimensional unit-ball fixed-point theorem,
obtained from polynomial Jacobian integration, not from a topological axiom. -/
lemma fixedPoint_unitBall {f : E → E} (hf : ContinuousOn f (closedBall (0:E) 1))
    (hball : MapsTo f (closedBall (0:E) 1) (closedBall (0:E) 1)) :
    ∃ x∈closedBall (0:E) 1, f x=x := by
  by_contra hfix
  have hgap : ContinuousOn (fun x => ‖f x-x‖) (closedBall (0:E) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀,hx₀,hmin⟩ := (isCompact_closedBall (0:E) 1).exists_isMinOn
    (nonempty_closedBall.mpr (by norm_num)) hgap
  let δ : ℝ := ‖f x₀-x₀‖
  have hδ : 0<δ := by
    apply norm_pos_iff.mpr
    intro he
    exact hfix ⟨x₀,hx₀,sub_eq_zero.mp he⟩
  let ε : ℝ := δ/4
  have hε : 0<ε := div_pos hδ (by norm_num)
  obtain ⟨g,hg,hga⟩ := (uniformlyContinuous_ball_extension hf).exists_contDiff_dist_le hε
  have happ (x : E) (hx : x∈closedBall (0:E) 1) : dist (g x) (f x)<ε := by
    have he : ballNearest x=x := ballNearest_eq
      (by simpa only [mem_closedBall,dist_zero_right] using hx)
    simpa only [he] using hga x
  have hn (x : E) (hx : x∈closedBall (0:E) 1) : ‖f x‖≤1 := by
    simpa only [mem_closedBall,dist_zero_right] using hball hx
  let q : E → E := fun x => (1+ε)⁻¹ • g x
  have hq : ContDiff ℝ 1 q := (hg.of_le (by norm_num)).const_smul _
  have hqb (x : E) (hx : x∈closedBall (0:E) 1) : ‖q x‖<1 :=
    (scaled_approximation hε (hn x hx) (happ x hx)).1
  obtain ⟨x,hx,hqx⟩ := smooth_fixedPoint_ball hq hqb
  have hdist := (scaled_approximation hε (hn x hx) (happ x hx)).2
  change dist (q x) (f x)<2*ε at hdist
  rw [hqx,dist_eq_norm,norm_sub_rev] at hdist
  have hh : δ≤‖f x-x‖ := hmin hx
  dsimp [ε] at hdist
  linarith

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Topology
namespace PettyProjection.FixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Brouwer on any nonempty compact convex set, derived from the genuine
unit-ball theorem by the nearest-point extension. -/
theorem fixedPoint_compact_convex {K : Set E} (hne : K.Nonempty)
    (hk : IsCompact K) (hc : Convex ℝ K) {f : E → E}
    (hf : ContinuousOn f K) (hmap : MapsTo f K K) : ∃ x∈K, f x=x := by
  obtain ⟨R,hR,hbound⟩ := hk.isBounded.exists_pos_norm_le
  let p : E → E := nearest K hne hk.isComplete hc
  have hp (x : E) : p x∈K := nearest_mem K hne hk.isComplete hc x
  have hpc : Continuous p := (nearest_lipschitz K hne hk.isComplete hc).continuous
  let F : E → E := fun x => R⁻¹ • f (p (R • x))
  have hFc : Continuous F := by
    apply Continuous.const_smul
    exact hf.comp_continuous (hpc.comp (continuous_const.smul continuous_id)) (fun x => hp _)
  have hFB : MapsTo F (closedBall (0:E) 1) (closedBall (0:E) 1) := by
    intro x hx
    rw [mem_closedBall,dist_zero_right]
    change ‖R⁻¹ • f (p (R • x))‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hbound _ (hmap (hp _)))
  obtain ⟨x,_,hfix⟩ := fixedPoint_unitBall hFc.continuousOn hFB
  have he : f (p (R • x))=R • x := by
    have hh := congrArg (fun y : E => R • y) hfix
    simpa only [F,smul_smul,mul_inv_cancel₀ hR.ne',one_smul] using hh
  have hxK : R • x∈K := he ▸ hmap (hp _)
  refine ⟨R • x,hxK,?_⟩
  have hpfix : p (R • x)=R • x := nearest_eq_of_mem K hne hk.isComplete hc hxK
  rwa [hpfix] at he

end PettyProjection.FixedPoint
end

end OAI
