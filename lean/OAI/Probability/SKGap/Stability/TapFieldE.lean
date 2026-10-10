import Mathlib
import OAI.Probability.SKGap.Localization.AttractionBasinIUnion

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientRoots
open Set Function Filter Real
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_small_gradient_step {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ M*ε < 1 ∧ 2*ε*c ≤ 1 ∧ ε*M^2 < c := by
  have h1 : 0 < 1/(M+1) := by positivity
  have h2 : 0 < 1/(2*c+1) := by positivity
  have h3 : 0 < c/(M^2+1) := by positivity
  obtain ⟨ε, hε, he⟩ := exists_between
    (lt_min (by norm_num : (0:ℝ) < 1) (lt_min h1 (lt_min h2 h3)))
  have he1 := (lt_min_iff.mp he).1
  have he2 := (lt_min_iff.mp (lt_min_iff.mp he).2).1
  have he3 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).1
  have he4 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp he).2).2).2
  have hp2 := (lt_div_iff₀ (show 0 < M+1 by positivity)).mp he2
  have hp3 := (lt_div_iff₀ (show 0 < 2*c+1 by positivity)).mp he3
  have hp4 := (lt_div_iff₀ (show 0 < M^2+1 by positivity)).mp he4
  exact ⟨ε, hε, he1.le, by nlinarith, by nlinarith, by nlinarith⟩

lemma gradient_step_derivative_norm_lt {D : E →L[ℝ] E} {c M ε : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε)
    (hsmall0 : 2*ε*c ≤ 1) (hsmall1 : ε*M^2 < c)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M) :
    ‖ContinuousLinearMap.id ℝ E - ε • D‖ < 1 := by
  let k := 1-2*ε*c+ε^2*M^2
  have hk0 : 0 ≤ k := by dsimp [k]; nlinarith [sq_nonneg (ε*M)]
  have hk1 : k < 1 := by
    dsimp [k]
    have h := mul_lt_mul_of_pos_left hsmall1 hε
    nlinarith
  have hb : ‖ContinuousLinearMap.id ℝ E - ε • D‖ ≤ sqrt k := by
    refine (ContinuousLinearMap.id ℝ E - ε • D).opNorm_le_bound (sqrt_nonneg k) ?_
    intro v
    change ‖v-ε • D v‖ ≤ sqrt k * ‖v‖
    have h := gradient_step_derivative_sq_bound hc.le hM hε.le hcoercive hbound v
    have hp : 0 ≤ sqrt k*‖v‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    calc
      ‖v-ε • D v‖^2 ≤ k*‖v‖^2 := h
      _ = (sqrt k*‖v‖)^2 := by rw [mul_pow, sq_sqrt hk0]
  exact hb.trans_lt (by simpa using sqrt_lt_sqrt hk0 hk1)

theorem gradient_unique_zero_on_compact
    {φ : E → ℝ} {G : E → E} {s : Set E}
    (hcompact : IsCompact s) (hne : s.Nonempty) (hconv : Convex ℝ s)
    (hgrad : ∀ x, HasFDerivAt φ (innerSL ℝ (G x)) x)
    (hG : ContDiff ℝ 1 G)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ x ∈ s, G x = 0 → ∀ v, c*‖v‖^2 ≤ inner ℝ v (fderiv ℝ G x v))
    (hinvariant : ∀ ε ∈ Icc (0:ℝ) 1, MapsTo (fun x => x-ε • G x) s s) :
    ∃! x : s, G x = 0 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty s := hne.to_subtype
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp (hconv.isConnected hne)
  have hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖fderiv ℝ G x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image
      (hG.continuous_fderiv (by norm_num)).norm.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
    exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M, hM, hbound⟩ := hbound
  obtain ⟨ε, hε, hε1, hεM, hεc, hεM2⟩ := exists_small_gradient_step hc hM
  let L : ℝ≥0 := ⟨M, hM⟩
  have hLip : LipschitzOnWith L G s :=
    hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x _ => (hG.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx => by exact_mod_cast hbound x hx)
  let T : s → s := fun x => ⟨x.val-ε • G x.val, hinvariant ε ⟨hε.le,hε1⟩ x.property⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (continuous_const.smul (hG.continuous.comp continuous_subtype_val))
  let ψ : s → ℝ := fun x => φ x.val
  have hψ : Continuous ψ :=
    (continuous_iff_continuousAt.mpr fun x => (hgrad x).continuousAt).comp continuous_subtype_val
  have hzero (x : s) : T x = x ↔ G x.val = 0 := by
    rw [Subtype.ext_iff]
    change x.val-ε • G x.val = x.val ↔ G x.val = 0
    simp only [sub_eq_self, smul_eq_zero, hε.ne', false_or]
  have hstrict (x : s) (hx : T x ≠ x) : ψ (T x) < ψ x := by
    exact gradient_step_strict_descent hconv (fun x _ => hgrad x) hLip hε hεM
      x.property (T x).property (fun h => hx ((hzero x).mpr h))
  have hattract (p : s) (hp : T p = p) :
      ∃ U : Set s, IsOpen U ∧ p ∈ U ∧ U ⊆ attractionBasin T p := by
    let D := ContinuousLinearMap.id ℝ E - ε • fderiv ℝ G p.val
    have hD : HasStrictFDerivAt (fun x : E => x-ε • G x) D p.val :=
      (hasStrictFDerivAt_id p.val).sub
        ((hG.contDiffAt.hasStrictFDerivAt (by norm_num)).const_smul ε)
    have hDn : ‖D‖ < 1 := gradient_step_derivative_norm_lt hc hM hε hεc hεM2
      (hcoercive p.val p.property ((hzero p).mp hp)) (hbound p.val p.property)
    have hDnn : ‖D‖₊ < 1 := by exact_mod_cast hDn
    obtain ⟨K, hDK, hK⟩ := exists_between hDnn
    obtain ⟨U, hU, hULip⟩ := hD.exists_lipschitzOnWith_of_nnnorm_lt K hDK
    have hpre : Subtype.val ⁻¹' U ∈ 𝓝 p := continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hpreLip : LipschitzOnWith K T (Subtype.val ⁻¹' U) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      exact hULip.dist_le_mul x.val hx y.val hy
    exact local_contraction_attracts hp hK hpre hpreLip
  obtain ⟨p, hp, huniq⟩ := lyapunov_unique_fixed_point T hT ψ hψ hstrict hattract
  exact ⟨p, (hzero p).mp hp, fun q hq => huniq q ((hzero q).mpr hq)⟩

end GradientRoots

lemma weightedTapE_eq_zero_iff {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (y : EField n) :
    weightedTapE j J h y = 0 ↔ tapField j J h (WithLp.ofLp y) = 0 := by
  constructor
  · intro hz
    ext i
    have he := congrArg (fun z : EField n => z i) hz
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0 at he
    exact (mul_eq_zero.mp he).resolve_left (spinVariance_pos (WithLp.ofLp y) i).ne'
  · intro hz
    ext i
    change spinVariance (WithLp.ofLp y) i * tapField j J h (WithLp.ofLp y) i = 0
    rw [hz, Pi.zero_apply, mul_zero]

lemma weightedTapE_coercive_on_box {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) {R c : ℝ}
    (hR : 0 ≤ R) (hc : 0 ≤ c) (y : EField n) (hy : y ∈ fieldBoxE n R)
    (hz : tapField j J h (WithLp.ofLp y) = 0)
    (hH : ∀ x : Field n, c*vectorSqNorm x ≤
      quadraticForm (fieldHessian j J (WithLp.ofLp y) (spinVariance (WithLp.ofLp y))) x)
    (v : EField n) :
    (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
  rw [weightedTapE_derivative_energy j J h y v hz]
  have hV := spinVariance_bound_on_box (WithLp.ofLp y) hR ((mem_fieldBoxE hR y).mp hy)
  have hb : (1 / cosh R^2)*‖v‖^2 ≤ vectorSqNorm (sqrtVarianceMul (WithLp.ofLp y) (WithLp.ofLp v)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [vectorSqNorm, sqrtVarianceMul, Finset.mul_sum, mul_pow,
      sq_sqrt (spinVariance_pos _ _).le]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hV i) (sq_nonneg _)
  have h := (mul_le_mul_of_nonneg_left hb hc).trans (hH _)
  simpa only [mul_assoc, div_eq_mul_inv, one_mul] using h

theorem tap_unique_zero {n : ℕ} (hn : 0 < n) {j c : ℝ} (hj : 0 ≤ j) (hc : 0 < c)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsSymm) (h : Field n)
    (hH : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃! r : Field n, tapField j J h r = 0 := by
  obtain ⟨R, hR, hbound⟩ := exists_tapBox_radius hn hj J h
  have hco : ∀ y ∈ fieldBoxE n R, weightedTapE j J h y = 0 → ∀ v,
      (c / cosh R^2)*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (weightedTapE j J h) y v) := by
    intro y hy hz v
    have hz' := (weightedTapE_eq_zero_iff j J h y).mp hz
    exact weightedTapE_coercive_on_box j J h hR.le hc.le y hy hz' (hH _ hz') v
  have hmaps : ∀ ε ∈ Set.Icc (0:ℝ) 1,
      Set.MapsTo (fun y => y-ε • weightedTapE j J h y) (fieldBoxE n R) (fieldBoxE n R) := by
    intro ε hε y hy
    rw [mem_fieldBoxE hR.le] at hy ⊢
    exact weightedTap_step_box j J h (WithLp.ofLp y) hε (hbound _) hy
  obtain ⟨r, hr, huniq⟩ := gradient_unique_zero_on_compact
    (isCompact_fieldBoxE n R) (nonempty_fieldBoxE n hR.le) (convex_fieldBoxE n R)
    (tapPotentialE_hasFDerivAt j hJ h) (weightedTapE_contDiff j J h)
    (show 0 < c / cosh R^2 by positivity) hco hmaps
  refine ⟨WithLp.ofLp r.val, (weightedTapE_eq_zero_iff j J h r.val).mp hr, ?_⟩
  intro y hy
  have hys : WithLp.toLp 2 y ∈ fieldBoxE n R := by
    rw [mem_fieldBoxE hR.le]
    intro i
    have hb := hbound y i
    simpa only [hy, Pi.zero_apply, sub_zero] using hb
  have hye : weightedTapE j J h (WithLp.toLp 2 y) = 0 :=
    (weightedTapE_eq_zero_iff j J h (WithLp.toLp 2 y)).mpr hy
  have he := congrArg (fun z : fieldBoxE n R => WithLp.ofLp z.val)
    (huniq ⟨WithLp.toLp 2 y, hys⟩ hye)
  exact he

theorem inverseOnConvex_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → E} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiff ℝ 1 f)
    (hunique : ∀ z ∈ U, ∃! y, f y = z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, f y ∈ U → ∀ v, ‖v‖ ≤ C * ‖fderiv ℝ f y v‖)
    {x y : E} (hx : f x ∈ U) (hy : f y ∈ U) :
    ‖y-x‖ ≤ C * ‖f y-f x‖ := by
  classical
  let g : E → E := fun z => if hz : z ∈ U then (hunique z hz).choose else 0
  have hg (z : E) (hz : z ∈ U) : f (g z) = z := by
    simp only [g, dite_eq_left hz]
    exact (hunique z hz).choose_spec.1
  have hgf (z : E) (hz : f z ∈ U) : g (f z) = z := by
    simp only [g, dite_eq_left hz]
    exact ((hunique (f z) hz).choose_spec.2 z rfl).symm
  have hinj (z : E) (hz : f z ∈ U) : Function.Injective (fderiv ℝ f z) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := hbound z hz (a-b)
    rw [map_sub, hab, sub_self, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let D (z : E) : E →L[ℝ] E := fderiv ℝ f z
  let e (z : E) (hz : f z ∈ U) : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (D z).toLinearMap (hinj z hz)).toContinuousLinearEquiv
  have he (z : E) (hz : f z ∈ U) : (e z hz : E →L[ℝ] E) = D z := by
    ext v
    rfl
  have hgder (z : E) (hz : z ∈ U) :
      HasFDerivAt g ((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E) z := by
    let p := g z
    have hp : f p = z := hg z hz
    have hpU : f p ∈ U := hp ▸ hz
    have hder : HasStrictFDerivAt f (e p hpU : E →L[ℝ] E) p := by
      rw [he p hpU]
      exact hf.contDiffAt.hasStrictFDerivAt (by norm_num)
    have hleft : ∀ᶠ w in 𝓝 p, g (f w) = w := by
      filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with w hw
      exact hgf w hw
    have H := (hder.to_local_left_inverse hleft).hasFDerivAt
    simpa only [hp] using H
  have hnorm (z : E) (hz : z ∈ U) :
      ‖((e (g z) (by rw [hg z hz]; exact hz)).symm : E →L[ℝ] E)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    have hh := hbound (g z) (by rw [hg z hz]; exact hz)
      ((e (g z) (by rw [hg z hz]; exact hz)).symm v)
    change ‖_‖ ≤ C*‖D (g z) _‖ at hh
    rw [← he (g z) (by rw [hg z hz]; exact hz)] at hh
    simpa using hh
  have hd : DifferentiableOn ℝ g U := fun z hz => (hgder z hz).differentiableAt.differentiableWithinAt
  have hn : ∀ z ∈ U, ‖fderivWithin ℝ g U z‖ ≤ C := by
    intro z hz
    rw [(hgder z hz).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffWithinAt hz)]
    exact hnorm z hz
  have H := hconv.norm_image_sub_le_of_norm_fderivWithin_le hd hn hx hy
  simpa only [hgf x hx, hgf y hy] using H

def tapFieldE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : EField n :=
  WithLp.toLp 2 (tapField j J h (WithLp.ofLp y))

lemma tapFieldE_contDiff {n : ℕ} {m : WithTop ℕ∞} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : ContDiff ℝ m (tapFieldE j J h) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm.contDiff.comp
    ((tapField_contDiff j J h).comp
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).contDiff)

lemma norm_EField_eq {n : ℕ} (v : EField n) : ‖v‖ = vectorNorm (WithLp.ofLp v) := by
  simp only [EuclideanSpace.norm_eq, vectorNorm, Real.norm_eq_abs, sq_abs]

lemma tapFieldE_fderiv {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y v : EField n) :
    fderiv ℝ (tapFieldE j J h) y v =
      WithLp.toLp 2 ((fieldJacobian j J (WithLp.ofLp y)).mulVec (WithLp.ofLp v)) := by
  let e := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hd := e.symm.hasFDerivAt.comp y
    ((tapField_hasFDerivAt j J h (WithLp.ofLp y)).comp y e.hasFDerivAt)
  change HasFDerivAt (tapFieldE j J h) _ y at hd
  rw [hd.fderiv]
  rfl

lemma vectorNorm_zero (n : ℕ) : vectorNorm (0 : Field n) = 0 := by
  simp [vectorNorm]

lemma tapField_shift {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h z y : Field n) : tapField j J (h+z) y = tapField j J h y-z := by
  ext i
  simp only [tapField, Pi.add_apply, Pi.sub_apply]
  ring

theorem tap_root_and_distance {n : ℕ} (hn : 0 < n) {j K c R : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hc : 0 < c) (hR : 0 < R)
    {J : Matrix (Fin n) (Fin n) ℝ} (hJsymm : J.IsSymm) (h : Field n)
    (hJ : ∀ z : Field n, vectorNorm (J.mulVec z) ≤ K*vectorNorm z)
    (hH : ∀ y : Field n, vectorNorm (tapField j J h y) ≤ R → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x) :
    ∃ r : Field n, tapField j J h r = 0 ∧
      (∀ y, tapField j J h y = 0 → y = r) ∧
      ∀ y, vectorNorm (tapField j J h y) < R →
        vectorNorm (y-r) ≤ (1+(K+3*j)/c)*vectorNorm (tapField j J h y) := by
  have hH0 : ∀ y : Field n, tapField j J h y = 0 → ∀ x : Field n,
      c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J y (spinVariance y)) x := by
    intro y hy
    apply hH y
    simpa only [hy, vectorNorm_zero] using hR.le
  obtain ⟨r, hr, huniq⟩ := tap_unique_zero hn hj hc hJsymm h hH0
  refine ⟨r, hr, huniq, ?_⟩
  intro y hy
  let F := tapFieldE j J h
  let U := Metric.ball (0 : EField n) R
  have hmem (v : EField n) : F v ∈ U ↔ vectorNorm (tapField j J h (WithLp.ofLp v)) < R := by
    simp only [U, Metric.mem_ball, dist_zero_right, F, norm_EField_eq, tapFieldE]
  have hsurj : ∀ z ∈ U, ∃! v, F v = z := by
    intro z hz
    have hzn : vectorNorm (WithLp.ofLp z) < R := by
      simpa only [U, Metric.mem_ball, dist_zero_right, norm_EField_eq] using hz
    have hHz : ∀ v : Field n, tapField j J (h+WithLp.ofLp z) v = 0 → ∀ x : Field n,
        c*vectorSqNorm x ≤ quadraticForm (fieldHessian j J v (spinVariance v)) x := by
      intro v hv
      rw [tapField_shift, sub_eq_zero] at hv
      exact hH v (by rw [hv]; exact hzn.le)
    obtain ⟨v, hv, huv⟩ := tap_unique_zero hn hj hc hJsymm (h+WithLp.ofLp z) hHz
    have hv' : tapField j J h v = WithLp.ofLp z := by
      simpa only [tapField_shift, sub_eq_zero] using hv
    refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
    · change WithLp.toLp 2 (tapField j J h v) = z
      rw [hv', WithLp.toLp_ofLp]
    · intro w hw
      apply (WithLp.ofLp_injective 2)
      apply huv
      rw [tapField_shift, sub_eq_zero]
      exact congrArg WithLp.ofLp hw
  have hbound : ∀ v, F v ∈ U → ∀ w, ‖w‖ ≤ (1+(K+3*j)/c)*‖fderiv ℝ F v w‖ := by
    intro v hv w
    rw [tapFieldE_fderiv, norm_EField_eq, norm_EField_eq]
    exact fieldJacobian_inverse_bound hn hc hj hK J (WithLp.ofLp v) (WithLp.ofLp w)
      hJ (hH _ ((hmem v).mp hv).le)
  have hrmem : F (WithLp.toLp 2 r) ∈ U := by
    rw [hmem]
    simpa only [WithLp.ofLp_toLp, hr, vectorNorm_zero] using hR
  have hymem : F (WithLp.toLp 2 y) ∈ U := (hmem _).mpr hy
  have H := inverseOnConvex_bound Metric.isOpen_ball (convex_ball _ _) (tapFieldE_contDiff j J h)
    hsurj (show 0 ≤ 1+(K+3*j)/c by positivity) hbound hrmem hymem
  simpa only [norm_EField_eq, WithLp.ofLp_sub, WithLp.ofLp_toLp, F, tapFieldE, hr,
    sub_zero, WithLp.toLp_zero] using H

end SKGap

end
end
end

end OAI
