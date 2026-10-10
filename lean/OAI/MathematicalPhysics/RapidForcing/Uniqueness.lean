import OAI.MathematicalPhysics.RapidForcing.CurlDerivatives

namespace OAI

section
open scoped BigOperators ENNReal Topology NNReal InnerProductSpace
open Set MeasureTheory
namespace RapidForcing

noncomputable def spaceD {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) : Space → E := fun x => fderiv ℝ f x (basis i)

lemma spaceD_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Space → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin 3) :
    spaceD i (fun x => f x - g x) = fun x => spaceD i f x - spaceD i g x := by
  funext x
  simp [spaceD, fderiv_fun_sub (hf x) (hg x)]

lemma spaceD_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ 2 f) (i : Fin 3) : ContDiff ℝ 1 (spaceD i f) := by
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

lemma spaceD_coordinate {f : Space → Space} (hf : Differentiable ℝ f) (i j : Fin 3)
    (x : Space) : spaceD i (fun x => f x j) x = spaceD i f x j :=
  fderiv_coordinate (hf x) j (basis i)

lemma spaceD_smul {a : Space → ℝ} {f : Space → Space}
    (ha : Differentiable ℝ a) (hf : Differentiable ℝ f) (i : Fin 3) (x : Space) :
    spaceD i (fun x => a x • f x) x =
      spaceD i a x • f x + a x • spaceD i f x := by
  simp [spaceD, fderiv_fun_smul (ha x) (hf x), add_comm]

lemma memLp_coordinate {f : Space → Space} (hf : MemLp f 2 volume) (i : Fin 3) :
    MemLp (fun x => f x i) 2 volume := by
  exact hf.continuousLinearMap_comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)

lemma memLp_inner_integrable {f g : Space → Space}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) volume := by
  apply (L2.integrable_inner (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

lemma memLp_mul_integrable {f g : Space → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * g x) volume := by
  have h : MemLp (fun x => f x * g x) 1 volume := hf.fun_mul hg
  exact memLp_one_iff_integrable.mp h

lemma memLp_smul_bounded {a : Space → ℝ} {f : Space → Space}
    (ha : Continuous a) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C) (hf : MemLp f 2 volume) :
    MemLp (fun x => a x • f x) 2 volume := by
  apply hf.of_le_mul (ha.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => (norm_smul _ _).le.trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

lemma memLp_smul_l2_bounded {a : Space → ℝ} {f : Space → Space}
    (ha : MemLp a 2 volume) (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    MemLp (fun x => a x • f x) 2 volume := by
  apply ha.of_le_mul (ha.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖a x • f x‖ ≤ C * ‖a x‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

lemma integral_inner_spaceD {f g : Space → Space}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin 3)
    (hf0 : MemLp f 2 volume) (hg0 : MemLp g 2 volume)
    (hf1 : MemLp (spaceD i f) 2 volume) (hg1 : MemLp (spaceD i g) 2 volume) :
    (∫ x, ⟪f x, spaceD i g x⟫_ℝ) = - ∫ x, ⟪spaceD i f x, g x⟫_ℝ := by
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    (memLp_inner_integrable hf1 hg0) (memLp_inner_integrable hf0 hg1)
    (memLp_inner_integrable hf0 hg0) (fun x _ => hf x) (fun x _ => hg x)

lemma integral_mul_spaceD {f g : Space → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin 3)
    (hf0 : MemLp f 2 volume) (hg0 : MemLp g 2 volume)
    (hf1 : MemLp (spaceD i f) 2 volume) (hg1 : MemLp (spaceD i g) 2 volume) :
    (∫ x, f x * spaceD i g x) = - ∫ x, spaceD i f x * g x := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (memLp_mul_integrable hf1 hg0) (memLp_mul_integrable hf0 hg1)
    (memLp_mul_integrable hf0 hg0) (fun x _ => hf x) (fun x _ => hg x)

lemma inner_basis (x : Space) (i : Fin 3) : ⟪x, basis i⟫_ℝ = x i := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, basis, dotProduct]

lemma inner_basis_left (x : Space) (i : Fin 3) : ⟪basis i, x⟫_ℝ = x i := by
  rw [real_inner_comm, inner_basis]

lemma sum_basis (x : Space) : ∑ i, x i • basis i = x := by
  ext j
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma spaceD_sum (f : Space → Space) (x v : Space) :
    ∑ i, v i • spaceD i f x = fderiv ℝ f x v := by
  calc
    _ = fderiv ℝ f x (∑ i, v i • basis i) := by simp [map_smul, spaceD]
    _ = _ := by rw [sum_basis]

lemma integral_laplace_dissipation {f : Space → Space}
    (hf : ContDiff ℝ 2 f) (hf0 : MemLp f 2 volume)
    (hf1 : ∀ i, MemLp (spaceD i f) 2 volume)
    (hf2 : ∀ i, MemLp (spaceD i (spaceD i f)) 2 volume) :
    (∫ x, ⟪f x, ∑ i, spaceD i (spaceD i f) x⟫_ℝ) ≤ 0 := by
  simp_rw [inner_sum]
  rw [integral_finsetSum _ (fun i _ => memLp_inner_integrable hf0 (hf2 i))]
  apply Finset.sum_nonpos
  intro i _
  rw [integral_inner_spaceD (hf.differentiable (by norm_num))
    ((spaceD_contDiff hf i).differentiable (by norm_num)) i hf0 (hf1 i) (hf1 i) (hf2 i)]
  exact neg_nonpos.mpr (integral_nonneg (fun x => real_inner_self_nonneg))

lemma integral_pressure_orthogonal {w : Space → Space} {q : Space → ℝ}
    (hw : Differentiable ℝ w) (hq : Differentiable ℝ q)
    (hw0 : MemLp w 2 volume) (hq0 : MemLp q 2 volume)
    (hw1 : ∀ i, MemLp (spaceD i w) 2 volume)
    (hq1 : ∀ i, MemLp (spaceD i q) 2 volume)
    (hdiv : ∀ x, ∑ i, spaceD i w x i = 0) :
    (∫ x, ⟪w x, ∑ i, spaceD i q x • basis i⟫_ℝ) = 0 := by
  have hwi (i : Fin 3) : Differentiable ℝ (fun x => w x i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).differentiable.comp hw
  have hwdi (i : Fin 3) : MemLp (spaceD i (fun x => w x i)) 2 volume := by
    simpa only [funext (spaceD_coordinate hw i i)] using memLp_coordinate (hw1 i) i
  have hprod (i : Fin 3) : Integrable (fun x => spaceD i (fun x => w x i) x * q x) :=
    memLp_mul_integrable (hwdi i) hq0
  simp_rw [inner_sum, inner_smul_right, inner_basis, mul_comm (spaceD _ q _) (w _ _)]
  rw [integral_finsetSum _ (fun i _ => memLp_mul_integrable (memLp_coordinate hw0 i) (hq1 i))]
  simp_rw [integral_mul_spaceD (hwi _) hq _ (memLp_coordinate hw0 _) hq0 (hwdi _) (hq1 _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hprod i)]
  have hz : (fun x => ∑ i, spaceD i (fun x => w x i) x * q x) = fun _ => 0 := by
    funext x
    simp only [spaceD_coordinate hw, ← Finset.sum_mul, hdiv x, zero_mul]
  rw [hz, integral_zero, neg_zero]

lemma integral_transport_zero {v w : Space → Space}
    (hv : Differentiable ℝ v) (hw : Differentiable ℝ w)
    (hw0 : MemLp w 2 volume)
    (hv1 : ∀ i, MemLp (spaceD i v) 2 volume)
    (hw1 : ∀ i, MemLp (spaceD i w) 2 volume)
    {C D : ℝ} (hbv : ∀ x, ‖v x‖ ≤ C) (hbw : ∀ x, ‖w x‖ ≤ D)
    (hdiv : ∀ x, ∑ i, spaceD i v x i = 0) :
    (∫ x, ⟪w x, ∑ i, v x i • spaceD i w x⟫_ℝ) = 0 := by
  have hvi (i : Fin 3) : Differentiable ℝ (fun x => v x i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).differentiable.comp hv
  have hbvi (i : Fin 3) (x : Space) : ‖v x i‖ ≤ C :=
    (PiLp.norm_apply_le _ _).trans (hbv x)
  have hA (i : Fin 3) : MemLp (fun x => v x i • w x) 2 volume :=
    memLp_smul_bounded (hvi i).continuous (hbvi i) hw0
  have hB (i : Fin 3) : MemLp (fun x => spaceD i v x i • w x) 2 volume :=
    memLp_smul_l2_bounded (memLp_coordinate (hv1 i) i) hw.continuous hbw
  have hE (i : Fin 3) : MemLp (fun x => v x i • spaceD i w x) 2 volume :=
    memLp_smul_bounded (hvi i).continuous (hbvi i) (hw1 i)
  have hdA (i : Fin 3) : MemLp (spaceD i (fun x => v x i • w x)) 2 volume := by
    have he : spaceD i (fun x => v x i • w x) =
        fun x => spaceD i v x i • w x + v x i • spaceD i w x := by
      funext x
      rw [spaceD_smul (hvi i) hw, spaceD_coordinate hv]
    rw [he]
    exact (hB i).add (hE i)
  let I : Fin 3 → ℝ := fun i => ∫ x, ⟪w x, v x i • spaceD i w x⟫_ℝ
  let J : Fin 3 → ℝ := fun i => ∫ x, ⟪spaceD i v x i • w x, w x⟫_ℝ
  have he (i : Fin 3) : I i = -(J i + I i) := by
    have h := integral_inner_spaceD (f := fun x => v x i • w x) ((hvi i).smul hw) hw i (hA i) hw0 (hdA i) (hw1 i)
    have hleft : (fun x => ⟪v x i • w x, spaceD i w x⟫_ℝ) =
        fun x => ⟪w x, v x i • spaceD i w x⟫_ℝ := by
      funext x
      simp only [real_inner_smul_left, inner_smul_right]
    rw [hleft] at h
    have hright : (fun x => ⟪spaceD i (fun x => v x i • w x) x, w x⟫_ℝ) =
        fun x => ⟪spaceD i v x i • w x, w x⟫_ℝ + ⟪w x, v x i • spaceD i w x⟫_ℝ := by
      funext x
      rw [spaceD_smul (hvi i) hw, spaceD_coordinate hv, inner_add_left]
      rw [real_inner_comm (v x i • spaceD i w x)]
    rw [hright, integral_add (memLp_inner_integrable (hB i) hw0)
      (memLp_inner_integrable hw0 (hE i))] at h
    exact h
  have hj : ∑ i, J i = 0 := by
    dsimp only [J]
    rw [← integral_finsetSum _ (fun i _ => memLp_inner_integrable (hB i) hw0)]
    have hz : (fun x => ∑ i, ⟪spaceD i v x i • w x, w x⟫_ℝ) = fun _ => 0 := by
      funext x
      simp only [real_inner_smul_left, ← Finset.sum_mul, hdiv x, zero_mul]
    rw [hz, integral_zero]
  have hs : (∑ i, I i) = - (∑ i, J i) - ∑ i, I i := by
    calc
      _ = ∑ i, -(J i + I i) := Finset.sum_congr rfl (fun i _ => he i)
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]; ring
  rw [hj] at hs
  have hi : ∑ i, I i = 0 := by linarith
  simp_rw [inner_sum]
  rw [integral_finsetSum _ (fun i _ => memLp_inner_integrable hw0 (hE i))]
  exact hi

lemma memLp_drift {u w : Space → Space}
    (hu : ContDiff ℝ 2 u) (hw : MemLp w 2 volume)
    {C : ℝ} (hb : ∀ x, ‖fderiv ℝ u x‖ ≤ C) :
    MemLp (fun x => fderiv ℝ u x (w x)) 2 volume := by
  apply hw.of_le_mul
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hu.continuous_fderiv (by norm_num)).aestronglyMeasurable.prodMk hw.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun x => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

lemma integral_drift_bound {u w : Space → Space}
    (hu : ContDiff ℝ 2 u) (hw : MemLp w 2 volume)
    {C : ℝ} (hb : ∀ x, ‖fderiv ℝ u x‖ ≤ C) :
    -(∫ x, ⟪w x, fderiv ℝ u x (w x)⟫_ℝ) ≤ C * ∫ x, ‖w x‖ ^ 2 := by
  have hi := memLp_inner_integrable hw (memLp_drift hu hw hb)
  have hw2 : Integrable (fun x => ‖w x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using memLp_inner_integrable hw hw
  rw [← integral_neg, ← integral_const_mul]
  apply integral_mono hi.neg (hw2.const_mul C)
  intro x
  calc
    -⟪w x, fderiv ℝ u x (w x)⟫_ℝ ≤ |⟪w x, fderiv ℝ u x (w x)⟫_ℝ| := neg_le_abs _
    _ ≤ ‖w x‖ * ‖fderiv ℝ u x (w x)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w x‖ * (C * ‖w x‖) := mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))) (norm_nonneg _)
    _ = C * ‖w x‖ ^ 2 := by ring

lemma spatial_energy_bound {u v w : Space → Space} {q : Space → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : Differentiable ℝ v) (hw : ContDiff ℝ 2 w)
    (hq : Differentiable ℝ q) (hw0 : MemLp w 2 volume) (hq0 : MemLp q 2 volume)
    (hv1 : ∀ i, MemLp (spaceD i v) 2 volume)
    (hw1 : ∀ i, MemLp (spaceD i w) 2 volume)
    (hw2 : ∀ i, MemLp (spaceD i (spaceD i w)) 2 volume)
    (hq1 : ∀ i, MemLp (spaceD i q) 2 volume)
    {C B D ν : ℝ} (hν : 0 ≤ ν)
    (huC : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hvB : ∀ x, ‖v x‖ ≤ B) (hwD : ∀ x, ‖w x‖ ≤ D)
    (hdivv : ∀ x, ∑ i, spaceD i v x i = 0)
    (hdivw : ∀ x, ∑ i, spaceD i w x i = 0) :
    (∫ x, ⟪w x, -(∑ i, spaceD i q x • basis i) +
      ν • (∑ i, spaceD i (spaceD i w) x) -
      (∑ i, v x i • spaceD i w x) - fderiv ℝ u x (w x)⟫_ℝ) ≤
      C * ∫ x, ‖w x‖ ^ 2 := by
  have hp : MemLp (fun x => ∑ i, spaceD i q x • basis i) 2 volume := by
    apply memLp_finsetSum
    intro i _hi
    exact (hq1 i).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (basis i))
  have hl : MemLp (fun x => ∑ i, spaceD i (spaceD i w) x) 2 volume := by
    exact memLp_finsetSum _ (fun i _ => hw2 i)
  have ht : MemLp (fun x => ∑ i, v x i • spaceD i w x) 2 volume := by
    apply memLp_finsetSum
    intro i _hi
    exact memLp_smul_bounded ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hv.continuous)
      (fun x => (PiLp.norm_apply_le _ _).trans (hvB x)) (hw1 i)
  have hd := memLp_drift hu hw0 huC
  have hip := memLp_inner_integrable hw0 hp
  have hil := memLp_inner_integrable hw0 hl
  have hit := memLp_inner_integrable hw0 ht
  have hid := memLp_inner_integrable hw0 hd
  simp_rw [inner_sub_right, inner_add_right, inner_neg_right, inner_smul_right]
  have hi₁ := integral_sub ((hip.neg.add (hil.const_mul ν)).sub hit) hid
  have hi₂ := integral_sub (hip.neg.add (hil.const_mul ν)) hit
  have hi₃ := integral_add hip.neg (hil.const_mul ν)
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at hi₁ hi₂ hi₃
  rw [hi₁, hi₂, hi₃, integral_neg, integral_const_mul]
  rw [integral_pressure_orthogonal (hw.differentiable (by norm_num)) hq hw0 hq0 hw1 hq1 hdivw,
    integral_transport_zero hv (hw.differentiable (by norm_num)) hw0 hv1 hw1 hvB hwD hdivv]
  have hl0 := integral_laplace_dissipation hw hw0 hw1 hw2
  have hd0 := integral_drift_bound hu hw0 huC
  have hn := mul_nonpos_of_nonneg_of_nonpos hν hl0
  linarith

end RapidForcing

end

end OAI
