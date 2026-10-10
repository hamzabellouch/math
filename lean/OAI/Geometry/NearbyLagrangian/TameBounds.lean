import Mathlib
import OAI.Geometry.NearbyLagrangian.MorseTransport
import OAI.Geometry.NearbyLagrangian.PhaseErrors

namespace OAI

/-! Homogeneous reference bounds and preservation of tame tails. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma norm_baseDifferential_le (F : E × W → ℝ) (x : E) (w : W) :
    ‖baseDifferential F x w‖ ≤ ‖fderiv ℝ F (x,w)‖ := by
  apply (baseDifferential F x w).opNorm_le_bound (norm_nonneg (fderiv ℝ F (x,w)))
  intro u
  simpa [baseDifferential] using (fderiv ℝ F (x,w)).le_opNorm (u,0)

lemma norm_verticalDifferential_le (F : E × W → ℝ) (x : E) (w : W) :
    ‖verticalDifferential F x w‖ ≤ ‖fderiv ℝ F (x,w)‖ := by
  apply (verticalDifferential F x w).opNorm_le_bound (norm_nonneg (fderiv ℝ F (x,w)))
  intro v
  simpa [verticalDifferential] using (fderiv ℝ F (x,w)).le_opNorm (0,v)

lemma differentiableAt_homogeneousReference {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : DifferentiableAt ℝ g (q.1,q.2.1)) :
    DifferentiableAt ℝ (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2) q :=
  (hg.comp q (differentiableAt_fst.prodMk differentiableAt_snd.fst)).sub
    (differentiableAt_snd.snd.fst.inner ℝ differentiableAt_snd.snd.snd)

lemma contDiffAt_homogeneousReference {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : ContDiffAt ℝ 1 g (q.1,q.2.1)) :
    ContDiffAt ℝ 1 (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2) q :=
  (hg.comp q (contDiffAt_fst.prodMk contDiffAt_snd.fst)).sub
    (contDiffAt_snd.snd.fst.inner ℝ contDiffAt_snd.snd.snd)

lemma baseDifferential_homogeneousReference {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : DifferentiableAt ℝ g (q.1,q.2.1)) :
    baseDifferential (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2) q.1 q.2 =
      baseDifferential g q.1 q.2.1 := by
  have h₁ := (differentiableAt_homogeneousReference q hg).hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  have h₂ := (hg.hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2.1)).sub_const
      (inner ℝ q.2.2.1 q.2.2.2)
  exact h₁.unique h₂

lemma vertical_homogeneousReference_old {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : DifferentiableAt ℝ g (q.1,q.2.1)) :
    (verticalDifferential (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2)
      q.1 q.2).comp (inl ℝ W (E × E)) = verticalDifferential g q.1 q.2.1 := by
  have h₁ := ((differentiableAt_homogeneousReference q hg).hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).comp q.2.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.2.1 q.2.2)
  have h₂ := (hg.hasFDerivAt.comp q.2.1
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2.1)).sub_const
      (inner ℝ q.2.2.1 q.2.2.2)
  exact h₁.unique h₂

lemma vertical_homogeneousReference_z {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : DifferentiableAt ℝ g (q.1,q.2.1)) :
    (verticalDifferential (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2)
      q.1 q.2).comp ((inr ℝ W (E × E)).comp (inl ℝ E E)) = -innerSL ℝ q.2.2.2 := by
  have h₁ := (((differentiableAt_homogeneousReference q hg).hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).comp q.2.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.1 q.2.2)).comp q.2.2.1
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.2.2.1 q.2.2.2)
  have h₂ : HasFDerivAt (fun z : E => g (q.1,q.2.1)-inner ℝ z q.2.2.2)
      (-innerSL ℝ q.2.2.2) q.2.2.1 := by
    simpa only [innerSL_apply_apply, real_inner_comm] using
      ((innerSL ℝ q.2.2.2).hasFDerivAt.const_sub (g (q.1,q.2.1)))
  exact h₁.unique h₂

lemma vertical_homogeneousReference_p {g : E × W → ℝ}
    (q : E × (W × (E × E))) (hg : DifferentiableAt ℝ g (q.1,q.2.1)) :
    (verticalDifferential (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2)
      q.1 q.2).comp ((inr ℝ W (E × E)).comp (inr ℝ E E)) = -innerSL ℝ q.2.2.1 := by
  have h₁ := (((differentiableAt_homogeneousReference q hg).hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).comp q.2.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.1 q.2.2)).comp q.2.2.2
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.2.2.1 q.2.2.2)
  have h₂ : HasFDerivAt (fun p : E => g (q.1,q.2.1)-inner ℝ q.2.2.1 p)
      (-innerSL ℝ q.2.2.1) q.2.2.2 :=
    (innerSL ℝ q.2.2.1).hasFDerivAt.const_sub (g (q.1,q.2.1))
  exact h₁.unique h₂

lemma homogeneousReference_vertical_lower {g : E × W → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (q : E × (W × (E × E)))
    (hg : DifferentiableAt ℝ g (q.1,q.2.1))
    (hl : c * ‖q.2.1‖ ≤ ‖verticalDifferential g q.1 q.2.1‖) :
    min c 1 * ‖q.2‖ ≤ ‖verticalDifferential
      (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2) q.1 q.2‖ := by
  let L := verticalDifferential
    (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2) q.1 q.2
  have hw : ‖verticalDifferential g q.1 q.2.1‖ ≤ ‖L‖ := by
    rw [← vertical_homogeneousReference_old q hg]
    apply opNorm_le_bound _ (norm_nonneg L)
    intro v
    change ‖L (v,0,0)‖ ≤ ‖L‖ * ‖v‖
    simpa only [Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg v)] using L.le_opNorm (v,0,0)
  have hz : ‖q.2.2.2‖ ≤ ‖L‖ := by
    have hh : ‖L.comp ((inr ℝ W (E × E)).comp (inl ℝ E E))‖ ≤ ‖L‖ := by
      apply opNorm_le_bound _ (norm_nonneg L)
      intro v
      simpa using L.le_opNorm (0,v,0)
    rw [vertical_homogeneousReference_z q hg, norm_neg, innerSL_apply_norm] at hh
    exact hh
  have hp : ‖q.2.2.1‖ ≤ ‖L‖ := by
    have hh : ‖L.comp ((inr ℝ W (E × E)).comp (inr ℝ E E))‖ ≤ ‖L‖ := by
      apply opNorm_le_bound _ (norm_nonneg L)
      intro v
      simpa using L.le_opNorm (0,0,v)
    rw [vertical_homogeneousReference_p q hg, norm_neg, innerSL_apply_norm] at hh
    exact hh
  have hmc : 0 ≤ min c 1 := le_min hc zero_le_one
  change min c 1 * max ‖q.2.1‖ (max ‖q.2.2.1‖ ‖q.2.2.2‖) ≤ ‖L‖
  rw [mul_max_of_nonneg _ _ hmc, mul_max_of_nonneg _ _ hmc]
  exact max_le ((mul_le_mul_of_nonneg_right (min_le_left c 1) (norm_nonneg _)).trans (hl.trans hw))
    (max_le ((mul_le_of_le_one_left (norm_nonneg _) (min_le_right c 1)).trans hp)
      ((mul_le_of_le_one_left (norm_nonneg _) (min_le_right c 1)).trans hz))

lemma homogeneousReference_base_upper {g : E × W → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (q : E × (W × (E × E)))
    (hg : DifferentiableAt ℝ g (q.1,q.2.1))
    (hb : ‖baseDifferential g q.1 q.2.1‖ ≤ C * ‖q.2.1‖^2) :
    ‖baseDifferential (fun r : E × (W × (E × E)) => homogeneousReference g r.1 r.2)
      q.1 q.2‖ ≤ C * ‖q.2‖^2 := by
  rw [baseDifferential_homogeneousReference q hg]
  exact hb.trans (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
    (norm_fst_le q.2)) hC)


structure TameOn (U : Set E) (F g : E × W → ℝ) : Prop where
  smooth_F : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w)
  smooth_g : ∀ x ∈ U, ∀ w, ContDiffAt ℝ 1 g (x,w)
  homogeneous : ∀ x ∈ U, ∀ r : ℝ, 0 < r → ∀ w, g (x,r • w) = r^2 * g (x,w)
  estimates : ∃ c C M₀ M₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ M₀ ∧ 0 ≤ M₁ ∧
    (∀ x ∈ U, ∀ w, c * ‖w‖ ≤ ‖verticalDifferential g x w‖) ∧
    (∀ x ∈ U, ∀ w, ‖baseDifferential g x w‖ ≤ C * ‖w‖^2) ∧
    (∀ q : E × W, q.1 ∈ U → ‖F q-g q‖ ≤ M₀) ∧
    (∀ q : E × W, q.1 ∈ U → ‖fderiv ℝ (F-g) q‖ ≤ M₁)

lemma baseDifferential_sub {F g : E × W → ℝ} (q : E × W)
    (hF : DifferentiableAt ℝ F q) (hg : DifferentiableAt ℝ g q) :
    baseDifferential (F-g) q.1 q.2 = baseDifferential F q.1 q.2 - baseDifferential g q.1 q.2 := by
  simp only [baseDifferential, Prod.mk.eta, fderiv_sub hF hg, sub_comp]

lemma verticalDifferential_sub {F g : E × W → ℝ} (q : E × W)
    (hF : DifferentiableAt ℝ F q) (hg : DifferentiableAt ℝ g q) :
    verticalDifferential (F-g) q.1 q.2 =
      verticalDifferential F q.1 q.2 - verticalDifferential g q.1 q.2 := by
  simp only [verticalDifferential, Prod.mk.eta, fderiv_sub hF hg, sub_comp]

namespace TameOn
variable {U : Set E} {F g : E × W → ℝ} (T : TameOn U F g)
include T

lemma diff_error (q : E × W) (hq : q.1 ∈ U) : DifferentiableAt ℝ (F-g) q :=
  ((T.smooth_F _ hq _).differentiableAt (by simp)).sub
    ((T.smooth_g _ hq _).differentiableAt one_ne_zero)

theorem exists_tail_bounds : ∃ R c C : ℝ, 0 < R ∧ 0 < c ∧ 0 ≤ C ∧
    (∀ x ∈ U, ∀ w, R ≤ ‖w‖ → ‖baseDifferential F x w‖ ≤ C * ‖w‖^2) ∧
    (∀ x ∈ U, ∀ w, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖verticalDifferential F x w‖) := by
  obtain ⟨c,C,M₀,M₁,hc,hC,_,hM₁,hv,hb,_,he⟩ := T.estimates
  let R := max 1 (2*M₁/c)
  refine ⟨R,c/2,C+M₁,lt_of_lt_of_le zero_lt_one (le_max_left ..),
    half_pos hc,add_nonneg hC hM₁,?_,?_⟩
  · intro x hx w hw
    have hF := (T.smooth_F x hx w).differentiableAt (by simp)
    have hg := (T.smooth_g x hx w).differentiableAt one_ne_zero
    have herr : ‖baseDifferential F x w-baseDifferential g x w‖ ≤ M₁ := by
      rw [← baseDifferential_sub (x,w) hF hg]
      exact (norm_baseDifferential_le (F-g) x w).trans (he (x,w) hx)
    have ht : ‖baseDifferential F x w‖ ≤ ‖baseDifferential g x w‖ + M₁ := by
      calc
        _ = ‖baseDifferential g x w + (baseDifferential F x w-baseDifferential g x w)‖ := by congr 1; abel
        _ ≤ ‖baseDifferential g x w‖ + ‖baseDifferential F x w-baseDifferential g x w‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl herr
    have hw1 : 1 ≤ ‖w‖ := (le_max_left ..).trans hw
    have hw2 : 1 ≤ ‖w‖^2 := one_le_pow₀ hw1
    have := mul_le_mul_of_nonneg_left hw2 hM₁
    nlinarith [hb x hx w]
  · intro x hx w hw
    have hF := (T.smooth_F x hx w).differentiableAt (by simp)
    have hg := (T.smooth_g x hx w).differentiableAt one_ne_zero
    have herr : ‖verticalDifferential F x w-verticalDifferential g x w‖ ≤ M₁ := by
      rw [← verticalDifferential_sub (x,w) hF hg]
      exact (norm_verticalDifferential_le (F-g) x w).trans (he (x,w) hx)
    have ht : ‖verticalDifferential g x w‖ ≤ ‖verticalDifferential F x w‖ + M₁ := by
      calc
        _ = ‖verticalDifferential F x w - (verticalDifferential F x w-verticalDifferential g x w)‖ := by congr 1; abel
        _ ≤ ‖verticalDifferential F x w‖ + ‖verticalDifferential F x w-verticalDifferential g x w‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl herr
    have hlow : 2*M₁ ≤ c*‖w‖ := by
      have hh : 2*M₁/c ≤ ‖w‖ := (le_max_right ..).trans hw
      exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
    nlinarith [hv x hx w]

end TameOn

namespace StepData
variable (S : StepData (E := E) (W := W))

theorem tameOn_transport {g : E × W → ℝ} (T : TameOn S.U S.F g)
    (hζU : tsupport S.ζ ⊆ S.U)
    (hζ : HasCompactSupport S.ζ) (hβ : HasCompactSupport S.β) (hχ : HasCompactSupport S.χ)
    (hσ : HasCompactSupport S.σ) :
    TameOn S.U (totalPhase S.F S.σ S.κ)
      (fun q : E × (W × (E × E)) => homogeneousReference g q.1 q.2) := by
  obtain ⟨c,C,M₀,M₁,hc,hC,_,_,hv,hb,hval,hder⟩ := T.estimates
  obtain ⟨A₀,A₁,hA₀,hA₁⟩ := S.jointPhaseError_uniform_bounds hζU hζ hβ hχ hσ
    T.diff_error ⟨M₀,hval⟩ ⟨M₁,hder⟩
  refine ⟨(fun x hx w => S.contDiffAt_totalPhase hx), (fun x hx w =>
    contDiffAt_homogeneousReference (x,w) (T.smooth_g x hx w.1)),?_,?_⟩
  · intro x hx r hr w
    change g (x,r • w.1) - inner ℝ (r • w.2.1) (r • w.2.2) =
      r^2 * (g (x,w.1)-inner ℝ w.2.1 w.2.2)
    rw [T.homogeneous x hx r hr,real_inner_smul_left,real_inner_smul_right]
    ring
  · refine ⟨min c 1,C,max A₀ 0,max A₁ 0,lt_min hc zero_lt_one,hC,
      le_max_right ..,le_max_right ..,?_,?_,?_,?_⟩
    · intro x hx w
      exact homogeneousReference_vertical_lower hc.le (x,w)
        ((T.smooth_g x hx w.1).differentiableAt one_ne_zero) (hv x hx w.1)
    · intro x hx w
      exact homogeneousReference_base_upper hC (x,w)
        ((T.smooth_g x hx w.1).differentiableAt one_ne_zero) (hb x hx w.1)
    · intro q hq
      exact (hA₀ q hq).trans (le_max_left ..)
    · intro q hq
      exact (hA₁ q hq).trans (le_max_left ..)

end StepData
end NearbyLagrangian.Transport

end

end OAI
