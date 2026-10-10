import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts

namespace OAI

/-! Bidual approximation for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace
namespace HochschildApproximation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_closure_image_ball (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hp : ∀ f : StrongDual ℂ F, f w = z (f.comp L))
    {R : ℝ} (hR : 0 < R) (hz : ‖z‖ ≤ R) :
    w ∈ closure (L '' Metric.closedBall (0 : E) R) := by
  by_contra hn
  have hc : Convex ℝ (L '' Metric.closedBall (0 : E) R) :=
    (convex_closedBall (0 : E) R).linear_image (L.restrictScalars ℝ).toLinearMap
  obtain ⟨f,r,hr,hwr⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hc.closure isClosed_closure hn
  have hr0 : 0 < r := by
    have h := hr 0 (subset_closure (show (0 : F) ∈ L '' Metric.closedBall 0 R from
      ⟨0, by simpa using hR.le, map_zero L⟩))
    simpa using h
  let g := f.comp L
  have hgn : ‖(R : ℂ) • g‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hr0.le
    intro a ha
    obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (g a)
    have hain : (R : ℂ) • c • a ∈ Metric.closedBall (0 : E) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, hc, ha, mul_one, le_refl]
    have h := (hr (L ((R : ℂ) • c • a)) (subset_closure ⟨_,hain,rfl⟩)).le
    have he' : (g (c • a)) = (‖g a‖ : ℂ) := by
      simpa only [map_smul, smul_eq_mul] using he.symm
    change ‖(R : ℂ) • g a‖ ≤ r
    change (g ((R : ℂ) • c • a)).re ≤ r at h
    rw [map_smul, he', smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using h
  have hg : R * ‖g‖ ≤ r := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hgn
  have hbound : (f w).re ≤ r := calc
    (f w).re = (z g).re := congrArg Complex.re (hp f)
    _ ≤ ‖z g‖ := Complex.re_le_norm _
    _ ≤ ‖z‖ * ‖g‖ := z.le_opNorm g
    _ ≤ R * ‖g‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ ≤ r := hg
  exact hwr.not_ge hbound

open Filter Topology

private lemma functional_prod (f : StrongDual ℂ (F × ℂ)) (a : F) (c : ℂ) :
    f (a,c) = f (a,0) + c * f (0,1) := by
  have he : (a,c) = (a,0) + c • ((0,1) : F × ℂ) := by simp
  rw [he, map_add, map_smul, smul_eq_mul]

theorem pair_representation (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L)) (g : StrongDual ℂ E) :
    ∀ f : StrongDual ℂ (F × ℂ), f (w,z g) = z (f.comp (L.prod g)) := by
  intro f
  let f₁ := f.comp (ContinuousLinearMap.inl ℂ F ℂ)
  have he : f.comp (L.prod g) = f₁.comp L + f (0,1) • g := by
    ext a
    change f (L a,g a) = f (L a,0) + f (0,1) * g a
    rw [functional_prod, mul_comm (g a)]
  rw [he, map_add, map_smul, smul_eq_mul, functional_prod]
  change f₁ w + z g * f (0,1) = z (f₁.comp L) + f (0,1) * z g
  rw [hw]; ring

theorem bounded_sequence_approximation (L : E →L[ℂ] F)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L))
    {R : ℝ} (hR : 0 < R) (hz : ‖z‖ ≤ R) :
    ∃ a : ℕ → E, (∀ n, ‖a n‖ ≤ R) ∧ Tendsto (fun n => L (a n)) atTop (𝓝 w) := by
  have hm := mem_closure_image_ball L z w hw hR hz
  obtain ⟨s,hs,hlim⟩ := mem_closure_iff_seq_limit.mp hm
  choose a ha he using hs
  refine ⟨a, ?_, ?_⟩
  · intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha n
  · simpa only [he] using hlim

private lemma tendsto_of_fourth {ι : Type*} {l : Filter ι} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (h : Tendsto (fun i => (f i)^4) l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  have hs := h.sqrt.sqrt
  have he (i : ι) : Real.sqrt (Real.sqrt ((f i)^4)) = f i := by
    rw [show (f i)^4 = ((f i)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _),
      Real.sqrt_sq (hf i)]
  simpa only [he, Real.sqrt_zero] using hs

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem quartic_tendsto_zero_bounded (T : E →L[ℂ] Y) (L : E →L[ℂ] F)
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ a, ‖T a‖^4 ≤ C * ‖a‖^2 * ‖L a‖^2)
    {ι : Type*} {l : Filter ι} {a : ι → E} {R : ℝ} (_hR : 0 ≤ R)
    (ha : ∀ i, ‖a i‖ ≤ R) (hL : Tendsto (fun i => L (a i)) l (𝓝 0)) :
    Tendsto (fun i => T (a i)) l (𝓝 0) := by
  have hn : Tendsto (fun i => ‖L (a i)‖) l (𝓝 0) := by simpa using hL.norm
  have hu : Tendsto (fun i => (C * R^2) * ‖L (a i)‖^2) l (𝓝 0) := by
    simpa using (hn.pow 2).const_mul (C * R^2)
  have hp : Tendsto (fun i => ‖T (a i)‖^4) l (𝓝 0) := by
    apply squeeze_zero (fun i => pow_nonneg (norm_nonneg _) _) _ hu
    intro i
    calc
      ‖T (a i)‖^4 ≤ C * ‖a i‖^2 * ‖L (a i)‖^2 := hdom _
      _ ≤ C * R^2 * ‖L (a i)‖^2 := by gcongr; exact ha i
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_fourth (fun _ => norm_nonneg _) hp)

theorem closed_subspace_preserved_of_quartic [CompleteSpace Y]
    (T : E →L[ℂ] Y) (L : E →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ a, ‖T a‖^4 ≤ C * ‖a‖^2 * ‖L a‖^2)
    (K : Submodule ℂ Y) (hK : IsClosed (K : Set Y)) (hT : ∀ a, T a ∈ K)
    (z : StrongDual ℂ (StrongDual ℂ E)) (w : F)
    (hw : ∀ f : StrongDual ℂ F, f w = z (f.comp L)) :
    ∃ y ∈ K, ∀ f : StrongDual ℂ Y, f y = z (f.comp T) := by
  let R := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : ‖z‖ ≤ R := by dsimp [R]; linarith
  obtain ⟨a,ha,halim⟩ := bounded_sequence_approximation L z w hw hR hz
  have hdiff : Tendsto (fun p : ℕ × ℕ => L (a p.1 - a p.2)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self, Function.comp_apply] using
      (halim.comp (show Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop by
        rw [← prod_atTop_atTop_eq]; exact tendsto_fst)).sub (halim.comp (show Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop by
        rw [← prod_atTop_atTop_eq]; exact tendsto_snd))
  have hTd := quartic_tendsto_zero_bounded T L hC hdom (by positivity : 0 ≤ 2*R)
    (fun p : ℕ × ℕ => (norm_sub_le _ _).trans (show ‖a p.1‖ + ‖a p.2‖ ≤ 2*R by
      linarith [ha p.1,ha p.2])) hdiff
  have hc : CauchySeq (fun n => T (a n)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    simpa only [map_sub, norm_zero, dist_eq_norm] using hTd.norm
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, hK.mem_of_tendsto hy (Eventually.of_forall (fun n => hT (a n))), ?_⟩
  intro f
  obtain ⟨b,hb,hblim⟩ := bounded_sequence_approximation (L.prod (f.comp T)) z
    (w,z (f.comp T)) (pair_representation L z w hw (f.comp T)) hR hz
  have hbL : Tendsto (fun n => L (b n)) atTop (𝓝 w) :=
    (continuous_fst.tendsto (w,z (f.comp T))).comp hblim
  have hbf : Tendsto (fun n => f (T (b n))) atTop (𝓝 (z (f.comp T))) :=
    (continuous_snd.tendsto (w,z (f.comp T))).comp hblim
  have hdL : Tendsto (fun n => L (a n - b n)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using halim.sub hbL
  have hdT := quartic_tendsto_zero_bounded T L hC hdom (by positivity : 0 ≤ 2*R)
    (fun n => (norm_sub_le _ _).trans (show ‖a n‖ + ‖b n‖ ≤ 2*R by
      linarith [ha n,hb n])) hdL
  have hbT : Tendsto (fun n => T (b n)) atTop (𝓝 y) := by
    simpa only [map_sub, sub_sub_cancel, sub_zero] using hy.sub hdT
  exact tendsto_nhds_unique (f.continuous.tendsto y |>.comp hbT) hbf

end HochschildApproximation

end

end OAI
