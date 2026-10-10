import OAI.Analysis.IrrationalRotation.Operators.StrongOperatorConvergence
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.WeightedShift

theorem diagonal_tendsto_apply {ι : Type*} {l : Filter ι}
    {a : ι → Weight} {b : Weight} {C : ℝ}
    (ha : ∀ᶠ n in l, ‖a n‖ ≤ C)
    (hab : ∀ k : ℤ, Tendsto (fun n => a n k) l (𝓝 (b k))) (v : Hilbert) :
    Tendsto (fun n => diagonal (a n) v) l (𝓝 (diagonal b v)) := by
  let basis : HilbertBasis ℤ ℂ Hilbert := ⟨LinearIsometryEquiv.refl ℂ Hilbert⟩
  have hbasis (k : ℤ) : basis k = (lp.single 2 k (1 : ℂ) : Hilbert) :=
    basis.repr_self k
  apply strong_tendsto_of_dense_span_of_bounded (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr basis.dense_span) ?_ ?_ v
  · intro k
    have hs : ∀ w : Weight, diagonal w (basis k) = w k • basis k := by
      intro w
      rw [hbasis]
      apply lp.ext
      funext j
      change w j * (lp.single 2 k (1 : ℂ) : Hilbert) j = w k * (lp.single 2 k (1 : ℂ) : Hilbert) j
      by_cases hj : j = k
      · subst j; rfl
      · simp [lp.single_apply, hj]
    simp_rw [hs]
    exact (hab k).smul_const (basis k)
  · filter_upwards [ha] with n hn
    exact (lp.norm_mapCLM_le 2 _ (norm_nonneg (a n)) _).trans hn

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem lp_tendsto_of_ae_of_dominated
    {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → Lp E 2 μ} {g : Lp E 2 μ} {bound : X → ℝ}
    (hbound : MemLp bound 2 μ)
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => Lp.aestronglyMeasurable (f n)) (Lp.memLp g) ?_ hfg
  apply unifIntegrable_iff'.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hbound.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  apply le_trans ?_ (hsmall s hs hμs)
  apply eLpNorm_mono_ae_real ((Lp.aestronglyMeasurable (f n)).indicator hs)
  filter_upwards [hf n] with x hx
  by_cases hxs : x ∈ s
  · simpa [hxs] using hx
  · simp [hxs]

theorem fieldDiagonal_tendsto_apply
    (a : ℕ → X → Weight) (b : X → Weight)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n x, ‖a n x‖ ≤ C) (hb : ∀ x, ‖b x‖ ≤ D)
    (hma : ∀ n k, AEStronglyMeasurable (fun x => a n x k) μ)
    (hmb : ∀ k, AEStronglyMeasurable (fun x => b x k) μ)
    (hab : ∀ᵐ x ∂μ, ∀ k, Tendsto (fun n => a n x k) atTop (𝓝 (b x k)))
    (v : Lp Hilbert 2 μ) :
    Tendsto (fun n => fieldDiagonal (a n) C hC (ha n) (hma n) v)
      atTop (𝓝 (fieldDiagonal b D hD hb hmb v)) := by
  apply lp_tendsto_of_ae_of_dominated ((Lp.memLp v).norm.const_mul C)
  · intro n
    filter_upwards [fieldDiagonal_ae (a n) C hC (ha n) (hma n) v] with x hx
    rw [hx]
    exact (diagonal (a n x)).le_of_opNorm_le
      ((lp.norm_mapCLM_le 2 _ (norm_nonneg (a n x)) _).trans (ha n x)) (v x)
  · have hall : ∀ᵐ x ∂μ, ∀ n,
        fieldDiagonal (a n) C hC (ha n) (hma n) v x = diagonal (a n x) (v x) := by
      rw [ae_all_iff]
      intro n
      exact fieldDiagonal_ae (a n) C hC (ha n) (hma n) v
    filter_upwards [hall, fieldDiagonal_ae b D hD hb hmb v, hab] with x hx hy hxy
    simp_rw [hx, hy]
    exact diagonal_tendsto_apply (Eventually.of_forall fun n => ha n x) hxy (v x)

end Invariant233.WeightedShift

end

end OAI
