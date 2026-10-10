import Mathlib
import OAI.Computability.MinUncut.Games.MaskRowKernel

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

abbrev Rest (r : R) := {t : R // t ≠ r} → W

def joinRow (r : R) (b : W) (D : Rest (W := W) r) : R → W :=
  (Equiv.funSplitAt r W).symm (b,D)

omit [Fintype R] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
@[simp] lemma joinRow_at (r : R) (b : W) (D : Rest (W := W) r) : joinRow r b D r = b := by
  simp [joinRow, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype R] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
@[simp] lemma joinRow_other (r : R) (b : W) (D : Rest (W := W) r) (t : {t : R // t≠r}) :
    joinRow r b D t = D t := by
  simp [joinRow, Equiv.funSplitAt, Equiv.piSplitAt, t.property]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma expect_splitRow (r : R) (f : (R → W) → ℝ) :
    (𝔼 B, f B) = 𝔼 b, 𝔼 D, f (joinRow r b D) := by
  calc
    _ = 𝔼 p : W × Rest (W := W) r, f (joinRow r p.1 p.2) :=
      Fintype.expect_equiv (Equiv.funSplitAt r W) _ _ (fun B => congrArg f ((Equiv.funSplitAt r W).symm_apply_apply B).symm)
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

def restMask (r : R) (S : Finset R) : Finset {t : R // t≠r} :=
  Finset.univ.filter (fun t => t.val∈S)

omit [AddCommGroup W] [Module F₂ W] in
lemma maskKernel_split (r : R) (S : Finset R) (b c : W)
    (D E : Rest (W := W) r) :
    maskKernel S (joinRow r b D) (joinRow r c E) =
      maskRowKernel (decide (r∈S)) b c * maskKernel (restMask r S) D E := by
  let k := fun t : R => maskRowKernel (decide (t∈S)) (joinRow r b D t) (joinRow r c E t)
  have hp := Finset.prod_subtype (Finset.univ.erase r) (p := fun t : R => t≠r) (F := inferInstance)
    (by simp) k
  have h := Finset.mul_prod_erase Finset.univ k (Finset.mem_univ r)
  rw [hp] at h
  simpa [k, maskKernel, restMask] using h.symm

def rowCoefficient (r : R) (f : (R → W) → ℝ) (α : Module.Dual F₂ W)
    (D : Rest (W := W) r) : ℝ :=
  𝔼 b, f (joinRow r b D) * character α b

lemma rowCoefficient_maskProject (r : R) (S : Finset R) (f : (R → W) → ℝ)
    (α : Module.Dual F₂ W) (hα : α ≠ 0) (D : Rest (W := W) r) :
    rowCoefficient r (maskProject S f) α D =
      if r∈S then maskProject (restMask r S) (rowCoefficient r f α) D else 0 := by
  unfold rowCoefficient maskProject
  simp_rw [expect_splitRow r, maskKernel_split, Finset.expect_mul]
  rw [Finset.expect_comm]
  have hc (c : W) : (𝔼 b, 𝔼 E : Rest (W := W) r,
      maskRowKernel (decide (r∈S)) b c * maskKernel (restMask r S) D E *
      f (joinRow r c E) * character α b) =
      𝔼 E : Rest (W := W) r, 𝔼 b,
      maskRowKernel (decide (r∈S)) b c * maskKernel (restMask r S) D E *
      f (joinRow r c E) * character α b := by rw [Finset.expect_comm]
  simp_rw [hc]
  simp_rw [show ∀ b c, maskRowKernel (decide (r∈S)) b c =
      maskRowKernel (decide (r∈S)) c b from fun b c => maskRowKernel_symmetric _ _ _]
  simp_rw [show ∀ b c (E : Rest (W := W) r),
      maskRowKernel (decide (r∈S)) c b * maskKernel (restMask r S) D E *
        f (joinRow r c E) * character α b =
      maskKernel (restMask r S) D E * f (joinRow r c E) *
        (maskRowKernel (decide (r∈S)) c b * character α b) from fun _ _ _ => by ring]
  simp_rw [← Finset.mul_expect, maskRowKernel_character]
  have hdec : decide (α≠0)=true := by simp [hα]
  by_cases hs : r∈S
  · simp only [hs, hdec, decide_true, ↓reduceIte]
    rw [Finset.expect_comm]
    simp_rw [mul_assoc, ← Finset.mul_expect]
  · simp [hs, hα]

lemma rowCoefficient_maskProject_envelope (r : R) (S : Finset R)
    (f : (R → W) → ℝ) (a : Rest (W := W) r → ℝ)
    (ha : ∀ D, 0 ≤ a D) (α : Module.Dual F₂ W) (hα : α≠0)
    (h : ∀ D, |rowCoefficient r f α D| ≤ a D) (D : Rest (W := W) r) :
    |rowCoefficient r (maskProject S f) α D| ≤
      𝔼 E, |maskKernel (restMask r S) D E| * a E := by
  rw [rowCoefficient_maskProject _ _ _ _ hα]
  split_ifs with hs
  · calc
      _ ≤ 𝔼 E, |maskKernel (restMask r S) D E| * |rowCoefficient r f α E| := by
        simpa only [maskProject, abs_mul] using
          Finset.abs_expect_le Finset.univ (fun E => maskKernel (restMask r S) D E * rowCoefficient r f α E)
      _ ≤ _ := Finset.expect_le_expect (fun E _ => mul_le_mul_of_nonneg_left (h E) (abs_nonneg _))
  · simpa only [abs_zero] using Finset.expect_nonneg (fun E _ => mul_nonneg (abs_nonneg _) (ha E))

omit [Module F₂ W] in
lemma rowEnvelope_mean (r : R) (S : Finset R) (a : Rest (W := W) r → ℝ)
    (ha : ∀ D, 0 ≤ a D) :
    (𝔼 D, 𝔼 E, |maskKernel (restMask r S) D E| * a E) ≤
      (2:ℝ)^Fintype.card R * (𝔼 E, a E) := by
  rw [Finset.expect_comm]
  simp only [maskKernel_symmetric]
  simp_rw [← Finset.expect_mul]
  calc
    _ ≤ 𝔼 E, ((2:ℝ)^Fintype.card {t : R // t≠r}) * a E := by
      exact Finset.expect_le_expect (fun E _ => mul_le_mul_of_nonneg_right (maskKernel_abs_mean _ E) (ha E))
    _ ≤ 𝔼 E, ((2:ℝ)^Fintype.card R) * a E := by
      apply Finset.expect_le_expect
      intro E _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Fintype.card_subtype_le (fun t : R => t≠r))) (ha E)
    _ = _ := (Finset.mul_expect _ _ _).symm
end MinUncut.RowNoise

end

end OAI
