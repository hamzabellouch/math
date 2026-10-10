import Mathlib
import OAI.Analysis.BoundedHochschild.CochainLimits
import OAI.Analysis.BoundedHochschild.CollisionBounds

namespace OAI

/-! Cesaro averaging and fixed cocycles. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace HochschildCesaro
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def avg (P : E →L[ℂ] E) (f : E) (n : ℕ) : E :=
  (n+1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (n+1), P^[j] f

lemma iterate_norm_le (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (f : E) (j : ℕ) : ‖P^[j] f‖ ≤ ‖f‖ := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simpa only [Function.iterate_succ_apply'] using (hP (P^[j] f)).trans ih

lemma norm_avg_le (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (f : E) (n : ℕ) : ‖avg P f n‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hs : ‖∑ j ∈ Finset.range (n+1), P^[j] f‖ ≤ (n+1 : ℝ) * ‖f‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), ‖P^[j] f‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range (n+1), ‖f‖ :=
        Finset.sum_le_sum fun j _ => iterate_norm_le P hP f j
      _ = _ := by simp [nsmul_eq_mul]
  calc
    ‖avg P f n‖ = (n+1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (n+1), P^[j] f‖ := by
      rw [avg, norm_smul, norm_inv, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
    _ ≤ (n+1 : ℝ)⁻¹ * ((n+1 : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

lemma sum_defect (P : E →L[ℂ] E) (f : E) (n : ℕ) :
    P (∑ j ∈ Finset.range n, P^[j] f) - (∑ j ∈ Finset.range n, P^[j] f) = P^[n] f - f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add]
    rw [show P (P^[n] f) = P^[n+1] f by rw [Function.iterate_succ_apply']]
    calc
      _ = (P (∑ j ∈ Finset.range n, P^[j] f) - (∑ j ∈ Finset.range n, P^[j] f)) + (P^[n+1] f - P^[n] f) := by abel
      _ = _ := by rw [ih]; abel

lemma avg_defect (P : E →L[ℂ] E) (f : E) (n : ℕ) :
    P (avg P f n) - avg P f n = (n+1 : ℂ)⁻¹ • (P^[n+1] f - f) := by
  simp only [avg,map_smul,← smul_sub,sum_defect]

lemma avg_defect_tendsto (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) :
    Tendsto (fun n => P (avg P f n) - avg P f n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have H : Tendsto (fun n : ℕ => (n+1 : ℝ)⁻¹ * (2*‖f‖)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2*‖f‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) H
  rw [avg_defect,norm_smul]
  have hn : ‖(n+1:ℂ)⁻¹‖ = (n+1 : ℝ)⁻¹ := by
    rw [norm_inv, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by linarith [iterate_norm_le P hP f (n+1)])

end HochschildCesaro

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]
lemma residual_cesaro {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) (j : ℕ) :
    ∀ v x, residualCLM x (translateLast (HochschildCesaro.avg (averageLastCLM p u hp hs) f j) v) =
      ((-1:ℂ)^(n+1)) • f x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  change L (HochschildCesaro.avg (averageLastCLM p u hp hs) f j) = _
  rw [HochschildCesaro.avg,map_smul,map_sum]
  have hL (k : ℕ) : L ((averageLastCLM p u hp hs)^[k] f) = ((-1:ℂ)^(n+1)) • f x :=
    residual_iterate p u hp hs f hf k v x
  simp only [hL,Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add_one,smul_smul]
  rw [← mul_assoc,inv_mul_cancel₀ (show (j+1:ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero j),one_mul]

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma averageLast_apply {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (F : Cochain M (n+1)) (x : Fin (n+1) → M) :
    averageLast p u F x = ∑' j, (p j : ℂ) • translateLast F (u j) x := by
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x).map_tsum
    (summable_averageLast p u hp hs F)

lemma predual_tendsto_average {n : ℕ}
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    {F : I → Cochain M (n+1)} {G : Cochain M (n+1)} {l : Filter I} [l.NeBot]
    (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x)) :
    ∀ x, PredualTendsto e (fun i => averageLast p u (F i) x) l (averageLast p u G x) := by
  intro x
  simp_rw [averageLast_apply p u hp hs]
  apply predual_tendsto_tsum e (fun j => p j * (C * ∏ k, ‖x k‖)) (hs.mul_right _)
  · intro i j
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp j)]
    apply mul_le_mul_of_nonneg_left _ (hp j)
    exact ((translateLast (F i) (u j)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((norm_translateLast_le _ _).trans (hF i))
        (Finset.prod_nonneg fun k _ => norm_nonneg _))
  · intro j
    apply predual_tendsto_smul e _ (p j : ℂ)
    simp only [translateLast_apply]
    exact (hR (star (u j : M))).tendsto e (ht _)

lemma predual_tendsto_residual {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    {F : I → Cochain M (n+1)} {G : Cochain M (n+1)} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x)) (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => residualCLM x (F i)) l (residualCLM x G) := by
  simp only [residualCLM_apply]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e (ht _) _

 

theorem exists_average_fixed_cocycle {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (f : Cochain M (n+1)) (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) :
    ∃ G : Cochain M (n+1), ‖G‖ ≤ ‖f‖ ∧ averageLast p u G = G ∧
      (∀ x, residualCLM x G = ((-1:ℂ)^(n+1)) • f x) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∀ x, PredualTendsto e
          (fun j => HochschildCesaro.avg (averageLastCLM p u hp hs) f j x) U (G x) := by
  let P : Cochain M (n+1) →L[ℂ] Cochain M (n+1) := averageLastCLM p u hp hs
  let F : ℕ → Cochain M (n+1) := fun j => HochschildCesaro.avg P f j
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hP (g : Cochain M (n+1)) : ‖P g‖ ≤ ‖g‖ := norm_averageLast_le p u hp hs g
  have hF (j : ℕ) : ‖F j‖ ≤ ‖f‖ := HochschildCesaro.norm_avg_le P hP f j
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hF
  have hfix : averageLast p u G = G := by
    ext x
    have hpa := predual_tendsto_average e hR p u hp hs.summable ‖f‖ hF ht x
    have hsub := predual_tendsto_sub e hpa (ht x)
    have hn : Tendsto (fun j => P (F j)-F j) (U : Filter ℕ) (𝓝 0) :=
      (HochschildCesaro.avg_defect_tendsto P hP f).mono_left hU
    have hxn : Tendsto (fun j => (P (F j)-F j) x) (U : Filter ℕ) (𝓝 0) := by
      convert
        ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x).continuous.tendsto 0).comp hn using 1
      · rfl
      · simp

    have hz := predual_tendsto_of_norm e hxn
    have he := predual_tendsto_unique e hsub hz
    exact sub_eq_zero.mp he
  refine ⟨G,hG,hfix,?_,U,hU,ht⟩
  intro x
  have hr := predual_tendsto_residual e hL ht x
  have hid (j : ℕ) : residualCLM x (F j) = ((-1:ℂ)^(n+1)) • f x := by
    simpa only [translateLast_one] using residual_cesaro p u hp hs f hf j 1 x
  apply predual_tendsto_unique e hr
  simp only [hid]
  exact predual_tendsto_const e (((-1:ℂ)^(n+1)) • f x) (U : Filter ℕ)

end BoundedHochschild
end

end OAI
