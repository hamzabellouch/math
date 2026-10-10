import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Translation averages preserving commuting invariance. -/

noncomputable section

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_translate {n : ℕ}
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    {F : I → Cochain M (n+1)} {G : Cochain M (n+1)} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x)) (u : unitary M)
    (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => translateLast (F i) u x) l (translateLast G u x) := by
  simp only [translateLast_apply]
  exact (hR (star (u:M))).tendsto e (ht _)

lemma translate_iterate_eq {n : ℕ} (u : unitary M) (F : Cochain M (n+1)) (j : ℕ) :
    (translateLastCLM u)^[j] F=translateLast F (u^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply',ih]
      change translateLast (translateLast F (u^j)) u = _
      rw [translateLast_mul,pow_succ']

lemma residual_translate_cesaro {n : ℕ} (u : unitary M) (F : Cochain M (n+1))
    (c : (Fin (n+1) → M) → M)
    (hr : ∀ v x, residualCLM x (translateLast F v)=c x) (j : ℕ) :
    ∀ v x, residualCLM x (translateLast (HochschildCesaro.avg (translateLastCLM u) F j) v)=c x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  change L (HochschildCesaro.avg (translateLastCLM u) F j)=c x
  rw [HochschildCesaro.avg,map_smul,map_sum]
  have hL (k : ℕ) : L ((translateLastCLM u)^[k] F)=c x := by
    rw [translate_iterate_eq]
    change residualCLM x (translateLast (translateLast F (u^k)) v)=c x
    rw [translateLast_mul,hr]
  simp only [hL,Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_add_one,smul_smul]
  rw [inv_mul_cancel₀ (show (j+1:ℂ)≠0 by exact_mod_cast Nat.succ_ne_zero j),one_smul]

lemma translate_cesaro_fixed {n : ℕ} (u v : unitary M) (huv : Commute u v)
    (F : Cochain M (n+1)) (hF : translateLast F v=F) (j : ℕ) :
    translateLast (HochschildCesaro.avg (translateLastCLM u) F j) v=
      HochschildCesaro.avg (translateLastCLM u) F j := by
  have hi (k : ℕ) : translateLast ((translateLastCLM u)^[k] F) v=
      (translateLastCLM u)^[k] F := by
    rw [translate_iterate_eq,translateLast_mul,← (huv.pow_left k).eq,
      ← translateLast_mul,hF]
  change (translateLastCLM v) (HochschildCesaro.avg (translateLastCLM u) F j)=_
  rw [HochschildCesaro.avg,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact hi k

theorem exists_translate_fixed_preserving {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (u : unitary M) (S : Set (unitary M)) (hcomm : ∀ v ∈ S, Commute u v)
    (F : Cochain M (n+1)) (hfix : ∀ v ∈ S, translateLast F v=F)
    (c : (Fin (n+1) → M) → M)
    (hr : ∀ v x, residualCLM x (translateLast F v)=c x) :
    ∃ G : Cochain M (n+1), ‖G‖≤‖F‖ ∧
      (∀ v ∈ insert u S, translateLast G v=G) ∧
      ∀ v x, residualCLM x (translateLast G v)=c x := by
  let P : Cochain M (n+1) →L[ℂ] Cochain M (n+1) := translateLastCLM u
  let A := fun j => HochschildCesaro.avg P F j
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ)≤atTop := Ultrafilter.of_le _
  have hP (g : Cochain M (n+1)) : ‖P g‖≤‖g‖ := norm_translateLast_le g u
  have hA (j : ℕ) : ‖A j‖≤‖F‖ := HochschildCesaro.norm_avg_le P hP F j
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U A ‖F‖ (norm_nonneg _) hA
  refine ⟨G,hG,?_,?_⟩
  · intro v hv
    rcases hv with hv | hv
    · subst v
      ext x
      have hlim := predual_tendsto_sub e (predual_tendsto_translate e hR ht u x) (ht x)
      have hn : Tendsto (fun j => P (A j)-A j) (U : Filter ℕ) (𝓝 0) :=
        (HochschildCesaro.avg_defect_tendsto P hP F).mono_left hU
      have hxn : Tendsto (fun j => (P (A j)-A j) x) (U : Filter ℕ) (𝓝 0) := by
        convert ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x).continuous.tendsto 0).comp hn using 1
        · rfl
        · simp
      exact sub_eq_zero.mp (predual_tendsto_unique e hlim (predual_tendsto_of_norm e hxn))
    · ext x
      have hlim := predual_tendsto_translate e hR ht v x
      have he (j : ℕ) : translateLast (A j) v=A j :=
        translate_cesaro_fixed u v (hcomm v hv) F (hfix v hv) j
      simp only [he] at hlim
      exact predual_tendsto_unique e hlim (ht x)
  · intro v x
    have hlim := predual_tendsto_residual e hL
      (fun y => predual_tendsto_translate e hR ht v y) x
    have he (j : ℕ) : residualCLM x (translateLast (A j) v)=c x :=
      residual_translate_cesaro u F c hr j v x
    simp only [he] at hlim
    exact predual_tendsto_unique e hlim (predual_tendsto_const e (c x) (U : Filter ℕ))

end BoundedHochschild

end

end OAI
