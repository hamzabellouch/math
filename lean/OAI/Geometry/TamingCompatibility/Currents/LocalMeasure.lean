import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TamingCompatibility.LocalRestriction

variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def localMeasure (μ : Measure E) (K : Set E) : Measure K := μ.comap Subtype.val

def restrict (μ : Measure E) (K : Set E) (hK : MeasurableSet K) :
    Lp F 2 μ →L[ℝ] Lp F 2 (localMeasure μ K) :=
  (Lp.compMeasurePreservingₗᵢ ℝ ((↑) : K → E)
    (measurePreserving_subtype_coe hK)).toContinuousLinearMap ∘L
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using μ.restrict_le_self (s := K))

lemma restrict_coe (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) : restrict μ K hK u =ᵐ[localMeasure μ K] (fun x : K => u x) := by
  apply (Lp.coeFn_compMeasurePreserving _ (measurePreserving_subtype_coe hK)).trans
  exact (measurePreserving_subtype_coe hK).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) u)

lemma restrict_norm_le (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (u : Lp F 2 μ) : ‖restrict μ K hK u‖ ≤ ‖u‖ := by
  change ‖Lp.compMeasurePreserving ((↑) : K → E) (measurePreserving_subtype_coe hK)
    (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) u)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  have hb := Lp.norm_LpToLpOfMeasureLeSMul_le (p := (2 : ℝ≥0∞)) (E := F)
    (c := 1) (by simp) (by simpa using μ.restrict_le_self (s := K))
  have hn : ‖(Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using μ.restrict_le_self (s := K)) : Lp F 2 μ →L[ℝ] Lp F 2 (μ.restrict K))‖ ≤ 1 := by
    simpa using hb
  exact ContinuousLinearMap.le_of_opNorm_le _ hn u |>.trans_eq (one_mul _)

lemma restrict_opNorm_le (μ : Measure E) (K : Set E) (hK : MeasurableSet K) :
    ‖restrict (F := F) μ K hK‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro u
    simpa using restrict_norm_le μ K hK u)

lemma finite_localMeasure (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (hm : μ K < ∞) : IsFiniteMeasure (localMeasure μ K) := by
  constructor
  have h := (measurePreserving_subtype_coe (μa := μ) hK).measure_preimage MeasurableSet.univ
  change (μ.comap ((↑) : K → E)) Set.univ < ∞
  have h' : (μ.comap ((↑) : K → E)) Set.univ = (μ.restrict K) Set.univ := h
  exact h'.trans_lt (by rw [Measure.restrict_apply_univ]; exact hm)

end TamingCompatibility.LocalRestriction

end

end OAI
