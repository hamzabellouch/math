import OAI.NumberTheory.CubicMoment.Estimates.SignedMellinTail

namespace OAI

/-! Assemble a local Mellin estimate and the two signed tails as a bound
for the full integral. -/
noncomputable section
open Set MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_height_split {F : ℝ → ℝ} (hF : Integrable F) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, F t) = (∫ t in Ioo (-T) T, F t)+
      (∫ t in Ici T, F t)+(∫ t in Ici T, F (-t)) := by
  have hc : (Ioo (-T) T)ᶜ = Ici T ∪ Iic (-T) := by
    ext t
    simp only [mem_compl_iff,mem_Ioo,not_and_or,not_lt,mem_union,mem_Ici,mem_Iic]
    tauto
  have hd : Disjoint (Ici T) (Iic (-T)) := by
    apply disjoint_left.mpr
    intro t ht hs
    have ht' : T ≤ t := ht
    have hs' : t ≤ -T := hs
    linarith
  rw [← integral_add_compl measurableSet_Ioo hF,hc,
    setIntegral_union hd measurableSet_Iic hF.integrableOn hF.integrableOn]
  have hn : (∫ t in Ici T, F (-t)) = ∫ t in Iic (-T), F t := by
    rw [integral_Ici_eq_integral_Ioi,integral_comp_neg_Ioi]
  rw [hn]
  ring

theorem integral_local_and_signed_tail {f g : ℝ → ℝ} (hfi : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfg : Integrable (fun t => f t*g t))
    {T B E : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hlocal : ∀ t : ℝ, |t| < T → g t ≤ B)
    (htail : (∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t)) ≤ E) :
    (∫ t : ℝ, f t*g t) ≤ B*(∫ t : ℝ, f t)+E := by
  have hi : (∫ t in Ioo (-T) T, f t*g t) ≤ B*(∫ t : ℝ, f t) := by
    calc
      _ ≤ ∫ t in Ioo (-T) T, B*f t := by
        apply setIntegral_mono_on hfg.integrableOn (hfi.const_mul B).integrableOn measurableSet_Ioo
        intro t ht
        calc
          _ ≤ f t*B := mul_le_mul_of_nonneg_left (hlocal t (abs_lt.mpr ht)) (hf0 t)
          _ = _ := mul_comm _ _
      _ = B*(∫ t in Ioo (-T) T, f t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hfi (Eventually.of_forall hf0)) hB
  rw [integral_height_split hfg hT]
  linarith

end CubicFirstMoment

end

end OAI
