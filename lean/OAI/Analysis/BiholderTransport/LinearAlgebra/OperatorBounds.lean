import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology

namespace WeakMTWTransport
section OperatorBounds
variable {A E F : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eventually_injective_operator_bounds {f : A → E →L[ℝ] F} {a : A}
    (hf : ContinuousAt f a) (hi : Function.Injective (f a)) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ b in 𝓝 a, ∀ v,
      c*‖v‖≤‖f b v‖ ∧ ‖f b v‖≤C*‖v‖ := by
  obtain ⟨K,hK,hKa⟩ := (f a).injective_iff_antilipschitz.mp hi
  have hKr : 0<(K:ℝ) := hK
  let c : ℝ := (2*(K:ℝ))⁻¹
  have hc : 0<c := inv_pos.mpr (mul_pos (by norm_num) hKr)
  have he : ∀ᶠ b in 𝓝 a, ‖f b-f a‖<c :=
    (hf.sub_const (f a)).norm.eventually (gt_mem_nhds (by simpa using hc))
  refine ⟨c,‖f a‖+c,hc,by positivity,?_⟩
  filter_upwards [he] with b hb
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz (f a) hKa v
  have H' : (K:ℝ)⁻¹*‖v‖≤‖f a v‖ := by
    rw [inv_mul_le_iff₀ hKr]
    exact H
  have hdiff : ‖f b v-f a v‖≤c*‖v‖ :=
    ((f b-f a).le_opNorm v).trans (mul_le_mul_of_nonneg_right hb.le (norm_nonneg v))
  have htri : ‖f a v‖≤‖f b v‖+‖f b v-f a v‖ := by
    have ht := norm_add_le (f b v) (f a v-f b v)
    rw [←add_sub_assoc,add_sub_cancel_left,norm_sub_rev] at ht
    exact ht
  have hcn : (K:ℝ)⁻¹=2*c := by dsimp [c]; field_simp
  constructor
  · rw [hcn] at H'
    nlinarith
  · calc
      ‖f b v‖≤‖f a v‖+‖f b v-f a v‖ := by
        have ht := norm_add_le (f a v) (f b v-f a v)
        rwa [←add_sub_assoc,add_sub_cancel_left] at ht
      _ ≤ ‖f a‖*‖v‖+c*‖v‖ := add_le_add ((f a).le_opNorm v) hdiff
      _ = (‖f a‖+c)*‖v‖ := by ring

end OperatorBounds
end WeakMTWTransport

end

end

section

noncomputable section
open ContinuousLinearMap

namespace WeakMTWTransport
section OperatorTransfer
variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma operator_bounds_through_charts (U : E →L[ℝ] H) (Ui : H →L[ℝ] E)
    (V : F →L[ℝ] H) (Vi : H →L[ℝ] F) (A : H →L[ℝ] H) (P : E →L[ℝ] F)
    (hU : ∀ v, Ui (U v)=v) (hV : ∀ w, Vi (V w)=w)
    (hA : ∀ v, A (U v)=V (P v))
    {c C CU DU CV DV : ℝ} (hc : 0<c) (hC : 0<C)
    (hCU : 0<CU) (hDU : 0<DU) (hCV : 0<CV) (hDV : 0<DV)
    (hUb : ‖U‖≤CU) (hUib : ‖Ui‖≤DU) (hVb : ‖V‖≤CV) (hVib : ‖Vi‖≤DV)
    (hAb : ∀ w, c*‖w‖≤‖A w‖ ∧ ‖A w‖≤C*‖w‖) :
    ∀ v, c/(DU*CV)*‖v‖≤‖P v‖ ∧ ‖P v‖≤DV*C*CU*‖v‖ := by
  intro v
  have hu : ‖v‖≤DU*‖U v‖ := by
    calc
      ‖v‖=‖Ui (U v)‖ := by rw [hU]
      _ ≤ ‖Ui‖*‖U v‖ := Ui.le_opNorm _
      _ ≤ DU*‖U v‖ := mul_le_mul_of_nonneg_right hUib (norm_nonneg _)
  have hv : ‖P v‖≤DV*‖V (P v)‖ := by
    calc
      ‖P v‖=‖Vi (V (P v))‖ := by rw [hV]
      _ ≤ ‖Vi‖*‖V (P v)‖ := Vi.le_opNorm _
      _ ≤ DV*‖V (P v)‖ := mul_le_mul_of_nonneg_right hVib (norm_nonneg _)
  have hvu : ‖V (P v)‖≤CV*‖P v‖ :=
    (V.le_opNorm _).trans (mul_le_mul_of_nonneg_right hVb (norm_nonneg _))
  have huu : ‖U v‖≤CU*‖v‖ :=
    (U.le_opNorm _).trans (mul_le_mul hUb le_rfl (norm_nonneg _) hCU.le)
  have hlow : c*‖v‖≤(DU*CV)*‖P v‖ := by
    calc
      c*‖v‖ ≤ c*(DU*‖U v‖) := mul_le_mul_of_nonneg_left hu hc.le
      _ = DU*(c*‖U v‖) := by ring
      _ ≤ DU*‖A (U v)‖ := mul_le_mul_of_nonneg_left (hAb _).1 hDU.le
      _ = DU*‖V (P v)‖ := by rw [hA]
      _ ≤ DU*(CV*‖P v‖) := mul_le_mul_of_nonneg_left hvu hDU.le
      _ = _ := by ring
  refine ⟨?_,?_⟩
  · rw [div_mul_eq_mul_div,div_le_iff₀ (mul_pos hDU hCV)]
    nlinarith [hlow]
  · calc
      ‖P v‖ ≤ DV*‖V (P v)‖ := hv
      _ = DV*‖A (U v)‖ := by rw [hA]
      _ ≤ DV*(C*‖U v‖) := mul_le_mul_of_nonneg_left (hAb _).2 hDV.le
      _ ≤ DV*(C*(CU*‖v‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huu hC.le) hDV.le
      _ = _ := by ring

end OperatorTransfer
end WeakMTWTransport

end

end

end

end OAI
