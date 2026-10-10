import OAI.Probability.SLE.Stochastic.ProgressiveRandomTime

namespace OAI

/-! A parameter may choose both the sample and the evaluation time of a
progressive process. Finite truncation keeps the original raw sigma algebras. -/

noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal

namespace MeasureTheory.IsProgressive
open scoped _root_.MeasureTheory _root_.MeasureTheory.IsProgressive

theorem parameter_time_measurable
    {Ω Ξ X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace X]
    {ℱ : _root_.MeasureTheory.Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → X} (hN : _root_.MeasureTheory.IsProgressive ℱ N)
    (g : Ξ → Ω) (hg : Measurable g) (T : Ξ → ℝ≥0) (hT : Measurable T) :
    Measurable (fun x => N (T x) (g x)) := by
  let f (n : ℕ) (x : Ξ) := N (min (T x) (n:ℝ≥0)) (g x)
  have hf (n : ℕ) : Measurable (f n) := by
    have ht : Measurable (fun x => (⟨min (T x) (n:ℝ≥0),
        Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic (n:ℝ≥0))) :=
      (hT.min measurable_const).subtype_mk
    have hgn : @Measurable Ξ Ω _ (ℱ (n:ℝ≥0)) g := hg.mono le_rfl (ℱ.le _)
    exact (hN (n:ℝ≥0)).comp (ht.prodMk hgn)
  intro A hA
  have he : (fun x => N (T x) (g x)) ⁻¹' A =
      ⋃ n : ℕ, {x | T x ≤ (n:ℝ≥0)} ∩ (f n) ⁻¹' A := by
    ext x
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := exists_nat_ge (T x : ℝ)
      have htn : T x ≤ (n:ℝ≥0) := by exact_mod_cast hn
      exact ⟨n,htn,by simpa only [f,min_eq_left htn] using hx⟩
    · rintro ⟨n,hn,hx⟩
      simpa only [f,min_eq_left hn] using hx
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurableSet_le hT measurable_const).inter (hf n hA))

end MeasureTheory.IsProgressive

end

end OAI
