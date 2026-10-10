import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import Mathlib.Data.Finsupp.Encodable

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- Independent real variables cannot satisfy a prescribed affine equation
when the second variable has no atoms. -/
theorem independent_sum_ne {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) (hg0 : ∀ r : ℝ, μ {ω | g ω = r} = 0) (c : ℝ) :
    ∀ᵐ ω ∂μ, f ω + g ω ≠ c := by
  have hp : MeasurableSet {z : ℝ × ℝ | z.1+z.2 ≠ c} :=
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const).compl
  have ha : ∀ᵐ z ∂(μ.map f).prod (μ.map g), z.1+z.2 ≠ c := by
    apply (Measure.ae_prod_iff_ae_ae hp).mpr
    apply Eventually.of_forall
    intro x
    have he : (μ.map g) {y : ℝ | x+y = c} = 0 := by
      have hs : {y : ℝ | x+y = c} = {c-x} := by ext y; simp; constructor <;> intro h <;> linarith
      rw [hs, Measure.map_apply hg (measurableSet_singleton _)]
      exact hg0 _
    exact measure_eq_zero_iff_ae_notMem.mp he
  rw [← hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at ha
  exact (ae_map_iff (hf.prodMk hg).aemeasurable hp).mp ha

theorem sourceAngleLaw_scaled_atomless (i : SourceCoordinate) (a : ℝ) (ha : a ≠ 0) (r : ℝ) :
    sourceAngleLaw {θ | a*θ i = r} = 0 := by
  have hs : {θ : SourceCoordinate → ℝ | a*θ i = r} =
      (fun θ : SourceCoordinate → ℝ => θ i) ⁻¹' {r/a} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; apply (eq_div_iff ha).mpr; nlinarith [h]
    · intro h; rw [h, mul_div_cancel₀ _ ha]
  rw [hs, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _),
    sourceAngleLaw_coordinate]
  exact measure_singleton _

/-- Every nontrivial finitely supported integer relation has probability zero. -/
theorem sourceAngleLaw_relation_ne (v : SourceCoordinate →₀ ℤ) (hv : v ≠ 0) (c : ℤ) :
    ∀ᵐ θ ∂sourceAngleLaw, v.sum (fun i n => (n : ℝ)*θ i) ≠ (c : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hv
  have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hi
  let f (j : SourceCoordinate) (θ : SourceCoordinate → ℝ) : ℝ := (v j : ℝ)*θ j
  have hm (j : SourceCoordinate) : Measurable (f j) := measurable_const.mul (measurable_pi_apply j)
  have hind : iIndepFun f sourceAngleLaw :=
    sourceAngleLaw_independent.comp (fun j (t : ℝ) => (v j : ℝ)*t)
      (fun _ => measurable_const.mul measurable_id)
  have hh := independent_sum_ne (Finset.measurable_sum (v.support.erase i) (fun j _ => hm j)) (hm i)
    (by
      convert hind.indepFun_finsetSum_of_notMem hm (Finset.notMem_erase i v.support) using 1
      funext θ
      simp only [Finset.sum_apply])
    (sourceAngleLaw_scaled_atomless i (v i : ℝ) hvi) (c : ℝ)
  filter_upwards [hh] with θ hθ
  simpa only [Finsupp.sum, ← Finset.sum_erase_add _ _ hi] using hθ

/-- Exact integer formulation of rational independence of 1 and all angles. -/
def SourceRationalIndependent (θ : SourceCoordinate → ℝ) : Prop :=
  ∀ (v : SourceCoordinate →₀ ℤ) (c : ℤ),
    v.sum (fun i n => (n : ℝ)*θ i) = (c : ℝ) → v = 0 ∧ c = 0

theorem sourceAngleLaw_rationalIndependent :
    ∀ᵐ θ ∂sourceAngleLaw, SourceRationalIndependent θ := by
  have h (v : SourceCoordinate →₀ ℤ) (c : ℤ) :
      ∀ᵐ θ ∂sourceAngleLaw, v.sum (fun i n => (n : ℝ)*θ i) = (c : ℝ) → v = 0 ∧ c = 0 := by
    by_cases hv : v = 0
    · subst v
      apply Eventually.of_forall
      intro θ hθ
      simp only [Finsupp.sum_zero_index] at hθ
      exact ⟨rfl, by exact_mod_cast hθ.symm⟩
    · filter_upwards [sourceAngleLaw_relation_ne v hv c] with θ hθ he
      exact (hθ he).elim
  exact ae_all_iff.mpr (fun v => ae_all_iff.mpr (h v))

end
end FiniteFactor

end OAI
