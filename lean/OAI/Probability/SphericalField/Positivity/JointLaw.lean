import Mathlib
import OAI.Probability.SphericalField.Positivity.Triangles

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma measurableSet_gram_arrays :
    MeasurableSet {Q : OverlapArray | ∀ n, Matrix.PosSemidef (overlapBlock id n Q)} := by
  apply IsClosed.measurableSet
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  have hiff (Q : OverlapArray) :=
    Matrix.posSemidef_iff_dotProduct_mulVec (M := overlapBlock id n Q)
  simp_rw [hiff]
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {Q : OverlapArray | Matrix.conjTranspose (overlapBlock id n Q) = overlapBlock id n Q}
    apply isClosed_eq <;> unfold overlapBlock <;> fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold overlapBlock
    fun_prop

lemma scalarArray_ultrametric (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, min (f (Q 0 1)) (f (Q 0 2)) ≤ f (Q 1 2) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hu := gg_ultrametric ν (scalarArray_swap_invariant μ hEx hf)
    (scalarArray_gg μ hGG hf) hg hd
  exact ae_of_ae_map hm.aemeasurable hu

def UltrametricTriangle (x y z : ℝ) : Prop :=
  min x y ≤ z ∧ min x z ≤ y ∧ min y z ≤ x

lemma gg_ultrametric_triangle (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (Q 0 1) (Q 0 2) (Q 1 2) := by
  have h := gg_ultrametric μ hEx hGG hGram hdiag
  have h₁ := (hEx 0 1).quasiMeasurePreserving.ae h
  have h₂ := (hEx 0 2).quasiMeasurePreserving.ae h
  filter_upwards [h, h₁, h₂, hGram] with Q hQ hQ₁ hQ₂ hg
  have hs := gram_array_symmetric Q hg
  refine ⟨hQ, ?_, ?_⟩
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide, hs 1 0] using hQ₁
  · simpa only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide, hs 2 0, hs 2 1, hs 1 0,
      min_comm] using hQ₂

lemma scalarArray_ultrametric_triangle (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, UltrametricTriangle (f (Q 0 1)) (f (Q 0 2)) (f (Q 1 2)) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  exact ae_of_ae_map hm.aemeasurable
    (gg_ultrametric_triangle ν (scalarArray_swap_invariant μ hEx hf)
      (scalarArray_gg μ hGG hf) hg hd)

lemma ultrametric_triangle_small_eq {a b c : ℝ} (h : UltrametricTriangle a b c)
    (hab : a < b) : c = a := by
  have hlo : a ≤ c := by simpa only [min_eq_left hab.le] using h.1
  have hhi : c ≤ a := by
    rcases le_total b c with hbc | hcb
    · have : b ≤ a := by simpa only [min_eq_left hbc] using h.2.2
      exact (hab.not_ge this).elim
    · simpa only [min_eq_right hcb] using h.2.2
  exact le_antisymm hhi hlo

lemma ultrametric_sum_no_crossing {a b c x y z : ℝ}
    (hR : UltrametricTriangle a b c) (hT : UltrametricTriangle x y z)
    (hSum : min ((a + x) / 2) ((b + y) / 2) ≤ (c + z) / 2) :
    ¬ (a < b ∧ y < x) := by
  rintro ⟨hab, hyx⟩
  have hc := ultrametric_triangle_small_eq hR hab
  have hz : z = y := ultrametric_triangle_small_eq
    (show UltrametricTriangle y x z from ⟨by simpa only [min_comm] using hT.1,
      hT.2.2, hT.2.1⟩) hyx
  rw [hc, hz] at hSum
  rcases le_total ((a + x) / 2) ((b + y) / 2) with h | h
  · rw [min_eq_left h] at hSum
    linarith
  · rw [min_eq_right h] at hSum
    linarith

theorem joint_gg_no_crossing (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    (hR : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)))
    (hT : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.snd Q)))
    (hdR : ∀ᵐ Q ∂μ, ∀ i, (Q i i).1 ≤ 1)
    (hdT : ∀ᵐ Q ∂μ, ∀ i, (Q i i).2 ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2) := by
  have huR := scalarArray_ultrametric_triangle μ hEx hGG measurable_fst hR hdR
  have huT := scalarArray_ultrametric_triangle μ hEx hGG measurable_snd hT hdT
  let f : ℝ × ℝ → ℝ := fun x => (x.1 + x.2) / 2
  have hf : Measurable f := by fun_prop
  have hG : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)) := by
    filter_upwards [hR, hT] with Q hQ₁ hQ₂ n
    have heq : overlapBlock id n (scalarArray f Q) =
        (1 / 2 : ℝ) • (overlapBlock id n (scalarArray Prod.fst Q) +
          overlapBlock id n (scalarArray Prod.snd Q)) := by
      ext i j
      simp [overlapBlock, scalarArray, f, smul_eq_mul, div_eq_mul_inv, add_mul,
        mul_comm]
    rw [heq]
    exact ((hQ₁ n).add (hQ₂ n)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hd : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1 := by
    filter_upwards [hdR, hdT] with Q hQ₁ hQ₂ i
    dsimp [f]
    linarith [hQ₁ i, hQ₂ i]
  have huS := scalarArray_ultrametric μ hEx hGG hf hG hd
  filter_upwards [huR, huT, huS] with Q hQ₁ hQ₂ hQ₃
  exact ultrametric_sum_no_crossing hQ₁ hQ₂ hQ₃

theorem joint_gg_crossed_regions_null (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ)
    (hNo : ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2))
    (s t : Set (ℝ × ℝ)) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : ∀ u ∈ s, ∀ v ∈ t, u.1 < v.1 ∧ v.2 < u.2) :
    μ {Q | Q 0 1 ∈ s} = 0 ∨ μ {Q | Q 0 1 ∈ t} = 0 := by
  let S : Set (PairedOverlapBlock 2) := {A | A 0 1 ∈ s}
  have hS : MeasurableSet S := hs.preimage
    ((measurable_pi_apply 1).comp (measurable_pi_apply 0))
  have hnull : μ (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hNo] with Q hQ
    rintro ⟨h₁, h₂⟩
    exact hQ (hst (Q 0 1) h₁ (Q 0 2) h₂)
  have hid := hGG 2 (by omega) 0 S hS t ht
  have hzero : μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    simp only [measureReal_def, hnull, ENNReal.toReal_zero]
  have hsum : 0 ≤ ∑ j ∈ (Finset.univ.erase (0 : Fin 2)),
      μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 j ∈ t}) :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hprod : μ.real {Q | Q 0 1 ∈ s} * μ.real {Q | Q 0 1 ∈ t} = 0 := by
    change μ.real (pairedBlock 2 ⁻¹' S) * μ.real {Q | Q 0 1 ∈ t} = 0
    simp only [Fin.val_zero, Nat.cast_ofNat] at hid
    rw [hzero] at hid
    have h₁ := measureReal_nonneg (μ := μ) (s := pairedBlock 2 ⁻¹' S)
    have h₂ := measureReal_nonneg (μ := μ) (s := {Q | Q 0 1 ∈ t})
    nlinarith [mul_nonneg h₁ h₂]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  · right
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)

end SphericalPerceptron
end
end

end OAI
