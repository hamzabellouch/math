import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TentMatrixPositivity
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSeparatingLevels

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformThresholdCDF
open Classical MeasureTheory ProbabilityTheory

noncomputable def intervalCDF (lo hi d : ℝ) : ℝ := max (min hi d-lo) 0 / (hi-lo)

theorem intervalCDF_bounds {lo hi d : ℝ} (h : lo < hi) :
    0 ≤ intervalCDF lo hi d ∧ intervalCDF lo hi d ≤ 1 := by
  have hh := sub_pos.mpr h
  constructor
  · exact div_nonneg (le_max_right _ _) hh.le
  · apply (div_le_one hh).mpr
    exact max_le (sub_le_sub_right (min_le_left _ _) _) hh.le

theorem intervalCDF_lipschitz {lo hi : ℝ} (h : lo < hi) (d e : ℝ) :
    |intervalCDF lo hi d-intervalCDF lo hi e| ≤ |d-e|/(hi-lo) := by
  have hh := sub_pos.mpr h
  simp only [intervalCDF,← sub_div,abs_div,abs_of_pos hh]
  apply (div_le_div_iff_of_pos_right hh).mpr
  have h₁ := abs_max_sub_max_le_abs (min hi d-lo) (min hi e-lo) 0
  have h₂ := abs_min_sub_min_le_max hi d hi e
  calc
    _ ≤ |(min hi d-lo)-(min hi e-lo)| := h₁
    _ = |min hi d-min hi e| := by congr 1; ring
    _ ≤ |d-e| := by simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (d-e))] using h₂

theorem uniformInterval_Iio {lo hi : ℝ} (h : lo < hi) (d : ℝ) :
    (cond volume (Set.Icc lo hi)).real (Set.Iio d)=intervalCDF lo hi d := by
  rw [measureReal_def,cond_apply measurableSet_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_inv,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr h.le)]
  by_cases hd : d ≤ hi
  · have he : Set.Icc lo hi ∩ Set.Iio d = Set.Ico lo d := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,hx.2.le.trans hd⟩,hx.2⟩⟩
    rw [he,Real.volume_Ico,ENNReal.toReal_ofReal']
    simp [intervalCDF,min_eq_right hd,div_eq_mul_inv,mul_comm]
  · have he : Set.Icc lo hi ∩ Set.Iio d = Set.Icc lo hi := by
      ext x
      exact ⟨fun hx => hx.1,fun hx => ⟨hx,lt_of_le_of_lt hx.2 (lt_of_not_ge hd)⟩⟩
    rw [he,Real.volume_Icc,ENNReal.toReal_ofReal']
    simp [intervalCDF,min_eq_left (le_of_not_ge hd),div_eq_mul_inv,mul_comm]

theorem unit_product_sub_bound {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (hf : ∀i∈S,0 ≤ f i ∧ f i ≤ 1) (hg : ∀i∈S,0 ≤ g i ∧ g i ≤ 1) :
    |(∏i∈S,f i)-(∏i∈S,g i)| ≤ ∑i∈S,|f i-g i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS (j) (hj : j∈S) := hf j (Finset.mem_insert_of_mem hj)
    have hgS (j) (hj : j∈S) := hg j (Finset.mem_insert_of_mem hj)
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hgi := hg i (Finset.mem_insert_self _ _)
    have hp₀ : 0 ≤ ∏j∈S,g j := Finset.prod_nonneg (fun j hj => (hgS j hj).1)
    have hp₁ : (∏j∈S,g j) ≤ 1 := Finset.prod_le_one₀ (fun j hj => (hgS j hj).1) (fun j hj => (hgS j hj).2)
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    calc
      _ = |f i*((∏j∈S,f j)-(∏j∈S,g j))+(f i-g i)*(∏j∈S,g j)| := by congr 1; ring
      _ ≤ |f i*((∏j∈S,f j)-(∏j∈S,g j))|+|(f i-g i)*(∏j∈S,g j)| := abs_add_le _ _
      _ ≤ |(∏j∈S,f j)-(∏j∈S,g j)|+|f i-g i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfi.1,abs_of_nonneg hp₀]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hfi.2)
          (mul_le_of_le_one_right (abs_nonneg _) hp₁)
      _ ≤ _ := by linarith [ih hfS hgS]

end UniformThresholdCDF

section SeparatorCovariance
open Classical MeasureTheory ProbabilityTheory

def directionNoCut {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (z w : SquareFlag a v) : Set ℝ :=
  {t | ∀c, |conjugate c| ≤ t → ¬ FlagSeparates j c z w}

theorem directionNoCut_of_none {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (h : ¬ ∃c,FlagSeparates j c z w) :
    directionNoCut j z w = Set.univ := by
  ext t
  simp only [directionNoCut,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact fun c _ hc => h ⟨c,hc⟩

theorem directionNoCut_of_min {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (c : CutRing) (hc : FlagSeparates j c z w)
    (hmin : ∀ d,FlagSeparates j d z w → |conjugate c| ≤ |conjugate d|) :
    directionNoCut j z w = Set.Iio |conjugate c| := by
  ext t
  constructor
  · intro ht
    exact lt_of_not_ge (fun hle => ht c hle hc)
  · intro ht d hd hsep
    exact not_le_of_gt ht ((hmin d hsep).trans hd)

theorem uniformInterval_isProbability {lo hi : ℝ} (h : lo < hi) :
    IsProbabilityMeasure (cond volume (Set.Icc lo hi)) :=
  cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr h))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

noncomputable def directionNoCutProbability {a : ℕ} {v : ℝ×ℝ}
    (s κ : ℝ) (j : Fin 4) (z w : SquareFlag a v) : ℝ :=
  (cond volume (Set.Icc (κ/s) (2*κ/s))).real (directionNoCut j z w)

theorem directionNoCutProbability_bounds {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (j : Fin 4) (z w : SquareFlag a v) :
    0 ≤ directionNoCutProbability s κ j z w ∧ directionNoCutProbability s κ j z w ≤ 1 := by
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have := uniformInterval_isProbability h
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

theorem separatorMatrix_product {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) :
    separatorMatrix (thresholdLaw s κ) z w = ∏j,directionNoCutProbability s κ j z w := by
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have := uniformInterval_isProbability h
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      Set.univ.pi (fun j => directionNoCut j z w) := by
    ext t
    rw [Set.mem_ofPred_eq,flagChamber_eq_iff]
    simp only [Set.mem_pi,Set.mem_univ,forall_true_left,directionNoCut,Set.mem_ofPred_eq,
      FlagSeparates,not_not]
  rw [separatorMatrix_eq_measure,measureReal_def,he]
  change (Measure.pi (fun _ : Fin 4 => cond volume (Set.Icc (κ/s) (2*κ/s)))
    (Set.univ.pi (fun j => directionNoCut j z w))).toReal = _
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  rfl

theorem directionNoCutProbability_translation_bound {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (u : CutRing×CutRing) (j : Fin 4) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    |directionNoCutProbability s κ j z w-directionNoCutProbability s κ j z' w'| ≤
      |conjugate (integralCutForm a j u)| *s/κ := by
  have he : (∃c,FlagSeparates j c z w) ↔ ∃c,FlagSeparates j c z' w' := by
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨c+integralCutForm a j u,
        (flagSeparates_local_translation u j c z w z' w' hz hw).mpr hc⟩
    · rintro ⟨c,hc⟩
      refine ⟨c-integralCutForm a j u,?_⟩
      apply (flagSeparates_local_translation u j (c-integralCutForm a j u) z w z' w' hz hw).mp
      simpa only [sub_add_cancel] using hc
  by_cases hc : ∃c,FlagSeparates j c z w
  · obtain ⟨c,hc,hcmin⟩ := flagSeparates_exists_min j z w hc
    obtain ⟨d,hd,hdmin⟩ := flagSeparates_exists_min j z' w' (he.mp ⟨c,hc⟩)
    have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
    simp only [directionNoCutProbability,directionNoCut_of_min j z w c hc hcmin,
      directionNoCut_of_min j z' w' d hd hdmin,uniformInterval_Iio h]
    have hmin := separating_min_translation_bound u j z w z' w' hz hw c d hc hd hcmin hdmin
    calc
      _ ≤ abs (|conjugate c|-|conjugate d|)/(2*κ/s-κ/s) := intervalCDF_lipschitz h _ _
      _ ≤ |conjugate (integralCutForm a j u)|/(2*κ/s-κ/s) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr h)).mpr hmin
      _ = _ := by field_simp; ring
  · have hc' := he.not.mp hc
    simp only [directionNoCutProbability,directionNoCut_of_none j z w hc,
      directionNoCut_of_none j z' w' hc',sub_self,abs_zero]
    positivity

theorem separatorMatrix_translation_bound {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (u : CutRing×CutRing) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    |separatorMatrix (thresholdLaw s κ) z w-separatorMatrix (thresholdLaw s κ) z' w'| ≤
      (∑j : Fin 4,|conjugate (integralCutForm a j u)|)*s/κ := by
  rw [separatorMatrix_product hs hκ,separatorMatrix_product hs hκ]
  calc
    _ ≤ ∑j : Fin 4,|directionNoCutProbability s κ j z w-directionNoCutProbability s κ j z' w'| :=
      unit_product_sub_bound Finset.univ _ _
        (fun j _ => directionNoCutProbability_bounds hs hκ j z w)
        (fun j _ => directionNoCutProbability_bounds hs hκ j z' w')
    _ ≤ ∑j : Fin 4,|conjugate (integralCutForm a j u)| *s/κ :=
      Finset.sum_le_sum (fun j _ => directionNoCutProbability_translation_bound hs hκ u j z w z' w' hz hw)
    _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul]

end SeparatorCovariance

end SimpleAmenable
end
end

end OAI
