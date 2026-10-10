import OAI.NumberTheory.TotientAsymptotic.SimplexScaling
import OAI.NumberTheory.TotientAsymptotic.PrefixCoordinates

namespace OAI

/-! Diagonal contraction imposes strict Ford rows while preserving prime order. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixRegion_coordinate_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (i : Fin N) : 0 ≤ u i := by
  rw [prefixLinear_coordinate N u i]
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (g_pos _).le (hu.1 j)
  · exact le_rfl

def contractedPrefix (N : ℕ) (B : ℝ) (β : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {v | (∀ i,0 ≤ v i) ∧ StrictAnti v ∧
    (∀ i,(∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ v i/β i) ∧
    (∑ i : Fin N,a (i.val+1)*v i) ≤ B}

lemma prefix_contraction {N : ℕ} {B : ℝ} {β κ : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) (hκ : ∀ i,1 ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u) :
    simplexScale κ u ∈ contractedPrefix N B β := by
  have hkpos (i) : 0 < κ i := zero_lt_one.trans_le (hκ i)
  have hbpos (i) : 0 < β i := zero_lt_one.trans_le (hβ i)
  have hu0 := prefixRegion_coordinate_nonneg hu
  have hmono {i j : Fin N} (hij : i < j) : κ i ≤ κ j := by
    have hh := mul_le_mul_of_nonneg_right (hβ i) (hkpos i).le
    have hh' : κ i ≤ β i*κ i := by simpa only [one_mul] using hh
    exact hh'.trans (hstep i j hij)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [simplexScale_apply]
    exact div_nonneg (hu0 i) (hkpos i).le
  · intro i j hij
    simp only [simplexScale_apply]
    exact (div_le_div_of_nonneg_left (hu0 j) (hkpos i) (hmono hij)).trans_lt
      ((div_lt_div_iff_of_pos_right (hkpos i)).mpr (horder hij))
  · intro i
    simp only [simplexScale_apply]
    have hsum : (∑ j : Fin N,if i < j then a (j.val-i.val)*(u j/κ j) else 0) ≤
        (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0)/(β i*κ i) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · calc
          _ = (a (j.val-i.val)*u j)/κ j := by ring
          _ ≤ _ := div_le_div_of_nonneg_left
            (mul_nonneg (a_pos (by have := hij; simp only [Fin.lt_def] at this; omega)).le
              (hu0 j)) (mul_pos (hbpos i) (hkpos i)) (hstep i j hij)
      · simp
    have hrow := hu.1 i
    rw [prefixLinear_apply] at hrow
    have hrow' : (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0) ≤ u i := by
      change 0 ≤ u i-_ at hrow
      linarith only [hrow]
    have hh := hsum.trans (div_le_div_of_nonneg_right hrow'
      (mul_pos (hbpos i) (hkpos i)).le)
    convert hh using 1
    ring
  · simp only [simplexScale_apply]
    apply le_trans _ (by simpa only [sub_zero] using hu.2)
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (a (i.val+1)*u i)/κ i := by ring
      _ ≤ a (i.val+1)*u i := div_le_self
        (mul_nonneg (a_pos (by omega)).le (hu0 i)) (hκ i)

lemma prefix_contraction_gap {N : ℕ} {B : ℝ} {β κ : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) (hκ : ∀ i,1 ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u)
    {i j : Fin N} (hij : i < j) :
    simplexScale κ u j ≤ simplexScale κ u i/β i := by
  have hk (r) : 0 < κ r := zero_lt_one.trans_le (hκ r)
  have hb : 0 < β i := zero_lt_one.trans_le (hβ i)
  simp only [simplexScale_apply]
  calc
    _ ≤ u i/κ j := div_le_div_of_nonneg_right (horder hij).le (hk j).le
    _ ≤ u i/(β i*κ i) := div_le_div_of_nonneg_left
      (prefixRegion_coordinate_nonneg hu i) (mul_pos hb (hk i)) (hstep i j hij)
    _ = _ := by ring

lemma reciprocal_enlargement_contracts {N : ℕ} {B : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ r,1 ≤ β r) {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u) :
    simplexScale (enlargementScale β) u ∈
      contractedPrefix N B (fun i => β (i.val+1)) :=
  prefix_contraction (fun i => hβ (i.val+1))
    (fun i => (hβ 0).trans (enlargementScale_top hβ i))
    (enlargementScale_step hβ) hu horder

lemma reciprocal_enlargement_top {N : ℕ} {B : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ r,1 ≤ β r) {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) :
    (∑ i : Fin N,a (i.val+1)*simplexScale (enlargementScale β) u i) ≤ B/β 0 := by
  have hb : 0 < β 0 := zero_lt_one.trans_le (hβ 0)
  simp only [simplexScale_apply]
  calc
    _ ≤ (∑ i : Fin N,a (i.val+1)*u i)/β 0 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = (a (i.val+1)*u i)/enlargementScale β i := by ring
        _ ≤ _ := div_le_div_of_nonneg_left
          (mul_nonneg (a_pos (by omega)).le (prefixRegion_coordinate_nonneg hu i))
          hb (enlargementScale_top hβ i)
    _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [sub_zero] using hu.2) hb.le

lemma contractedPrefix_subset_prefixRegion {N : ℕ} {B : ℝ} {β : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) : contractedPrefix N B β ⊆ prefixRegion N B 0 0 := by
  intro v hv
  refine ⟨?_,by simpa only [sub_zero] using hv.2.2.2⟩
  intro i
  have hh := (hv.2.2.1 i).trans (div_le_self (hv.1 i) (hβ i))
  rw [prefixLinear_apply]
  change 0 ≤ v i-_
  linarith only [hh]

lemma measurableSet_contractedPrefix (N : ℕ) (B : ℝ) (β : Fin N → ℝ) :
    MeasurableSet (contractedPrefix N B β) := by
  have horder : MeasurableSet {v : Fin N → ℝ | StrictAnti v} := by
    change MeasurableSet {v : Fin N → ℝ | ∀ i j,i < j → v j < v i}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hij : i < j
    · simpa [hij] using
        (measurableSet_lt
          (by fun_prop : Measurable (fun v : Fin N → ℝ => v j))
          (by fun_prop : Measurable (fun v : Fin N → ℝ => v i)))
    · simp [hij]
  change MeasurableSet ({v : Fin N → ℝ | ∀ i,0 ≤ v i} ∩
    ({v : Fin N → ℝ | StrictAnti v} ∩
      ({v : Fin N → ℝ | ∀ i,
        (∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ v i/β i} ∩
        {v : Fin N → ℝ | (∑ i : Fin N,a (i.val+1)*v i) ≤ B})))
  apply MeasurableSet.inter _ (horder.inter (MeasurableSet.inter ?_ ?_))
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · rw [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => ?_)
    have heq : (fun v : Fin N → ℝ =>
        ∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) =
        (fun v => v i-prefixLinear N v i) := by
      ext v
      rw [prefixLinear_apply]
      ring
    apply measurableSet_le _ (by fun_prop)
    rw [heq]
    exact (measurable_pi_apply i).sub ((measurable_pi_apply i).comp
      (prefixLinear N).continuous_of_finiteDimensional.measurable)
  · exact measurableSet_le (by fun_prop) measurable_const

lemma ordered_prefix_contraction_volume {N : ℕ} (hN : 0 < N) (B : ℝ)
    {β κ : Fin N → ℝ} (hβ : ∀ i,1 ≤ β i) (hκ : ∀ i,1 ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j) :
    volume.real {u : Fin N → ℝ | u ∈ prefixRegion N B 0 0 ∧ StrictAnti u}/
      (∏ i : Fin N,κ i) ≤ volume.real (contractedPrefix N B β) := by
  have hp : 0 < ∏ i : Fin N,κ i := Finset.prod_pos
    (fun i _ => zero_lt_one.trans_le (hκ i))
  have hdet : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hsub : {u : Fin N → ℝ | u ∈ prefixRegion N B 0 0 ∧ StrictAnti u} ⊆
      simplexScale κ ⁻¹' contractedPrefix N B β := by
    intro u hu
    exact prefix_contraction hβ hκ hstep hu.1 hu.2
  have hmeasure := measure_mono (μ:=volume) hsub
  rw [←Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable
    (measurableSet_contractedPrefix N B β),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet,simplexScale_det,inv_inv,
    abs_of_pos hp,Measure.smul_apply,smul_eq_mul] at hmeasure
  have hfinite : volume (contractedPrefix N B β) ≠ ⊤ := by
    apply measure_ne_top_of_subset (contractedPrefix_subset_prefixRegion hβ)
    rw [volume_prefixRegion_explicit N hN]
    exact ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono (show
      ENNReal.ofReal (∏ i : Fin N,κ i)*volume (contractedPrefix N B β) ≠ ⊤
        from ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hmeasure
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] at hh
  apply (div_le_iff₀ hp).mpr
  simpa only [Measure.real,mul_comm] using hh

end TotientAsymptotic

end

end OAI
