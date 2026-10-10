import Mathlib
import OAI.Probability.SphericalField.Fields.GridGap
import OAI.Probability.SphericalField.Quantiles.RoundGrid

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma gridVariance_ofFn_le_sum {K N : ℕ} (A : Fin N → Fin K) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (i : Fin K) :
    gridVariance (List.ofFn fun r => (A r,v r)) i ≤ ∑ r, v r := by
  simp only [gridVariance,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_le_sum
  intro r _
  dsimp only [Function.comp_apply]
  split_ifs <;> first | rfl | exact hv r

lemma sphericalGridValue_tendsto (k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Tendsto (fun n => sphericalGridValue n k v) atTop (𝓝 (sphericalGridDual k v)) := by
  have hu := sphericalGridValue_compact_uniform k (∑ i, v i)
  apply hu.tendsto_at
  exact ⟨hv,fun i => Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)⟩

lemma finiteSphericalFieldValue_tendsto_dual {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
      (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1))) := by
  obtain ⟨q,hq,hq1,hleast,hlim⟩ := finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh hh0
  exact hlim

theorem finiteSphericalFieldValue_all_depths_uniform (H : ℝ) (hH : 0 ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (w h : Fin (d+1) → ℝ)
      (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1),
      Monotone h → 0 ≤ h 0 → h (Fin.last d) ≤ H →
      |finiteSphericalFieldValue n d w h-
        sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)| < ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2*H/ε)
  have hgrid_pos : (0 : ℝ) < (k+1:ℕ) := by
    push_cast
    exact add_pos ((div_nonneg (mul_nonneg (by norm_num) hH) hε.le).trans_lt hk)
      zero_lt_one
  have hδ : 2*H/(2*(k+1:ℕ)) < ε/2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hgrid_pos)).mpr
    have ht := (div_lt_iff₀ hε).mp hk
    push_cast
    nlinarith
  have hu := sphericalGridValue_compact_uniform k (2*H)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu (ε/2) (half_pos hε)] with n hn d w h hw hw1 hh hh0 hhH
  let p : Fin (d+1) → Time := fun i => ⟨fieldExponents w i,
    fieldExponents_nonneg w hw i,(fieldExponents_lt_one w hw hw1 i).le⟩
  let v := fieldVariances d h
  have hv := fieldVariances_nonneg d h hh hh0
  have hp : Monotone p := fun i j hij => (fieldExponents_strictMono w hw).monotone hij
  let A : Fin (k+2) → ℝ := gridVariance (List.ofFn fun i => (gridFloor k (p i),v i))
  let B : Fin (k+2) → ℝ := gridVariance (List.ofFn fun i => (gridCeil k (p i),v i))
  have hA : ∀ i, 0 ≤ A i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hv i
  have hB : ∀ i, 0 ≤ B i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hv i
  have hsum : (∑ i, v i) ≤ 2*H := by
    rw [show (∑ i, v i)=2*h (Fin.last d) from fieldVariances_sum d h]
    linarith
  have haK : A ∈ Icc (fun _ => 0) (fun _ => 2*H) :=
    ⟨hA,fun i => (gridVariance_ofFn_le_sum _ v hv i).trans hsum⟩
  have hbK : B ∈ Icc (fun _ => 0) (fun _ => 2*H) :=
    ⟨hB,fun i => (gridVariance_ofFn_le_sum _ v hv i).trans hsum⟩
  have haerr := hn A haK
  have hberr := hn B hbK
  rw [Real.dist_eq,abs_lt] at haerr hberr
  have hbr (m : ℕ) : sphericalGridValue m k A ≤ finiteSphericalFieldValue m d w h ∧
      finiteSphericalFieldValue m d w h ≤ sphericalGridValue m k B := by
    rw [finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0 m]
    exact sphericalGridValue_round_bracket m k (d+1) p v hp hv
  have hpLim := finiteSphericalFieldValue_tendsto_dual w h hw hw1 hh hh0
  have haLim := sphericalGridValue_tendsto k A hA
  have hbLim := sphericalGridValue_tendsto k B hB
  have haDual := le_of_tendsto_of_tendsto haLim hpLim (Eventually.of_forall (fun m => (hbr m).1))
  have hbDual := le_of_tendsto_of_tendsto hpLim hbLim (Eventually.of_forall (fun m => (hbr m).2))
  have hgap : |sphericalGridDual k A-sphericalGridDual k B| < ε/2 :=
    (sphericalGridDual_step_gap (fun i => gridFloor k (p i)) (fun i => gridCeil k (p i)) v hv
      (fun i => gridFloor_le_gridCeil k (p i)) (fun i => gridCeil_le_gridFloor_add_one k (p i))).trans_lt
      ((div_le_div_of_nonneg_right hsum (by positivity)).trans_lt hδ)
  rw [abs_lt] at hgap ⊢
  have hnbr := hbr n
  constructor <;> linarith

end SphericalPerceptron
end
end

end OAI
