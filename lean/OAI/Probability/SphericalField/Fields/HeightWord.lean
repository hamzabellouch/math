import Mathlib
import OAI.Probability.SphericalField.Fields.HeightPartition

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def extendedFieldExponents {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+2)) : ℝ :=
  ∑ r, if r.castSucc < i then w r else 0

def finiteFieldCDFLeft {d : ℕ} (w h : Fin (d+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ r, if h r < t then w r else 0

lemma extendedFieldExponents_castSucc {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    extendedFieldExponents w i.castSucc=fieldExponents w i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [extendedFieldExponents,fieldExponents]
  · unfold extendedFieldExponents fieldExponents
    simp only [Fin.cases_succ,stepCumulative]
    apply Finset.sum_congr rfl
    intro r _
    have he : r.castSucc < i.succ.castSucc ↔ r ≤ i.castSucc := by
      simp only [Fin.lt_def,Fin.le_def,Fin.val_castSucc,Fin.val_succ]
      omega
    simp only [he]

lemma extendedFieldExponents_last {d : ℕ} (w : Fin (d+1) → ℝ) :
    extendedFieldExponents w (Fin.last (d+1))=∑ r, w r := by
  simp [extendedFieldExponents,Fin.castSucc_lt_last]

lemma extendedFieldExponents_nonneg {d : ℕ} (w : Fin (d+1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i : Fin (d+2)) : 0 ≤ extendedFieldExponents w i := by
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> first | exact hw r | rfl

lemma extendedFieldExponents_heightIndex {d : ℕ} (w h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) : extendedFieldExponents w (heightIndex h t)=finiteFieldCDFLeft w h t := by
  simp only [extendedFieldExponents,finiteFieldCDFLeft,lt_heightIndex_iff h hh]

lemma sphericalHeatValue_compress (n N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (l : List (Fin N×ℝ)) (hl : l.Pairwise (fun a b => a.1 ≤ b.1))
    (hv : ∀ c ∈ l, 0 ≤ c.2) :
    sphericalHeatValue n (l.map fun c => (p c.1,Real.sqrt c.2))=
      sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (gridVariance l i))) := by
  unfold sphericalHeatValue
  rw [gaussianBackward_compress (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N p hp l hl hv]
  congr 1
  rw [List.map_ofFn,List.sum_ofFn,List.map_map]
  change (l.map fun c => (Real.sqrt c.2)^2).sum/2=(∑ i, (Real.sqrt (gridVariance l i))^2)/2
  simp only [Real.sq_sqrt (gridVariance_nonneg l hv _)]
  rw [gridVariance_sum]
  congr 2
  apply List.map_congr_left
  intro c hc
  exact Real.sq_sqrt (hv c hc)

lemma sphericalHeatValue_drop_last_one (n d : ℕ) (p v : Fin (d+2) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hv : ∀ i, 0 ≤ v i) (hpl : p (Fin.last (d+1))=1) :
    sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (v i)))=
      sphericalHeatValue n (List.ofFn fun i : Fin (d+1) => (p i.castSucc,Real.sqrt (v i.castSucc))) := by
  unfold sphericalHeatValue
  have he := congrFun (gaussianGrid_spherical_last n d p v hp (hv _) hpl) 0
  unfold gaussianGrid at he
  rw [he]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,Real.sq_sqrt (hv _)]
  rw [Fin.sum_univ_castSucc v]
  have hn : (n+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [hn]
  ring

lemma finiteSphericalFieldValue_height_word {d K : ℕ} (w h : Fin (d+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    (z : Fin (K+1) → ℝ) (hz : Monotone z) (hz0 : z 0=0)
    (hm : ∀ i, h i ∈ Set.range z) (n : ℕ) :
    finiteSphericalFieldValue n d w h=sphericalHeatValue n
      (List.ofFn fun j => (finiteFieldCDFLeft w h (z j.succ),Real.sqrt (heightVariances z j))) := by
  let l := List.ofFn fun j => (heightIndex h (z j.succ),heightVariances z j)
  have hl : l.Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact heightIndex_monotone h (hz (Fin.succ_le_succ_iff.mpr hij.le))
  have hv : ∀ c ∈ l, 0 ≤ c.2 := by
    intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    exact heightVariances_nonneg z hz j
  have he := sphericalHeatValue_compress n (d+2) (extendedFieldExponents w)
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) l hl hv
  dsimp only [l] at he
  simp only [List.map_ofFn,Function.comp_def,extendedFieldExponents_heightIndex w h hh] at he
  rw [he,sphericalHeatValue_drop_last_one n d _ _
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) (gridVariance_nonneg l hv)
    (by rw [extendedFieldExponents_last,hw1])]
  have hvf : (fun i => gridVariance l i.castSucc)=fieldVariances d h := by
    have hpref : varianceLevels (fun i => gridVariance l i.castSucc)=h := by
      funext i
      exact heightIndex_grid_prefix h hh z hz hz0 hm i
    rw [← hpref,fieldVariances_varianceLevels]
  simp only [extendedFieldExponents_castSucc]
  change finiteSphericalFieldValue n d w h=sphericalHeatValue n
    (List.ofFn fun i => (fieldExponents w i,Real.sqrt ((fun i => gridVariance l i.castSucc) i)))
  rw [hvf]
  exact finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0 n

end SphericalPerceptron
end
end

end OAI
