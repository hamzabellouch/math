import Mathlib
import OAI.Probability.SphericalField.Fields.Words

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def uniformWeights (k : ℕ) : Fin (k+1) → ℝ := fun _ => 1/(k+1:ℕ)
def uniformExponents (k : ℕ) (i : Fin (k+2)) : ℝ := (i:ℕ)/(k+1:ℕ)

lemma uniformWeights_pos (k : ℕ) (i : Fin (k+1)) : 0 < uniformWeights k i := by
  unfold uniformWeights
  positivity

lemma uniformWeights_sum (k : ℕ) : ∑ i, uniformWeights k i=1 := by
  simp only [uniformWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,one_div]
  exact mul_inv_cancel₀ (by positivity)

lemma uniformExponents_nonneg (k : ℕ) (i : Fin (k+2)) : 0 ≤ uniformExponents k i := by
  unfold uniformExponents
  positivity

lemma uniformExponents_last (k : ℕ) : uniformExponents k (Fin.last (k+1))=1 := by
  simp only [uniformExponents,Fin.val_last]
  exact div_self (by positivity)

lemma stepCumulative_uniformWeights (k : ℕ) (i : Fin k) :
    stepCumulative (uniformWeights k) i=(i.val+1:ℕ)/(k+1:ℕ) := by
  unfold stepCumulative uniformWeights
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun j : Fin (k+1) => j ≤ i.castSucc)=Finset.Iic i.castSucc := by
    ext j; simp
  rw [he,Finset.sum_const,Fin.card_Iic]
  simp only [Fin.val_castSucc,nsmul_eq_mul]
  push_cast
  ring

lemma uniformExponents_castSucc (k : ℕ) (i : Fin (k+1)) :
    uniformExponents k i.castSucc=fieldExponents (uniformWeights k) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [uniformExponents,fieldExponents]
  · simp [uniformExponents,fieldExponents,stepCumulative_uniformWeights]

def sphericalGridValue (n k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sphericalHeatValue n (List.ofFn fun i => (uniformExponents k i,Real.sqrt (v i)))

def sphericalGridDual (k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sInf (finiteSphericalDualValues (uniformWeights k) (varianceLevels (fun i => v i.castSucc))
    (fun i => (uniformWeights_pos k i).le) (uniformWeights_sum k))

lemma sphericalGridValue_eq (n k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sphericalGridValue n k v=finiteSphericalFieldValue n k (uniformWeights k)
      (varianceLevels (fun i => v i.castSucc)) := by
  rw [finiteSphericalFieldValue_eq_heat (uniformWeights k) _ (uniformWeights_pos k)
    (uniformWeights_sum k) (varianceLevels_monotone _ (fun i => hv i.castSucc))
    (varianceLevels_nonneg _ (fun i => hv i.castSucc) 0),fieldVariances_varianceLevels]
  unfold sphericalGridValue sphericalHeatValue
  have hs : ((List.ofFn fun i => (uniformExponents k i,Real.sqrt (v i))).map fun c => c.2^2).sum=
      (∑ i : Fin (k+1), v i.castSucc)+v (Fin.last (k+1)) := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i, (Real.sqrt (v i))^2)=_
    simp only [Real.sq_sqrt (hv _)]
    exact Fin.sum_univ_castSucc v
  have hs' : ((List.ofFn fun i => (fieldExponents (uniformWeights k) i,
      Real.sqrt (v (i : Fin (k+1)).castSucc))).map fun c => c.2^2).sum=∑ i : Fin (k+1), v i.castSucc := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin (k+1), (Real.sqrt (v i.castSucc))^2)=_
    simp only [Real.sq_sqrt (hv _)]
  rw [hs,hs']
  change gaussianGrid (k+2) (uniformExponents k) v _ 0/(n+1:ℕ)-_= _
  rw [gaussianGrid_spherical_last n k _ _ (uniformExponents_nonneg k)
    (hv _) (uniformExponents_last k)]
  simp only [uniformExponents_castSucc]
  unfold gaussianGrid
  have hn : (n+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [hn]
  ring

lemma varianceLevels_continuous (k : ℕ) : Continuous (varianceLevels (k := k)) := by
  apply continuous_pi
  intro i
  unfold varianceLevels
  apply Continuous.div_const
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

lemma sphericalGridValue_compact_uniform (k : ℕ) (H : ℝ) :
    TendstoUniformlyOn (fun n => sphericalGridValue n k) (sphericalGridDual k) atTop
      (Icc (fun _ => 0) (fun _ => H)) := by
  let T : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ) := fun v => varianceLevels (fun i => v i.castSucc)
  have hT : Continuous T := (varianceLevels_continuous k).comp (by fun_prop)
  have hK : IsCompact (T '' Icc (fun _ => 0) (fun _ => H)) := isCompact_Icc.image hT
  have hfield : ∀ h ∈ T '' Icc (fun _ => 0) (fun _ => H), Monotone h ∧ 0 ≤ h 0 := by
    rintro h ⟨v,hv,rfl⟩
    exact ⟨varianceLevels_monotone _ (fun i => hv.1 i.castSucc),
      varianceLevels_nonneg _ (fun i => hv.1 i.castSucc) 0⟩
  have hu := finiteSphericalFieldValue_compact_uniform (uniformWeights k)
    (uniformWeights_pos k) (uniformWeights_sum k) hK hfield
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn v hv
  rw [sphericalGridValue_eq n k v (fun i => hv.1 i)]
  exact hn (T v) ⟨v,hv,rfl⟩

lemma gridVariance_weighted_sum {N : ℕ} (l : List (Fin N×ℝ)) (g : Fin N → ℝ) :
    (∑ i, g i*gridVariance l i)=(l.map fun c => g c.1*c.2).sum := by
  induction l with
  | nil => simp [gridVariance]
  | cons c l ih =>
    rw [gridVariance_cons]
    simp only [mul_add,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons]
    simp only [mul_ite,mul_zero]
    simp [add_comm]

lemma gridVariance_sum {N : ℕ} (l : List (Fin N×ℝ)) :
    (∑ i, gridVariance l i)=(l.map Prod.snd).sum := by
  simpa only [one_mul] using gridVariance_weighted_sum l (fun _ => 1)

lemma sphericalGridValue_compress (n k : ℕ) (l : List (Fin (k+2)×ℝ))
    (hl : l.Pairwise (fun a b => a.1 ≤ b.1)) (hv : ∀ c ∈ l, 0 ≤ c.2) :
    sphericalHeatValue n (l.map fun c => (uniformExponents k c.1,Real.sqrt c.2))=
      sphericalGridValue n k (gridVariance l) := by
  unfold sphericalHeatValue sphericalGridValue
  unfold sphericalHeatValue
  rw [gaussianBackward_compress (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
    (k+2) (uniformExponents k) (uniformExponents_nonneg k) l hl hv]
  congr 1
  rw [List.map_ofFn,List.sum_ofFn,List.map_map]
  change (l.map fun c => (Real.sqrt c.2)^2).sum/2=(∑ i, (Real.sqrt (gridVariance l i))^2)/2
  simp only [Real.sq_sqrt (gridVariance_nonneg l hv _)]
  rw [gridVariance_sum]
  congr 2
  apply List.map_congr_left
  intro c hc
  exact Real.sq_sqrt (hv c hc)

end SphericalPerceptron
end
end

end OAI
