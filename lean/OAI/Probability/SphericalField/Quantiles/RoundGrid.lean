import Mathlib
import OAI.Probability.SphericalField.Fields.UniformGrid

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def gridFloor (k : ℕ) (p : Time) : Fin (k+2) :=
  ⟨Nat.floor ((k+1:ℕ)*(p:ℝ)),by
    have hs : (k+1:ℕ)*(p:ℝ) ≤ (k+1:ℕ) := by nlinarith [p.2.2]
    have h : Nat.floor ((k+1:ℕ)*(p:ℝ)) ≤ k+1 := by
      exact Nat.floor_le_of_le hs
    omega⟩

def gridCeil (k : ℕ) (p : Time) : Fin (k+2) :=
  ⟨Nat.ceil ((k+1:ℕ)*(p:ℝ)),by
    have hs : (k+1:ℕ)*(p:ℝ) ≤ (k+1:ℕ) := by nlinarith [p.2.2]
    have h := Nat.ceil_le.mpr hs
    omega⟩

lemma gridFloor_mono (k : ℕ) : Monotone (gridFloor k) := by
  intro p q hpq
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left hpq (by positivity)

lemma gridCeil_mono (k : ℕ) : Monotone (gridCeil k) := by
  intro p q hpq
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left hpq (by positivity)

lemma gridFloor_le_gridCeil (k : ℕ) (p : Time) : gridFloor k p ≤ gridCeil k p :=
  Nat.floor_le_ceil _

lemma gridCeil_le_gridFloor_add_one (k : ℕ) (p : Time) :
    (gridCeil k p).val ≤ (gridFloor k p).val+1 := Nat.ceil_le_floor_add_one _

lemma uniformExponents_gridFloor_le (k : ℕ) (p : Time) : uniformExponents k (gridFloor k p) ≤ p := by
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (k+1:ℕ))).mpr
  dsimp [gridFloor]
  simpa only [mul_comm] using Nat.floor_le (show 0 ≤ (k+1:ℕ)*(p:ℝ) from mul_nonneg (by positivity) p.2.1)

lemma le_uniformExponents_gridCeil (k : ℕ) (p : Time) : (p:ℝ) ≤ uniformExponents k (gridCeil k p) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (k+1:ℕ))).mpr
  dsimp [gridCeil]
  simpa only [mul_comm] using (Nat.le_ceil ((k+1:ℕ)*(p:ℝ)))

lemma gaussianBackward_ofFn_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (a b σ : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (x : E) :
    gaussianBackward (stdGaussian E) (List.ofFn fun i => (a i,σ i)) f x ≤
      gaussianBackward (stdGaussian E) (List.ofFn fun i => (b i,σ i)) f x := by
  induction N generalizing x with
  | zero => simp [gaussianBackward]
  | succ N ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [gaussianBackward]
    have hla : LipschitzWith L (gaussianBackward (stdGaussian E) (List.ofFn fun i => (a i.succ,σ i.succ)) f) := by
      apply gaussianBackward_lipschitz _ hf
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact ha i.succ
    have hlb : LipschitzWith L (gaussianBackward (stdGaussian E) (List.ofFn fun i => (b i.succ,σ i.succ)) f) := by
      apply gaussianBackward_lipschitz _ hf
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact (ha i.succ).trans (hab i.succ)
    calc
      _ ≤ gaussianEntropic (stdGaussian E) (b 0) (σ 0)
          (gaussianBackward (stdGaussian E) (List.ofFn fun i => (a i.succ,σ i.succ)) f) x :=
        gaussianEntropic_mono_parameter _ hla _ _ (hab 0)
      _ ≤ _ := gaussianEntropic_mono _ hla hlb ((ha 0).trans (hab 0)) _
        (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => σ i.succ)
          (fun i => ha i.succ) (fun i => hab i.succ)) x

lemma sphericalHeatValue_ofFn_mono (n N : ℕ) (a b σ : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    sphericalHeatValue n (List.ofFn fun i => (a i,σ i)) ≤
      sphericalHeatValue n (List.ofFn fun i => (b i,σ i)) := by
  unfold sphericalHeatValue
  simp only [List.map_ofFn]
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact gaussianBackward_ofFn_mono (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N a b σ ha hab 0

lemma sphericalGridValue_round_bracket (n k N : ℕ) (p : Fin N → Time) (v : Fin N → ℝ)
    (hp : Monotone p) (hv : ∀ i, 0 ≤ v i) :
    sphericalGridValue n k (gridVariance (List.ofFn fun i => (gridFloor k (p i),v i))) ≤
      sphericalHeatValue n (List.ofFn fun i => ((p i:ℝ),Real.sqrt (v i))) ∧
    sphericalHeatValue n (List.ofFn fun i => ((p i:ℝ),Real.sqrt (v i))) ≤
      sphericalGridValue n k (gridVariance (List.ofFn fun i => (gridCeil k (p i),v i))) := by
  have hp₁ : (List.ofFn fun i => (gridFloor k (p i),v i)).Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact gridFloor_mono k (hp hij.le)
  have hp₂ : (List.ofFn fun i => (gridCeil k (p i),v i)).Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact gridCeil_mono k (hp hij.le)
  have hv₁ : ∀ c ∈ List.ofFn (fun i => (gridFloor k (p i),v i)), 0 ≤ c.2 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hv i
  have hv₂ : ∀ c ∈ List.ofFn (fun i => (gridCeil k (p i),v i)), 0 ≤ c.2 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hv i
  rw [← sphericalGridValue_compress n k _ hp₁ hv₁,← sphericalGridValue_compress n k _ hp₂ hv₂]
  simp only [List.map_ofFn]
  constructor
  · exact sphericalHeatValue_ofFn_mono n N _ _ _ (fun i => uniformExponents_nonneg k _)
      (fun i => uniformExponents_gridFloor_le k _)
  · exact sphericalHeatValue_ofFn_mono n N _ _ _ (fun i => (p i).2.1)
      (fun i => le_uniformExponents_gridCeil k _)

end SphericalPerceptron
end
end

end OAI
