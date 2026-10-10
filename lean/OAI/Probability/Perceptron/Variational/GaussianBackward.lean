import Mathlib
import OAI.Probability.Perceptron.Variational.CompactGGFiniteCode

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianBackward (μ : Measure E) : List (ℝ×ℝ) → (E → ℝ) → E → ℝ
  | [], f => f
  | (p,σ)::l, f => gaussianEntropic μ p σ (gaussianBackward μ l f)

lemma gaussianBackward_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) :
    LipschitzWith L (gaussianBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons a l ih =>
    exact gaussianEntropic_lipschitz μ (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)))
      (hl a (List.mem_cons_self))

lemma gaussianBackward_add_const {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) (c : ℝ) :
    gaussianBackward μ l (fun x => f x+c)=(fun x => gaussianBackward μ l f x+c) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have htail := fun b hb => hl b (List.mem_cons_of_mem a hb)
    simp only [gaussianBackward,ih htail]
    funext x
    exact gaussianEntropic_add_const μ (gaussianBackward_lipschitz μ hf l htail) _ _ _ _

lemma gaussianBackward_append {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsGaussian μ] (l m : List (ℝ×ℝ)) (f : E → ℝ) :
    gaussianBackward μ (l++m) f=gaussianBackward μ l (gaussianBackward μ m f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,gaussianBackward,ih]

lemma gaussianBackward_mono {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) (hfg : ∀ x, f x ≤ g x) :
    ∀ x, gaussianBackward μ l f x ≤ gaussianBackward μ l g x := by
  induction l with
  | nil => exact hfg
  | cons a l ih =>
    have htail := fun b hb => hl b (List.mem_cons_of_mem a hb)
    exact gaussianEntropic_mono μ (gaussianBackward_lipschitz μ hf l htail)
      (gaussianBackward_lipschitz μ hg l htail) (hl a List.mem_cons_self) a.2 (ih htail)

lemma gaussianBackward_bounded_difference {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) {C : ℝ}
    (hfg : ∀ x, |f x-g x| ≤ C) (x : E) :
    |gaussianBackward μ l f x-gaussianBackward μ l g x| ≤ C := by
  induction l generalizing x with
  | nil => exact hfg x
  | cons a l ih =>
    have htail := fun b hb => hl b (List.mem_cons_of_mem a hb)
    apply entropicMean_bounded_difference μ
      (fun t => gaussian_integrable_exp_lipschitz μ (gaussianBackward_lipschitz μ hf l htail) t a.2 x)
      (fun t => gaussian_integrable_exp_lipschitz μ (gaussianBackward_lipschitz μ hg l htail) t a.2 x)
      (hl a List.mem_cons_self)
    exact ae_of_all _ fun y => ih htail (x+a.2 • y)

lemma gaussianBackward_mono_parameters {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (a b : ℝ → ℝ)
    (ha : ∀ c ∈ l, 0 ≤ a c.1) (hab : ∀ c ∈ l, a c.1 ≤ b c.1) :
    ∀ x, gaussianBackward μ (l.map fun c => (a c.1,c.2)) f x ≤
      gaussianBackward μ (l.map fun c => (b c.1,c.2)) f x := by
  have hb : ∀ c ∈ l, 0 ≤ b c.1 := fun c hc => (ha c hc).trans (hab c hc)
  induction l with
  | nil => intro x; exact le_rfl
  | cons c l ih =>
    have ha' := fun d hd => ha d (List.mem_cons_of_mem c hd)
    have hb' := fun d hd => hb d (List.mem_cons_of_mem c hd)
    have hab' := fun d hd => hab d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact ha' e he
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact hb' e he
    intro x
    simp only [List.map_cons,gaussianBackward]
    calc
      _ ≤ gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x :=
        gaussianEntropic_mono_parameter μ hla c.2 x (hab c List.mem_cons_self)
      _ ≤ _ := gaussianEntropic_mono μ hla hlb (hb c List.mem_cons_self) c.2 (ih ha' hab' hb') x

lemma gaussianBackward_parameter_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (a b : ℝ → ℝ) {S : ℝ}
    (ha : ∀ c ∈ l, a c.1 ∈ Icc (0:ℝ) 1) (hb : ∀ c ∈ l, b c.1 ∈ Icc (0:ℝ) 1)
    (hσ : ∀ c ∈ l, c.2 ∈ Icc (0:ℝ) S) : ∀ x,
    |gaussianBackward μ (l.map fun c => (a c.1,c.2)) f x-
      gaussianBackward μ (l.map fun c => (b c.1,c.2)) f x| ≤
      gaussianEntropicParamConstant μ L S*(l.map fun c => c.2^2*|a c.1-b c.1|).sum := by
  induction l with
  | nil => intro x; simp [gaussianBackward]
  | cons c l ih =>
    have ha' := fun d hd => ha d (List.mem_cons_of_mem c hd)
    have hb' := fun d hd => hb d (List.mem_cons_of_mem c hd)
    have hσ' := fun d hd => hσ d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (ha' e he).1
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (hb' e he).1
    intro x
    simp only [List.map_cons,List.sum_cons,gaussianBackward]
    have H1 := gaussianEntropic_parameter_bound μ hla (ha c List.mem_cons_self)
      (hb c List.mem_cons_self) (hσ c List.mem_cons_self).1 (hσ c List.mem_cons_self).2 x
    have H2 := entropicMean_bounded_difference μ
      (fun t => gaussian_integrable_exp_lipschitz μ hla t c.2 x)
      (fun t => gaussian_integrable_exp_lipschitz μ hlb t c.2 x) (hb c List.mem_cons_self).1
      (ae_of_all _ fun y => ih ha' hb' hσ' (x+c.2 • y))
    have HT := abs_sub_le (gaussianEntropic μ (a c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x)
    dsimp [entropicMean] at H2
    change |gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x-
      gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x| ≤ _ at H2
    nlinarith

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianBackward_merge {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ c ∈ l, 0 ≤ c.1) {p : ℝ} (hp : 0 ≤ p) (σ τ : ℝ) :
    gaussianBackward (stdGaussian E) ((p,σ)::(p,τ)::l) f=
      gaussianBackward (stdGaussian E) ((p,Real.sqrt (σ^2+τ^2))::l) f := by
  funext x
  exact gaussianEntropic_semigroup (gaussianBackward_lipschitz (stdGaussian E) hf l hl) hp σ τ x

lemma gaussianBackward_delete_zero {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ c ∈ l, 0 ≤ c.1) (p : ℝ) :
    gaussianBackward (stdGaussian E) ((p,0)::l) f=gaussianBackward (stdGaussian E) l f := by
  funext x
  exact gaussianEntropic_variance_zero (gaussianBackward_lipschitz (stdGaussian E) hf l hl) p x

end SphericalPerceptronFreeEnergy
end

end OAI
