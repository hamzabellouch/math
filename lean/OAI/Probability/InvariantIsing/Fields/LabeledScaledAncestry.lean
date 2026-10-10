import OAI.Probability.InvariantIsing.Fields.PoissonLabeledWeights
import OAI.Probability.InvariantIsing.Fields.NoiseLeafAncestry

namespace OAI

/-! Positive ancestor-dependent reweighting preserves the sampled branch labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing
variable {A S : Type} [MeasurableSpace A]

def ScaledLabelSimple : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → LabeledTree n → MarkForest A n → Prop
  | 0, _, _, _, _, _ => True
  | n+1, c, u, s, ω, z =>
      (∀ a b : ChildLabel, a.2 < (ω.1 a.1).1 → b.2 < (ω.1 b.1).1 →
        c 0 (s,(z a.1 a.2).1) * (ω.1 a.1).2 a.2 =
          c 0 (s,(z b.1 b.2).1) * (ω.1 b.1).2 b.2 → a = b) ∧
      ∀ a : ChildLabel, ScaledLabelSimple n (fun j => c (j+1)) (fun j => u (j+1))
        (u 0 (s,(z a.1 a.2).1)) (ω.2 a.1 a.2) (z a.1 a.2).2

lemma labeledCascade_scaled_simple_ae (n : ℕ) (b : ℕ → ℝ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i p, c i p ≠ 0) (s : S) (z : MarkForest A n) :
    ∀ᵐ ω ∂(labeledCascadeLaw n b : Measure (LabeledTree n)), ScaledLabelSimple n c u s ω z := by
  induction n generalizing b c u s with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    let bs := fun i => b (i+1)
    let Q : Measure (ℕ → ℕ → LabeledTree n) := Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => (labeledCascadeLaw n bs : Measure (LabeledTree n))
    have hchildren : ∀ᵐ ω ∂Q, ∀ a : ChildLabel,
        ScaledLabelSimple n (fun j => c (j+1)) (fun j => u (j+1))
          (u 0 (s,(z a.1 a.2).1)) (ω a.1 a.2) (z a.1 a.2).2 := by
      rw [ae_all_iff]
      intro a
      have hp := (measurePreserving_eval_infinitePi
        (fun _ : ℕ => (labeledCascadeLaw n bs : Measure (LabeledTree n))) a.2).comp
        (measurePreserving_eval_infinitePi
          (fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            (labeledCascadeLaw n bs : Measure (LabeledTree n))) a.1)
      exact hp.quasiMeasurePreserving.tendsto_ae.eventually
        (ih bs _ _ (fun i p => hc (i+1) p) _ (z a.1 a.2).2)
    have hroot := labeledPoisson_scaled_distinct (intensityComponents (powerIntensity (b 0)))
      (fun a : ChildLabel => c 0 (s,(z a.1 a.2).1)) (fun a => hc 0 _)
    have hfst := (measurePreserving_fst
      (μ := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))) (ν := Q)).quasiMeasurePreserving.tendsto_ae.eventually hroot
    have hsnd := (measurePreserving_snd
      (μ := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))) (ν := Q)).quasiMeasurePreserving.tendsto_ae.eventually hchildren
    filter_upwards [hfst,hsnd] with ω hω hω'
    exact ⟨hω,hω'⟩

lemma labeledLeafWeight_active {n : ℕ} (ω : LabeledTree (n+1))
    (v : LabeledLeaf (n+1)) (hv : labeledLeafWeight (n+1) ω v ≠ 0) :
    v.1.2 < (ω.1 v.1.1).1 := by
  by_contra h
  exact hv (by simp [labeledLeafWeight,childLabelWeight,h])

lemma noiseLeafCommonDepth_keep_labeled (n : ℕ) (c : ℕ → S × A → ℝ)
    (u : ℕ → S × A → S) (s : S) (ω : LabeledTree n) (z : MarkForest A n)
    (hω : ScaledLabelSimple n c u s ω z)
    (v w : LabeledLeaf n) (hv : labeledLeafWeight n ω v ≠ 0)
    (hw : labeledLeafWeight n ω w ≠ 0) :
    noiseLeafCommonDepth n
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (ω,z) v))
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (ω,z) w)) = labeledCommonDepth n v w := by
  induction n generalizing c u s with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨a,v⟩
    rcases w with ⟨a',w⟩
    have hva := labeledLeafWeight_active ω (a,v) hv
    have hwa := labeledLeafWeight_active ω (a',w) hw
    have hvt : labeledLeafWeight n (ω.2 a.1 a.2) v ≠ 0 := (mul_ne_zero_iff.mp hv).2
    have hwt : labeledLeafWeight n (ω.2 a'.1 a'.2) w ≠ 0 := (mul_ne_zero_iff.mp hw).2
    by_cases he : a = a'
    · subst a'
      simp only [noiseLeafKeep,labeledNoiseLeaf,noiseLeafCommonDepth,labeledCommonDepth,ite_true]
      rw [ih _ _ _ _ _ (hω.2 a) v w hvt hwt, Nat.add_comm]
    · have hne : c 0 (s,(z a.1 a.2).1) * (ω.1 a.1).2 a.2 ≠
          c 0 (s,(z a'.1 a'.2).1) * (ω.1 a'.1).2 a'.2 :=
        fun hh => he (hω.1 a a' hva hwa hh)
      simp only [noiseLeafKeep,labeledNoiseLeaf,noiseLeafCommonDepth,labeledCommonDepth,
        ite_eq_right he]
      exact ite_eq_right hne

end InvariantIsing

end

end OAI
