import OAI.Probability.InvariantIsing.Fields.CascadeSeedRegular

namespace OAI

/-! The weight-preserving leaf map for ancestor-dependent vector marks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def cascadeSeedLeaf : (n : ℕ) →
    (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) → (ι → ℝ) →
      NoiseLeaf unitInterval n → NoiseLeaf (ι → ℝ) n
  | 0, _, _, _ => PUnit.unit
  | n+1, ψ, z, v =>
    (v.1,(ψ 0 z v.2.1,
      cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z v.2.1) v.2.2))

lemma measurable_cascadeSeedLeaf (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) :
    Measurable (fun p : (ι → ℝ) × NoiseLeaf unitInterval n => cascadeSeedLeaf n ψ p.1 p.2) := by
  induction n generalizing ψ with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun p : (ι → ℝ) × NoiseLeaf unitInterval (n+1) => ψ 0 p.1 p.2.2.1) :=
      (hψ 0).comp (measurable_fst.prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (measurable_fst.comp measurable_snd).prodMk (hm.prodMk
      ((ih _ (fun i => hψ (i+1))).comp
        ((measurable_fst.add hm).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

lemma cascadeSeedLeaf_forget (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (z : ι → ℝ) (v : NoiseLeaf unitInterval n) :
    noiseLeafForget (ι → ℝ) n (cascadeSeedLeaf n ψ z v) = noiseLeafForget unitInterval n v := by
  induction n generalizing ψ z with
  | zero => rfl
  | succ n ih =>
    change (v.1,noiseLeafForget (ι → ℝ) n
      (cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z v.2.1) v.2.2)) = _
    rw [ih]
    rfl

end InvariantIsing

end

end OAI
