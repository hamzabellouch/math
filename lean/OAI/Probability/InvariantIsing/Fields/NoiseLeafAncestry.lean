import OAI.Probability.InvariantIsing.Fields.CascadeSeedLeaf

namespace OAI

/-! Shared ancestry read from the sequence of Poisson edge weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def noiseLeafCommonDepth {A B : Type} : (n : ℕ) → NoiseLeaf A n → NoiseLeaf B n → ℕ
  | 0, _, _ => 0
  | n+1, v, w => if v.1 = w.1 then 1 + noiseLeafCommonDepth n v.2.2 w.2.2 else 0

lemma measurable_noiseLeafCommonDepth {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (n : ℕ) : Measurable (fun p : NoiseLeaf A n × NoiseLeaf B n =>
      noiseLeafCommonDepth n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_snd.fst)
      (measurable_const.add (ih.comp (measurable_fst.snd.snd.prodMk measurable_snd.snd.snd)))
      measurable_const

lemma noiseLeafCommonDepth_seed {ι : Type} (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z w : ι → ℝ) (v v' : NoiseLeaf unitInterval n) :
    noiseLeafCommonDepth n (cascadeSeedLeaf n ψ z v) (cascadeSeedLeaf n ψ w v') =
      noiseLeafCommonDepth n v v' := by
  induction n generalizing ψ z w with
  | zero => rfl
  | succ n ih =>
    change (if v.1 = v'.1 then 1 + noiseLeafCommonDepth n
      (cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z v.2.1) v.2.2)
      (cascadeSeedLeaf n (fun j => ψ (j+1)) (w+ψ 0 w v'.2.1) v'.2.2) else 0) = _
    rw [ih]
    rfl

end InvariantIsing

end

end OAI
