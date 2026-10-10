import OAI.Dynamics.ConditionalShuffle.Exchangeable

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma physicalFlow_finSum {α : Type*} [Fintype α] (d : ℕ) (B : Position (d+1) → Bool)
    (a : α → ℝ) (w : α → Position (d+1) → ℝ) (c : Position d → Bool) (y) :
    physicalFlow d B (fun x => ∑ i, a i * w i x) c y =
      ∑ i, a i * physicalFlow d B (w i) c y := by
  rw [physicalFlow_resampling, mean_sum]
  simp only [mean_const_mul, physicalFlow_resampling]

lemma physicalFlow_nonneg (d : ℕ) (B : Position (d+1) → Bool)
    (w : Position (d+1) → ℝ) (hw : ∀ x, 0 ≤ w x) (c : Position d → Bool) (y) :
    0 ≤ physicalFlow d B w c y := by
  rw [physicalFlow_resampling]
  exact mean_nonneg (fun r => hw _)

lemma rawIterate_nonneg (d : ℕ) (v : RawState (d+1)) (hv : ∀ x, 0 ≤ v.weight x)
    (t : ℕ) (ω : SweepHistory d t) (y) : 0 ≤ (rawIterate d v t ω).weight y := by
  induction t generalizing y with
  | zero => exact hv y
  | succ t ih => exact physicalFlow_nonneg d _ _ (ih (Fin.init ω)) _ y

lemma rawIterate_finSum {α : Type*} [Fintype α] (d : ℕ) (B : Position (d+1) → Bool)
    (a : α → ℝ) (w : α → Position (d+1) → ℝ) (t : ℕ) (ω : SweepHistory d t) (y) :
    (rawIterate d ⟨B,fun x => ∑ i, a i * w i x⟩ t ω).weight y =
      ∑ i, a i * (rawIterate d ⟨B,w i⟩ t ω).weight y := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
      change physicalFlow d (rawIterate d ⟨B,_⟩ t (Fin.init ω)).free
        (rawIterate d ⟨B,_⟩ t (Fin.init ω)).weight (ω (Fin.last t)) y = _
      have hw : (rawIterate d ⟨B,fun x => ∑ i, a i * w i x⟩ t (Fin.init ω)).weight =
          fun z => ∑ i, a i * (rawIterate d ⟨B,w i⟩ t (Fin.init ω)).weight z := by
        funext z; exact ih (Fin.init ω) z
      rw [hw, physicalFlow_finSum]
      apply Finset.sum_congr rfl; intro i _
      congr 1
      change physicalFlow d _ _ _ y = physicalFlow d _ _ _ y
      congr 1
      funext x
      erw [rawIterate_free, rawIterate_free]
      rfl

lemma rawPoint_nonneg (d t : ℕ) (B : Position (d+1) → Bool) (a : Position (d+1))
    (ω : SweepHistory d t) (y) :
    0 ≤ (rawIterate d (rawPoint (d+1) B a) t ω).weight y :=
  rawIterate_nonneg d _ (fun x => by dsimp [rawPoint]; split <;> norm_num) t ω y

lemma rawIterate_point_decomposition {α : Type*} [Fintype α] (d : ℕ)
    (B : Position (d+1) → Bool) (e : α → Position (d+1)) (a : α → ℝ)
    (t : ℕ) (ω : SweepHistory d t) (y) :
    (rawIterate d ⟨B,fun x => ∑ i, if x = e i then a i else 0⟩ t ω).weight y =
      ∑ i, a i * (rawIterate d (rawPoint (d+1) B (e i)) t ω).weight y := by
  have hw : (fun x => ∑ i, if x = e i then a i else 0) =
      (fun x => ∑ i, a i * (rawPoint (d+1) B (e i)).weight x) := by
    funext x
    apply Finset.sum_congr rfl; intro i _
    simp only [rawPoint]
    split <;> simp
  rw [hw]
  exact rawIterate_finSum d B a (fun i => (rawPoint (d+1) B (e i)).weight) t ω y

end Thorp.Conditional

end

end OAI
