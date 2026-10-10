import Mathlib
import OAI.Geometry.IntegralFillings.Model

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
omit [MeasurableSpace X] in
lemma lipschitz_mul_real {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a : ℝ) :
    LipschitzWith (⟨|a|, abs_nonneg a⟩ * K) (fun x => a * f x) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  change dist (a * f x) (a * f y) ≤ (|a| * (K : ℝ)) * dist x y
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  calc |a| * |f x - f y| ≤ |a| * ((K : ℝ) * dist x y) :=
         mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg a)
       _ = _ := by ring

def lipSubmodule : Submodule ℝ (X → ℝ) where
  carrier := {f | ∃ K : ℝ≥0, LipschitzWith K f}
  zero_mem' := ⟨0, LipschitzWith.const 0⟩
  add_mem' := by
    rintro f g ⟨K, hK⟩ ⟨L, hL⟩
    exact ⟨K + L, hK.add hL⟩
  smul_mem' := by
    intro a f hf
    obtain ⟨K, hK⟩ := hf
    exact ⟨_, lipschitz_mul_real hK a⟩

omit [MeasurableSpace X] in
lemma lip_coe_update {k : ℕ} (π : Fin k → lipSubmodule (X := X))
    (i : Fin k) (f : lipSubmodule (X := X)) :
    (fun j => ((Function.update π i f) j : X → ℝ)) =
      Function.update (fun j => (π j : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j = i <;> simp [h]

noncomputable def IsMetricCurrent.multilinear {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (b : X → ℝ) (hb : BoundedLip b) :
    MultilinearMap ℝ (fun _ : Fin k => lipSubmodule (X := X)) ℝ :=
  MultilinearMap.mk' (fun π => T b (fun i => π i)) (by
    intro π i f g
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (g : X → ℝ) 1 1
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ g.property
    simpa only [lip_coe_update, Function.update_self, one_mul,
      Function.update_idem, Submodule.coe_add, Pi.add_def] using h) (by
    intro π i a f
    have h := hT.linearCoord b
      (fun j => ((Function.update π i f) j : X → ℝ)) i (f : X → ℝ) a 0
      ⟨hb, fun j => ((Function.update π i f) j).property⟩ f.property
    simpa only [lip_coe_update, Function.update_self, zero_mul, add_zero,
      Function.update_idem, Submodule.coe_smul, Pi.smul_def, smul_eq_mul] using h)

lemma IsMetricCurrent.scale_coordinates {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (a : Fin k → ℝ) :
    T b (fun i x => a i * π i x) = (∏ i, a i) * T b π := by
  let p : Fin k → lipSubmodule (X := X) := fun i => ⟨π i, hπ i⟩
  exact (hT.multilinear b hb).map_smul_univ a p

lemma IsMetricCurrent.eq_zero_of_const_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (c : ℝ) (hc : ∀ x, π i x = c) :
    T b π = 0 := by
  apply hT.locality b π h
  exact ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

lemma IsMetricCurrent.eq_zero_of_zero_lipschitz_coord {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (i : Fin k) (hi : LipschitzWith 0 (π i)) :
    T b π = 0 := by
  cases isEmpty_or_nonempty X with
  | inl hempty =>
    let := hempty
    exact hT.eq_zero_of_const_coord h i 0 (fun x => isEmptyElim x)
  | inr hnonempty =>
    obtain ⟨x₀⟩ := hnonempty
    apply hT.eq_zero_of_const_coord h i (π i x₀)
    intro x
    apply dist_le_zero.mp
    simpa using hi.dist_le_mul x x₀

end Foundations
end SharpIntegralFillings
end

end OAI
