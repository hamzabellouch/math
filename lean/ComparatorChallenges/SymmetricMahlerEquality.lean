import Mathlib

namespace OAI

namespace SymmetricMahler

section

open Real Complex Set Finset
variable {I : Type*} [Fintype I]

def coordinatePolar (K : Set (I → ℝ)) : Set (I → ℝ) :=
  {p | ∀ v ∈ K, (∑ i, p i*v i) ≤ 1}

end

noncomputable section

open Set MeasureTheory Metric

def hannerProduct {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = Fin.append x y}

def hannerJoin {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  convexHull ℝ
    (((fun x : Fin k → ℝ => Fin.append x 0) '' A) ∪
      ((fun y : Fin l → ℝ => Fin.append 0 y) '' B))

inductive IsHanner : {n : ℕ} → Set (Fin n → ℝ) → Prop
  | interval (a : ℝ) (ha : 0 < a) :
      IsHanner (Icc (fun _ : Fin 1 => -a) (fun _ : Fin 1 => a))
  | product {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerProduct A B)
  | join {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerJoin A B)

def IsLinearHanner {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ H : Set (Fin n → ℝ), IsHanner H ∧
    ∃ T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ), K = T '' H

theorem symmetric_mahler_equality {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ((volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) ↔ IsLinearHanner K := by
  sorry

end

end SymmetricMahler

end OAI
