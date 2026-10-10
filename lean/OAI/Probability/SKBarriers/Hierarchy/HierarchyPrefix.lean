import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianResponse
import OAI.Probability.SKBarriers.Hierarchy.HierarchyLevels

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

@[simp] theorem TailZero.zero (n : ℕ) (j : Fin (n+1)) : TailZero n j 0 := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [TailZero,Fin.lastCases_last]
    · simp only [TailZero,Fin.lastCases_castSucc]
      exact ⟨rfl,ih j⟩

@[simp] theorem PrefixZero.zero (n : ℕ) (j : Fin (n+1)) : PrefixZero n j 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last]
    · simpa only [PrefixZero,Fin.lastCases_castSucc,Prod.fst_zero] using ih j

theorem TailZero.add {n : ℕ} {j : Fin (n+1)} {u v : ParameterSpace n}
    (hu : TailZero n j u) (hv : TailZero n j v) : TailZero n j (u+v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    revert hu hv
    refine Fin.lastCases (fun _ _ => by simp only [TailZero,Fin.lastCases_last]) (fun j hu hv => ?_) j
    simp only [TailZero,Fin.lastCases_castSucc] at hu hv ⊢
    exact ⟨by simp only [Prod.snd_add,hu.1,hv.1,add_zero],ih hu.2 hv.2⟩

theorem TailZero.smul {n : ℕ} {j : Fin (n+1)} {u : ParameterSpace n}
    (hu : TailZero n j u) (c : ℝ) : TailZero n j (c • u) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    revert hu
    refine Fin.lastCases (fun _ => by simp only [TailZero,Fin.lastCases_last]) (fun j hu => ?_) j
    simp only [TailZero,Fin.lastCases_castSucc] at hu ⊢
    exact ⟨by simp only [Prod.smul_snd,hu.1,smul_zero],ih hu.2⟩

theorem PrefixZero.add {n : ℕ} {j : Fin (n+1)} {u v : ParameterSpace n}
    (hu : PrefixZero n j u) (hv : PrefixZero n j v) : PrefixZero n j (u+v) := by
  induction n with
  | zero => change u = 0 at hu; change v = 0 at hv; simp [hu,hv,PrefixZero]
  | succ n ih =>
    revert hu hv
    refine Fin.lastCases (fun hu hv => ?_) (fun j hu hv => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hu hv ⊢
      rw [hu,hv,add_zero]
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hu hv ⊢
      exact ih hu hv

theorem PrefixZero.smul {n : ℕ} {j : Fin (n+1)} {u : ParameterSpace n}
    (hu : PrefixZero n j u) (c : ℝ) : PrefixZero n j (c • u) := by
  induction n with
  | zero => change u = 0 at hu; simp [hu,PrefixZero]
  | succ n ih =>
    revert hu
    refine Fin.lastCases (fun hu => ?_) (fun j hu => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hu ⊢
      rw [hu,smul_zero]
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hu ⊢
      exact ih hu

theorem tailZero_coordinateAxis (n : ℕ) (i : Fin n) (j : Fin (n+1)) (h : i.val < j.val) :
    TailZero n j (coordinateAxis n i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.lastCases (fun _ => by simp only [TailZero,Fin.lastCases_last]) (fun j h => ?_) j
    revert h
    refine Fin.lastCases (fun h => ?_) (fun i h => ?_) i
    · exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ j.isLt) h).elim
    · simp only [coordinateAxis_castSucc,TailZero,Fin.lastCases_castSucc]
      exact ⟨trivial,ih i j h⟩

theorem prefixZero_coordinateAxis (n : ℕ) (i : Fin n) (j : Fin (n+1)) (h : j.val ≤ i.val) :
    PrefixZero n j (coordinateAxis n i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.lastCases (fun h => ?_) (fun j h => ?_) j
    · exact (Nat.not_le_of_gt i.isLt h).elim
    · revert h
      refine Fin.lastCases (fun _ => ?_) (fun i h => ?_) i
      · simpa only [coordinateAxis_last,PrefixZero,Fin.lastCases_castSucc] using PrefixZero.zero n j
      · simpa only [coordinateAxis_castSucc,PrefixZero,Fin.lastCases_castSucc] using ih i j h

@[simp] theorem coordinateLinear_coordinateAxis (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    coordinateLinear n a (coordinateAxis n i) = a i := by
  simp [coordinateLinear_apply,coordinateProjection_coordinateAxis]

theorem hierarchyLevel_pair_invariance (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (i₁ i₂ : Fin n) (c₁ c₂ : ℝ) (hi : i₁ ≤ i₂)
    (ht : TranslationInvariant f (c₁ • coordinateAxis n i₁+c₂ • coordinateAxis n i₂))
    (j : Fin (n+1)) (hj : j.val ≤ i₁.val ∨ i₂.val < j.val) :
    TranslationInvariant (hierarchyLevel n m f j) (c₁ • coordinateAxis n i₁+c₂ • coordinateAxis n i₂) := by
  rcases hj with hj | hj
  · apply hierarchyLevel_invariant_of_prefix
    exact ((prefixZero_coordinateAxis n i₁ j hj).smul c₁).add
      ((prefixZero_coordinateAxis n i₂ j (hj.trans hi)).smul c₂)
  · apply hierarchyLevel_invariant_of_tail n m f _ ht
    exact ((tailZero_coordinateAxis n i₁ j ((show i₁.val ≤ i₂.val from hi).trans_lt hj)).smul c₁).add
      ((tailZero_coordinateAxis n i₂ j hj).smul c₂)

end SK.Analytic

end
end
end
end
end
end
end

end OAI
