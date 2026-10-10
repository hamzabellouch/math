import OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleDiagonals
import OAI.NumberTheory.JointDickman.Arithmetic.MovingPrimeTuple

namespace OAI

/-! # Ordered prime tuples are continuity sets -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem strictMono_isOpen (n : ℕ) : IsOpen {t : Fin n → ℝ | StrictMono t} := by
  classical
  have he : {t : Fin n → ℝ | StrictMono t} =
      ⋂ i : Fin n, ⋂ j : Fin n, if i < j then {t | t i < t j} else Set.univ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro ht i j
      split_ifs with hij
      · exact ht hij
      · exact Set.mem_univ _
    · intro ht i j hij
      simpa only [hij, ite_true, Set.mem_ofPred_eq] using ht i j
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_univ

theorem strictMono_frontier_subset (n : ℕ) :
    frontier {t : Fin n → ℝ | StrictMono t} ⊆ tupleDiagonal n := by
  have hcl : closure {t : Fin n → ℝ | StrictMono t} ⊆ {t | Monotone t} :=
    closure_minimal (fun _ ht => ht.monotone) isClosed_monotone
  intro t ht hinj
  have hm : Monotone t := hcl (frontier_subset_closure ht)
  have hs := hm.strictMono_of_injective hinj
  have hnot : t ∉ interior {t : Fin n → ℝ | StrictMono t} := ht.2
  exact hnot (by rw [(strictMono_isOpen n).interior_eq]; exact hs)

theorem orderedPrimeRegion_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) : (Measure.pi (fun _ : Fin (n+1) => μ))
      (frontier {t | StrictMono t}) = 0 :=
  measure_mono_null (strictMono_frontier_subset (n+1)) (pi_tupleDiagonal_null μ n)

noncomputable def orderedPrimeBox (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  {t | StrictMono t} ∩ primeBoxCutoff h a b u

theorem orderedPrimeBox_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (orderedPrimeBox (n+1) a b u)) = 0 :=
  null_frontier_inter (orderedPrimeRegion_null_frontier μ n)
    (primeBoxCutoff_null_frontier μ n a b u)

theorem orderedPrimeBox_measure_continuous {c : ℝ} (n : ℕ)
    (a b : Fin (n+1) → ℝ) :
    Continuous (fun u : ℝ => ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
      (orderedPrimeBox (n+1) a b u) : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have he (u : ℝ) : orderedPrimeBox (n+1) a b u =
      ({t | StrictMono t} ∩ Set.pi Set.univ (fun i => Set.Ioc (a i) (b i))) ∩
        {t | ∑ i, t i ≤ u} := by
    exact (Set.inter_assoc _ _ _).symm
  simp only [he]
  apply sublevel_measure_continuousAt _
    ((strictMono_isOpen (n+1)).measurableSet.inter (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)))
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  exact pi_sum_level_null _ n u

end JointDickman

end OAI
