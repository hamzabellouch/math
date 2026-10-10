import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder Classical

namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

def finiteDPPWeight (K : Matrix F F ℂ) (x : F → Bool) : ℂ := by
  classical
  exact Matrix.det (fun i j => if x i = true then K i j else (1 - K) i j)

theorem finiteDPPWeight_sum_inclusion (K : Matrix F F ℂ) (A : Finset F) :
    (∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0) =
      Matrix.det (fun i j : A => K i.1 j.1) := by
  classical
  let choices : F → Finset Bool := fun i => if i ∈ A then {true} else Finset.univ
  let rows : F → Bool → F → ℂ :=
    fun i b j => if b = true then K i j else (1 - K) i j
  have hchoices : Fintype.piFinset choices =
      Finset.univ.filter (fun x : F → Bool => ∀ i ∈ A, x i = true) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx i hi
      simpa [choices, hi] using hx i
    · intro hx i
      by_cases hi : i ∈ A
      · simp [choices, hi, hx i hi]
      · simp [choices, hi]
  have hrows : (fun i => ∑ b ∈ choices i, rows i b) =
      A.piecewise K (1 : Matrix F F ℂ) := by
    funext i j
    by_cases hi : i ∈ A
    · simp [choices, rows, hi, Finset.piecewise]
    · simp [choices, rows, hi, Finset.piecewise, Finset.sum_apply,
        Matrix.sub_apply]
  have hsum := Matrix.detRowAlternating.toMultilinearMap.map_sum_finset rows choices
  rw [hchoices, Finset.sum_filter] at hsum
  rw [hrows] at hsum
  change Matrix.det (A.piecewise K (1 : Matrix F F ℂ)) =
    (∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0) at hsum
  exact hsum.symm.trans (Matrix.det_piecewise_one_eq_submatrix_det K A)

theorem finiteDPPWeight_sum (K : Matrix F F ℂ) :
    (∑ x : F → Bool, finiteDPPWeight K x) = 1 := by
  classical
  calc
    _ = Matrix.det (fun i j : (∅ : Finset F) => K i.1 j.1) := by
      simpa only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        ite_true] using finiteDPPWeight_sum_inclusion K ∅
    _ = 1 := Matrix.det_isEmpty

theorem finiteDPP_exists_of_weights_nonneg (K : Matrix F F ℂ)
    (hK : ∀ x : F → Bool, 0 ≤ finiteDPPWeight K x) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  classical
  have hre (x : F → Bool) : 0 ≤ (finiteDPPWeight K x).re :=
    (Complex.nonneg_iff.mp (hK x)).1
  have hreal (x : F → Bool) : ((finiteDPPWeight K x).re : ℂ) = finiteDPPWeight K x := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp (hK x)).2
  have hsum : (∑ x : F → Bool, (finiteDPPWeight K x).re) = 1 := by
    simpa using congrArg Complex.re (finiteDPPWeight_sum K)
  have hmass : (∑ x : F → Bool, ENNReal.ofReal (finiteDPPWeight K x).re) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hre x), hsum]
    simp
  let p : PMF (F → Bool) := PMF.ofFintype
    (fun x => ENNReal.ofReal (finiteDPPWeight K x).re) hmass
  refine ⟨⟨p.toMeasure, inferInstance⟩, ?_⟩
  intro A
  change ((p.toMeasure {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
    Matrix.det (fun i j : A => K i.1 j.1)
  rw [PMF.toMeasure_apply_fintype]
  have hfinite (x : F → Bool) :
      ({x | ∀ i ∈ A, x i = true}.indicator (⇑p) x) ≠ ∞ := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [p]
  rw [ENNReal.toReal_sum (fun x _ => hfinite x)]
  push_cast
  calc
    (∑ x : F → Bool,
        (({x | ∀ i ∈ A, x i = true}.indicator (⇑p) x).toReal : ℂ)) =
        ∑ x : F → Bool, if (∀ i ∈ A, x i = true) then finiteDPPWeight K x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, p, PMF.ofFintype_apply]
      split_ifs <;> simp [ENNReal.toReal_ofReal (hre x), hreal x]
    _ = Matrix.det (fun i j : A => K i.1 j.1) := finiteDPPWeight_sum_inclusion K A

end Problem336AdditiveD139

end

end OAI
