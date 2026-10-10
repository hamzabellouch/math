import OAI.Analysis.Cotype.MixedDerivative
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

abbrev ScalarTriple (m : ℕ) := (SignMatrix m → ℝ) × (Cube m → ℝ) × (Cube m → ℝ)

def admissibleSet (m : ℕ) (a b : ℝ) : Set (ScalarTriple m) :=
  {x | ScalarAdmissible m a b x.1 x.2.1 x.2.2}

theorem admissibleSet_closed (m : ℕ) (a b : ℝ) : IsClosed (admissibleSet m a b) := by
  simp only [admissibleSet, ScalarAdmissible, IsOdd, fourier, average, smul_eq_mul,
    Set.ofPred_and, Set.ofPred_forall]
  repeat' first
    | apply IsClosed.inter
    | apply isClosed_iInter; intro i
  all_goals first
    | exact isClosed_le (by fun_prop) (by fun_prop)
    | exact isClosed_eq (by fun_prop) (by fun_prop)

theorem function_box_compact (α : Type*) :
    IsCompact {f : α → ℝ | ∀ x, |f x| ≤ 4} := by
  have h : IsCompact {f : α → ℝ | ∀ x, f x ∈ Set.Icc (-4 : ℝ) 4} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  simpa only [Set.mem_Icc, abs_le] using h

theorem admissibleSet_compact (m : ℕ) (a b : ℝ) : IsCompact (admissibleSet m a b) := by
  have hbox := (function_box_compact (SignMatrix m)).prod
    ((function_box_compact (Cube m)).prod (function_box_compact (Cube m)))
  apply hbox.of_isClosed_subset (admissibleSet_closed m a b)
  intro x hx
  obtain ⟨_, _, _, hΨ, hf, hg, _, _, _, _⟩ := hx
  exact ⟨hΨ, hf, hg⟩

variable {m : ℕ}

def rankTwoMax (Ψ : SignMatrix m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun P =>
    if 2 ≤ (binaryMatrix P).rank then |fourier Ψ P| else 0)

theorem rankTwoMax_continuous (m : ℕ) : Continuous (@rankTwoMax m) := by
  apply Continuous.finset_sup'_apply
  intro P _
  by_cases hP : 2 ≤ (binaryMatrix P).rank
  · simp only [ite_eq_left hP]
    unfold fourier average
    fun_prop
  · simp only [ite_eq_right hP]
    fun_prop

theorem rankTwoMax_pos {Ψ : SignMatrix m → ℝ}
    (h : ∃ P, 2 ≤ (binaryMatrix P).rank ∧ fourier Ψ P ≠ 0) : 0 < rankTwoMax Ψ := by
  obtain ⟨P, hP, hc⟩ := h
  have hle := Finset.le_sup' (s := (Finset.univ : Finset (SignMatrix m)))
    (f := fun Q => if 2 ≤ (binaryMatrix Q).rank then |fourier Ψ Q| else 0) (Finset.mem_univ P)
  rw [ite_eq_left hP] at hle
  exact (abs_pos.mpr hc).trans_le hle

theorem rankTwoMax_attained {Ψ : SignMatrix m → ℝ} (h : 0 < rankTwoMax Ψ) :
    ∃ P, 2 ≤ (binaryMatrix P).rank ∧ rankTwoMax Ψ = |fourier Ψ P| := by
  obtain ⟨P, _, hP⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (SignMatrix m)))
    Finset.univ_nonempty (fun P => if 2 ≤ (binaryMatrix P).rank then |fourier Ψ P| else 0)
  by_cases hr : 2 ≤ (binaryMatrix P).rank
  · exact ⟨P, hr, by simpa [rankTwoMax, hr] using hP⟩
  · have hz : rankTwoMax Ψ = 0 := by simpa [rankTwoMax, hr] using hP
    linarith

theorem coefficientTarget_proved : CoefficientTarget := by
  intro m a b hd hm ha hb hlarge
  let K := admissibleSet m a b
  have hpos (x : ScalarTriple m) (hx : x ∈ K) : 0 < rankTwoMax x.1 :=
    rankTwoMax_pos (admissible_exists_rank_two hx ha hb hd hm hlarge)
  by_cases hK : K.Nonempty
  · have hcont : Continuous (fun x : ScalarTriple m => rankTwoMax x.1) :=
      (rankTwoMax_continuous m).comp continuous_fst
    obtain ⟨x, hx, hmin⟩ := (admissibleSet_compact m a b).exists_isMinOn hK hcont.continuousOn
    refine ⟨rankTwoMax x.1, hpos x hx, ?_⟩
    intro Ψ f g h
    have hmem : (Ψ, f, g) ∈ K := h
    obtain ⟨P, hr, he⟩ := rankTwoMax_attained (hpos _ hmem)
    refine ⟨P, hr, ?_⟩
    rw [← he]
    exact hmin hmem
  · refine ⟨1, by norm_num, ?_⟩
    intro Ψ f g h
    exact (hK ⟨(Ψ,f,g), h⟩).elim

end Cotype

end

end OAI
