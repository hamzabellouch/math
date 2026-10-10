import Mathlib.Tactic.FinCases
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M : MergedPairs F}

omit [Field F] [Fintype F] [DecidableEq F] in

theorem prescribed_generator_injective (hE : Eligible P a) (i : Fin b) :
    Function.Injective (prescribedTuple P a bits i).generator :=
  hE.2.1.comp (P.withinTuple i)

omit [Fintype F] [DecidableEq F] in

theorem prescribedPoint_on_left (hE : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i j)) (bits i j)) := by
  apply onLine_lineIntersection_left
  change a.2 (P.classOf i j) ≠ a.2 (P.classOf i (j + 1))
  intro h
  have h' := P.withinTuple i (hE.2.1 h)
  fin_cases j <;> contradiction

omit [Fintype F] [DecidableEq F] in

theorem prescribedPoint_on_right (hE : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i (j + 1))) (!(bits i (j + 1)))) := by
  apply onLine_lineIntersection_right
  change a.2 (P.classOf i j) ≠ a.2 (P.classOf i (j + 1))
  intro h
  have h' := P.withinTuple i (hE.2.1 h)
  fin_cases j <;> contradiction

omit [Fintype F] [DecidableEq F] in

theorem exists_prescribedPoint_on_constituent (hE : Eligible P a)
    (c : Fin (4 * b - κ)) (s : Bool) :
    ∃ ij : Fin b × Fin 4,
      OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hc⟩ := P.everyClass c
  change P.classOf i j = c at hc
  by_cases hs : s = bits i j
  · refine ⟨(i, j), ?_⟩
    simpa only [hc, hs] using prescribedPoint_on_left (M := M) hE i j
  · have hs' : s = !(bits i j) := by
      cases s <;> cases h : bits i j <;> simp_all
    refine ⟨(i, j + 3), ?_⟩
    have hj : (j + 3) + 1 = j := by fin_cases j <;> decide
    simpa only [hj, hc, hs'] using prescribedPoint_on_right (M := M) hE i (j + 3)

theorem not_onLine_used_constituent (hE : Eligible P a)
    (hA : Admissible P a bits p M) (c : Fin (4 * b - κ)) (s : Bool) :
    ¬ OnLine p (constituent M (a.2 c) s) := by
  obtain ⟨⟨i, j⟩, hpoint⟩ := exists_prescribedPoint_on_constituent hE c s
  intro hp
  have hline : constituent M (a.2 c) s ≠ lineThrough (a.1 i) p := by
    intro heq
    exact hA.2.2.2.1 i (heq ▸
      Finset.mem_image.mpr ⟨(a.2 c, s), Finset.mem_univ _, rfl⟩)
  exact hA.2.2.1 (i, j)
    (common_point_eq_of_lines_ne _ _ hline _ p hpoint (hA.1 (i, j)) hp
      (onLine_lineThrough _ _))

theorem direction_unused_of_onLine (hE : Eligible P a)
    (hA : Admissible P a bits p M) {d : Direction F} {s : Bool}
    (hp : OnLine p (constituent M d s)) :
    d ∉ Finset.univ.image a.2 := by
  intro hd
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
  exact not_onLine_used_constituent hE hA c s hp

theorem mem_prescribedPartners_iff_unused (hE : Eligible P a)
    (hA : Admissible P a bits p M) (x : Point F) :
    x ∈ prescribedPartners P a bits p M ↔
      x ∈ prescribedDesignated P a bits M ∧
      ∃ ds : Direction F × Bool,
        ds.1 ∉ Finset.univ.image a.2 ∧
        OnLine p (constituent M ds.1 ds.2) ∧
        OnLine x (constituent M ds.1 (!ds.2)) := by
  constructor
  · intro hx
    obtain ⟨hF, ds, hp, hx⟩ := Finset.mem_filter.mp hx
    exact ⟨hF, ds, direction_unused_of_onLine hE hA hp, hp, hx⟩
  · rintro ⟨hF, ds, _, hp, hx⟩
    exact Finset.mem_filter.mpr ⟨hF, ds, hp, hx⟩

end
end Balanced.Local.PrescribedGeometry

end OAI
