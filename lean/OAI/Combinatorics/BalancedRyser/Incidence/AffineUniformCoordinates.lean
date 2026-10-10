import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.BalancedRyser.Incidence.AffinePairEvaluation

namespace OAI

namespace Balanced.PairEvaluation

noncomputable section
open scoped ENNReal

theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    have hba : b ≠ e a := by
      intro h
      apply ha
      apply e.injective
      simpa using h.symm
    simp [hba]

variable {F : Type*} [Field F] [Fintype F]

theorem uniform_intersection_map (d e : Direction F) (hde : d ≠ e) :
    (PMF.uniformOfFintype (F × F)).map
        (fun ab => lineIntersection (d, ab.1) (e, ab.2)) =
      PMF.uniformOfFintype (Point F) := by
  exact uniform_map_equiv (pairEvalEquiv d e hde).symm

theorem uniform_evalPair_map (d e : Direction F) (hde : d ≠ e) :
    (PMF.uniformOfFintype (Point F)).map
        (fun p => (lineEval d p, lineEval e p)) =
      PMF.uniformOfFintype (F × F) := by
  exact uniform_map_equiv (pairEvalEquiv d e hde)

theorem uniform_intersection_apply (d e : Direction F) (hde : d ≠ e) (p : Point F) :
    ((PMF.uniformOfFintype (F × F)).map
      (fun ab => lineIntersection (d, ab.1) (e, ab.2))) p =
        ((Fintype.card F : ℝ≥0∞) ^ 2)⁻¹ := by
  rw [uniform_intersection_map d e hde]
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, pow_two]

theorem uniform_lineCoordinate_symm [DecidableEq F]
    (d e : Direction F) (hde : d ≠ e) (a : F) :
    letI : Nonempty {p : Point F // OnLine p (d, a)} :=
      ⟨(lineCoordinateEquiv d e hde a).symm 0⟩
    (PMF.uniformOfFintype F).map (lineCoordinateEquiv d e hde a).symm =
      PMF.uniformOfFintype {p : Point F // OnLine p (d, a)} := by
  let : Nonempty {p : Point F // OnLine p (d, a)} :=
    ⟨(lineCoordinateEquiv d e hde a).symm 0⟩
  exact uniform_map_equiv (lineCoordinateEquiv d e hde a).symm

theorem linePoints_card_via_coordinates [DecidableEq F]
    (d e : Direction F) (hde : d ≠ e) (a : F) :
    (linePoints (d, a)).card = Fintype.card F := by
  calc
    _ = Fintype.card {p : Point F // OnLine p (d, a)} := by
      simp [Fintype.card_subtype, linePoints]
    _ = _ := Fintype.card_congr (lineCoordinateEquiv d e hde a)

theorem linePoints_nonempty_via_coordinates [DecidableEq F]
    (d e : Direction F) (hde : d ≠ e) (a : F) :
    (linePoints (d, a)).Nonempty := by
  refine ⟨lineIntersection (d, a) (e, 0), ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, congrArg Prod.fst (eval_intersection d e hde a 0)⟩

theorem uniform_fixed_line_map [DecidableEq F]
    (d e : Direction F) (hde : d ≠ e) (a : F) :
    (PMF.uniformOfFintype F).map (fun b => lineIntersection (d, a) (e, b)) =
      PMF.uniformOfFinset (linePoints (d, a))
        (linePoints_nonempty_via_coordinates d e hde a) := by
  classical
  apply PMF.ext
  intro p
  by_cases hp : OnLine p (d, a)
  · have hp' : lineEval d p = a := hp
    have hpoint : lineIntersection (d, a) (e, lineEval e p) = p := by
      simpa [hp'] using intersection_eval d e hde p
    rw [PMF.map_apply, tsum_eq_single (lineEval e p)]
    · have hmem : p ∈ linePoints (d, a) := by simp [linePoints, hp]
      rw [PMF.uniformOfFinset_apply_of_mem _ hmem,
        linePoints_card_via_coordinates d e hde a]
      simp [hpoint]
    · intro b hb
      have hne : p ≠ lineIntersection (d, a) (e, b) := by
        intro heq
        apply hb
        have hh := congrArg Prod.snd (eval_intersection d e hde a b)
        simpa [← heq] using hh.symm
      simp [hne]
  · have hne : ∀ b, p ≠ lineIntersection (d, a) (e, b) := by
      intro b heq
      apply hp
      have hh := congrArg Prod.fst (eval_intersection d e hde a b)
      simpa [OnLine, ← heq] using hh
    simp [PMF.map_apply, hne, PMF.uniformOfFinset_apply, linePoints, hp]

theorem uniform_pair_eq_independent_bind :
    PMF.uniformOfFintype (F × F) =
      (PMF.uniformOfFintype F).bind
        (fun a => (PMF.uniformOfFintype F).map (fun b => (a, b))) := by
  classical
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · simp [PMF.map_apply, Fintype.card_prod, ENNReal.mul_inv]
  · intro c hc
    simp [PMF.map_apply, Ne.symm hc]

end
end Balanced.PairEvaluation

end OAI
