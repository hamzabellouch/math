import OAI.Geometry.IsometricImmersion.Taylor.ScalarChainExpansion
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Count

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem orderedPartial_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2)) :
    ContDiffOn ℝ ∞ (iteratedCoordPartial ds f) U := by
  induction ds with
  | nil => exact hf
  | cons i ds ih => exact normed_coordPartial_contDiffOn ih hU i

theorem orderedPartial_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ds es : List (Fin 2)) (f : Coord → E) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

theorem orderedPartial_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {ds es : List (Fin 2)} (hperm : ds.Perm es) :
    ∀ p ∈ U, iteratedCoordPartial ds f p = iteratedCoordPartial es f p := by
  induction hperm with
  | nil => intro p _; rfl
  | cons i _perm ih =>
      rename_i l1 l2
      intro p hp
      have he : iteratedCoordPartial l1 f =ᶠ[𝓝 p] iteratedCoordPartial l2 f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      exact coordPartial_eq_of_eventuallyEq he i
  | swap i j ds =>
      intro p hp
      exact normed_coordPartial_comm (orderedPartial_contDiffOn hf hU ds) hU hp j i
  | trans _ _ ih₁ ih₂ =>
      intro p hp
      exact (ih₁ p hp).trans (ih₂ p hp)

theorem coordinateDirections_apply (ds : List (Fin 2)) (i : Fin ds.length) :
    coordinateDirections ds i = Pi.single (ds.get i) (1 : ℝ) := by
  induction ds with
  | nil => exact Fin.elim0 i
  | cons a ds ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih j

theorem fullJet_coordinate_inputs_eq_ordered
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (d : Fin n → Fin 2) {p : Coord} (hp : p ∈ U) :
    iteratedFDeriv ℝ n f p (fun i => Pi.single (d i) (1 : ℝ)) =
      iteratedCoordPartial (List.ofFn d) f p := by
  induction n generalizing p with
  | zero => simp [iteratedCoordPartial]
  | succ n ih =>
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
      rw [hd.iteratedFDeriv_succ_apply_left']
      have he : (fun q => iteratedFDeriv ℝ n f q
          (fun i => Pi.single (d i.succ) (1 : ℝ))) =ᶠ[𝓝 p]
          iteratedCoordPartial (List.ofFn (fun i => d i.succ)) f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih (fun i => d i.succ) hq
      change fderiv ℝ (fun q => iteratedFDeriv ℝ n f q
        (fun i => Pi.single (d i.succ) (1 : ℝ))) p (Pi.single (d 0) 1) = _
      rw [he.fderiv_eq, List.ofFn_succ]
      rfl

theorem state_fullJet_eval
    {f : Coord → DarbouxState} {p : Coord} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) (v : Fin n → Coord) (i : Fin 6) :
    (iteratedFDeriv ℝ n f p v) i = iteratedFDeriv ℝ n (fun q => f q i) p v := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) p v = L (iteratedFDeriv ℝ n f p v)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem fullJet_linear_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Coord →L[ℝ] E) {n : ℕ} (hn : 2 ≤ n) (p : Coord) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n L p v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      have hn0 : n ≠ 0 := by omega
      rw [iteratedFDeriv_succ_apply_right]
      have he : (fun q => fderiv ℝ L q) = fun _ : Coord => L := by
        funext q
        exact L.fderiv
      rw [he, iteratedFDeriv_const_of_ne hn0]
      simp

theorem solutionJet_fullJet_ge_two
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 2 ≤ n) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n (solutionJet z) p v =
      ![0, 0, iteratedFDeriv ℝ n (coordPartial 0 z) p v,
        iteratedFDeriv ℝ n (coordPartial 1 z) p v,
        iteratedFDeriv ℝ n (coordPartial 0 (coordPartial 1 z)) p v,
        iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 z)) p v] := by
  have hJ := (solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)
  ext i
  rw [state_fullJet_eval hJ n v i]
  fin_cases i
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) hn p v
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) hn p v
  · rfl
  · rfl
  · rfl
  · rfl

theorem solutionJet_fullJet_one
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (v : Fin 1 → Coord) :
    iteratedFDeriv ℝ 1 (solutionJet z) p v =
      ![(v 0) 0, (v 0) 1, iteratedFDeriv ℝ 1 (coordPartial 0 z) p v,
        iteratedFDeriv ℝ 1 (coordPartial 1 z) p v,
        iteratedFDeriv ℝ 1 (coordPartial 0 (coordPartial 1 z)) p v,
        iteratedFDeriv ℝ 1 (coordPartial 1 (coordPartial 1 z)) p v] := by
  have hJ := (solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)
  ext i
  rw [state_fullJet_eval hJ 1 v i]
  fin_cases i
  · change iteratedFDeriv ℝ 1 (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) p v = _
    rw [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
    rfl
  · change iteratedFDeriv ℝ 1 (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) p v = _
    rw [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem word_two_x_permutation (ds : List (Fin 2)) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), ds.Perm (es ++ [0, 0]) := by
  have h0 : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
  have h1 : (0 : Fin 2) ∈ ds.erase 0 := List.count_pos_iff.mp (by
    rw [List.count_erase_self]
    omega)
  refine ⟨(ds.erase 0).erase 0, ?_⟩
  have h := (List.perm_cons_erase h0).trans ((List.perm_cons_erase h1).cons 0)
  exact h.trans (show ([0, 0] ++ (ds.erase 0).erase 0).Perm
    ((ds.erase 0).erase 0 ++ [0, 0]) from List.perm_append_comm)

theorem mixed_principal_word_orders (es : List (Fin 2)) :
    (es ++ [0, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [1, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [0, 1]).count 0 < (es ++ [0, 0]).count 0 ∧
    (es ++ [1, 1]).count 0 < (es ++ [0, 0]).count 0 := by
  simp

end SmoothLocal.HighEquation

end

end OAI
