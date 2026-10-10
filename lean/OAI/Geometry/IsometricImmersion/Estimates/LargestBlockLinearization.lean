import OAI.Geometry.IsometricImmersion.Darboux.SixVariableLinearization
import Mathlib.Order.Preorder.Finite

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def fullBlockPartition (ell : ℕ) (hell : 0 < ell) : OrderedFinpartition ell where
  length := 1
  partSize _ := ell
  partSize_pos _ := hell
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro firstBlock _ secondBlock _ hne
    exact (hne (Subsingleton.elim firstBlock secondBlock)).elim
  cover i := ⟨0, i, rfl⟩

theorem ordered_full_size_length_one {ell : ℕ} (c : OrderedFinpartition ell)
    {i : Fin c.length} (hi : c.partSize i = ell) : c.length = 1 := by
  have hunique : ∀ j : Fin c.length, j = i := by
    intro j
    by_contra hji
    have hb := ordered_two_partSizes_le c hji
    have hj := c.partSize_pos j
    rw [hi] at hb
    omega
  have hsub : Subsingleton (Fin c.length) :=
    ⟨fun a b => (hunique a).trans (hunique b).symm⟩
  have hcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
  simp only [Fintype.card_fin] at hcard
  have hi0 := i.isLt
  omega

theorem ordered_length_one_eq_full {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c.length = 1) : c = fullBlockPartition ell hell := by
  rcases c with ⟨length, size, hpos, emb, hmono, horder, hdis, hcover⟩
  dsimp only at hc
  subst length
  have hsize0 : size 0 = ell := by
    have hh := ordered_partSize_sum
      (OrderedFinpartition.mk 1 size hpos emb hmono horder hdis hcover)
    simpa only [Fin.sum_univ_one] using hh
  have hsize : size = fun _ : Fin 1 => ell := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hsize0
  subst size
  have hemb : emb = fun _ : Fin 1 => (id : Fin ell → Fin ell) := by
    funext i
    exact (hmono i).eq_id
  subst emb
  rfl

theorem ordered_nonfull_partSize_le {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c ≠ fullBlockPartition ell hell) (i : Fin c.length) :
    c.partSize i ≤ ell - 1 := by
  have hle := c.partSize_le i
  have hne : c.partSize i ≠ ell := by
    intro he
    exact hc (ordered_length_one_eq_full hell c (ordered_full_size_length_one c he))
  omega

def darbouxFaaTerm (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    {ell : ℕ} (c : OrderedFinpartition ell) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
    (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y)

def directLinearization (g : MetricField) (z u : Coord → ℝ) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * coordPartial 0 u p + heightPFirst g z 1 p * coordPartial 1 u p +
    2 * hessianQuotient g z p * coordPartial 0 (coordPartial 1 u) p -
    ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
      coordPartial 1 (coordPartial 1 u) p

theorem fullBlockPartition_term (g : MetricField) (z : Coord → ℝ) (x y : ℝ)
    (ell : ℕ) (hell : 0 < ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell hell) =
      fderiv ℝ (sixVariableP g) (solutionJetCurve z x y)
        (iteratedDeriv ell (solutionJetCurve z x) y) := by
  exact iteratedFDeriv_one_apply (𝕜 := ℝ) (f := sixVariableP g)
    (x := solutionJetCurve z x y) (fun _ : Fin 1 => iteratedDeriv ell (solutionJetCurve z x) y)

theorem fullBlockPartition_actual_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (ell : ℕ) (hell : 2 ≤ ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell (by omega)) =
      directLinearization g z (verticalJet z ell) ![x, y] := by
  rw [fullBlockPartition_term, solutionJetCurve_iteratedDeriv hU hz hp ell hell]
  change fderiv ℝ (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

theorem actualDarboux_extract_fullBlock
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (ell : ℕ) (hell : 2 ≤ ell) :
    coordPartial 0 (coordPartial 0 (verticalJet z ell)) ![x, y] =
      directLinearization g z (verticalJet z ell) ![x, y] +
        ∑ c ∈ (Finset.univ.erase (fullBlockPartition ell (by omega))), darbouxFaaTerm g z x y c := by
  have heq := actualDarboux_faaExpansion_coord hg hU hz hD hyy hp ell
  change coordPartial 0 (coordPartial 0 (verticalJet z ell)) ![x, y] =
    ∑ c : OrderedFinpartition ell, darbouxFaaTerm g z x y c at heq
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (OrderedFinpartition ell))
    (darbouxFaaTerm g z x y) (Finset.mem_univ (fullBlockPartition ell (by omega)))).symm
  rw [fullBlockPartition_actual_linearization hg hU hz hp (hyy _ hp) ell hell] at hsplit
  exact heq.trans hsplit

end SmoothLocal.HighEquation

end

end OAI
