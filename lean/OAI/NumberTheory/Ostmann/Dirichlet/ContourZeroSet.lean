import OAI.NumberTheory.Ostmann.Dirichlet.ContourZeroCount
import OAI.NumberTheory.Ostmann.Dirichlet.WideLocalEstimates

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open scoped BigOperators
open scoped Classical

def contourZeros {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (T : ℝ) : Finset ℂ :=
  (zerosUpTo_finite chi hchi (T+4)).toFinset.filter (fun rho => 3/20 ≤ rho.re)

lemma mem_contourZeros {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (T : ℝ) (rho : ℂ) :
    rho ∈ contourZeros chi hchi T ↔
      chi.LFunction rho = 0 ∧ 3/20 ≤ rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ T+4 := by
  simp only [contourZeros, Finset.mem_filter, Set.Finite.mem_toFinset, zerosUpTo,
    Set.mem_ofPred_eq, IsNontrivialZero]
  constructor
  · rintro ⟨⟨⟨hz,hpos,hlt⟩,him⟩,hre⟩
    exact ⟨hz,hre,hlt,him⟩
  · rintro ⟨hz,hre,hlt,him⟩
    exact ⟨⟨⟨hz,by linarith,hlt⟩,him⟩,hre⟩

lemma contourZeros_card_le {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    ((contourZeros chi hchi T).card : ℝ) ≤
      8000000*absoluteZetaTwo*q*(T+4)^4 := by
  have hcount := contour_zero_multiplicity_le chi hchi hT (contourZeros chi hchi T)
    (fun rho hr => by
      have h := (mem_contourZeros chi hchi T rho).mp hr
      exact ⟨h.2.1,h.2.2.1.le,h.2.2.2⟩)
  have hc : ((contourZeros chi hchi T).card : ℝ) ≤
      ∑ rho ∈ contourZeros chi hchi T, (zeroMultiplicity chi rho:ℝ) := by
    calc
      _ = ∑ rho ∈ contourZeros chi hchi T, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun rho hr => by
        have hp := zeroMultiplicity_pos chi hchi ((mem_contourZeros chi hchi T rho).mp hr).1
        exact_mod_cast hp)
  exact hc.trans hcount

lemma wide_zero_mem_contourZeros {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {T t : ℝ}
    (ht : |t| ≤ T+1) {rho : ℂ} (hr : ‖rho‖ ≤ 49/50)
    (hz : chi.LFunction (wideDirichletDiskPoint t rho) = 0) :
    wideDirichletDiskPoint t rho ∈ contourZeros chi hchi T := by
  apply (mem_contourZeros chi hchi T _).mpr
  have hre : 3/20 ≤ (wideDirichletDiskPoint t rho).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm rho).trans hr)).1
    rw [wideDirichletDiskPoint_re]
    linarith
  have hlt : (wideDirichletDiskPoint t rho).re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hz
  refine ⟨hz,hre,hlt,?_⟩
  have he : (wideDirichletDiskPoint t rho).im = t+(29/10:ℝ)*rho.im := by
    simp [wideDirichletDiskPoint,dirichletCenter]
  rw [he]
  have h := abs_add_le t ((29/10:ℝ)*rho.im)
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<29/10)] at h
  have hi := (Complex.abs_im_le_norm rho).trans hr
  linarith

lemma quarterPlane_coordinate_norm (s : ℂ) (hre : 1/4 ≤ s.re) (hre2 : s.re ≤ 2) :
    ‖(s-dirichletCenter s.im)/(29/10:ℂ)‖ ≤ 19/20 := by
  have he : s-dirichletCenter s.im = ((s.re-3:ℝ):ℂ) := by
    apply Complex.ext <;> simp [dirichletCenter]
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  norm_num
  linarith

lemma wideDirichletDiskPoint_coordinate (s : ℂ) :
    wideDirichletDiskPoint s.im ((s-dirichletCenter s.im)/(29/10:ℂ)) = s := by
  unfold wideDirichletDiskPoint
  field_simp
  ring

end Ostmann.Dirichlet

end

end OAI
