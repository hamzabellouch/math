import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentWalkCenters

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SymmetricCharts

@[simp] theorem endpointLabel_neg (z : CutRing) : endpointLabel (-z) = -endpointLabel z := rfl

def symmetricWindowStart (s : CutRing) : Fin 2 → ℤ := fun _ => -(endpointLabel s).natAbs

def symmetricWindowLength (s : CutRing) : ℕ := 2*(endpointLabel s).natAbs+2

theorem symmetricWindow_labels (s : CutRing) (j : Fin 2) :
    (symmetricWindowStart s j ≤ endpointLabel (-s) ∧
      endpointLabel (-s) < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel 0 ∧
      endpointLabel 0 < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel s ∧
      endpointLabel s < symmetricWindowStart s j+symmetricWindowLength s) := by
  have h₀ := Int.le_natAbs (a := endpointLabel s)
  have h₁ : -(endpointLabel s) ≤ ((endpointLabel s).natAbs:ℤ) := by
    simpa using (Int.le_natAbs (a := -endpointLabel s))
  simp only [symmetricWindowStart,symmetricWindowLength,endpointLabel_neg,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  change _ ∧ (_ ≤ (0:ℤ) ∧ (0:ℤ) < _) ∧ _
  omega

theorem signedShortSteps_bound (u : CutRing) (e : Fin 5) :
    |ordinary (signedShortSteps u e)| ≤ |ordinary u|+|ordinary (cutTau*u)| := by
  have h₀ := abs_nonneg (ordinary u)
  have h₁ := abs_nonneg (ordinary (cutTau*u))
  fin_cases e
  · change |ordinary 0| ≤ _
    rw [map_zero,abs_zero]
    linarith
  · exact le_add_of_nonneg_right h₁
  · change |ordinary (-u)| ≤ _
    rw [map_neg,abs_neg]
    exact le_add_of_nonneg_right h₁
  · exact le_add_of_nonneg_left h₀
  · change |ordinary (-(cutTau*u))| ≤ _
    rw [map_neg,abs_neg]
    exact le_add_of_nonneg_left h₀

theorem exists_symmetric_short_chart (a : ℕ) (r : CutRing) (hr : 0 < ordinary r) :
    ∃ s u v : CutRing, 0 < ordinary s ∧ ordinary s < ordinary r/2 ∧ u*v=1 ∧
      (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4 := by
  obtain ⟨s,hs,hs'⟩ := exists_cut_between (by linarith : (0:ℝ) < ordinary r/2)
  obtain ⟨u,v,huv,hshort⟩ := exists_short_tangent_basis (cutTau^a) (by linarith : 0 < ordinary s/4)
  exact ⟨s,u,v,hs,hs',huv,hshort⟩

theorem symmetric_chart_overlap_boxes (a : ℕ) (r s u : CutRing)
    (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    (d : Fin 2) (e : Fin 5) (j : Fin 2) :
    (-ordinary r < ordinary (-s) ∧ ordinary s < ordinary r) ∧
    (-ordinary r < ordinary (-s)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary s-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) := by
  have hh := (tangentOffset_ordinary_bound a d (signedShortSteps u e) j).trans
    (mul_le_mul_of_nonneg_left (signedShortSteps_bound u e) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|))
  have hh' := lt_of_le_of_lt hh hshort
  have hlim := abs_lt.mp hh'
  rw [map_neg]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
