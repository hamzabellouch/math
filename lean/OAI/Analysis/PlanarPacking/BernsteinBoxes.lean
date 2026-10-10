import OAI.Analysis.PlanarPacking.MatrixIntervals
import OAI.Analysis.PlanarPacking.HighMomentsBase
import OAI.Analysis.PlanarPacking.BernsteinSign

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
noncomputable def normalizedH (a : Bool) (m : ℝ) (ell : ℕ) : ℝ :=
  fullMoment a false m ell+fullMoment (!a) true m ell
noncomputable def sourcePower (a : Bool) (m y : ℝ) (nu r : ℕ) : ℝ :=
  (if a then 1 else -1)*y^r*normalizedH a m (r+nu)
def bernsteinBox (T : Fin 29 → RBox) (k : Fin 29) : RBox :=
  sumBox (fun r : Fin (k.val+1) => (T ⟨r.val,by omega⟩).scale (k.val.choose r.val) ((28).choose r.val))
lemma bernsteinBox_contains {T : Fin 29 → RBox} {t : ℕ → ℝ}
    (hT : ∀ r : Fin 29,(T r).Contains (t r.val)) (k : Fin 29) :
    (bernsteinBox T k).Contains (powerToBernstein 28 t k.val) := by
  have hh := sumBox_contains (fun r : Fin (k.val+1) =>
    RBox.contains_scale (hT ⟨r.val,by omega⟩) (k.val.choose r.val) ((28).choose r.val)
      (by exact_mod_cast Nat.choose_pos (by omega : r.val≤28)))
  change (bernsteinBox T k).Contains _ at hh
  convert hh using 1
  unfold powerToBernstein
  simp only [Int.cast_natCast]
  change (∑ r ∈ Finset.range (k.val+1),_)=(∑ i : Fin (k.val+1), (k.val.choose i.val:ℝ)/(Nat.choose 28 i.val:ℝ)*t i.val)
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ => (k.val.choose r:ℝ)/(Nat.choose 28 r:ℝ)*t r) (k.val+1)).symm
lemma RBox.lower_lt {box : RBox} {x : ℝ} {u v : ℤ} (hh : box.Contains x)
    (hv : 0<v) (hc : precision*u<box.lo*v) : (u:ℝ)/v<x := by
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hc' : (precision:ℝ)*u<(box.lo:ℝ)*v := by exact_mod_cast hc
  have hc'' := hc'.trans_le (mul_le_mul_of_nonneg_right hh.1 hv'.le)
  apply (div_lt_iff₀ hv').mpr
  nlinarith [precision_pos]
end SharpPlanar

end OAI
