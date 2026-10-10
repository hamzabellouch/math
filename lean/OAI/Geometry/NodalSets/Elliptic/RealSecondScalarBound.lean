import Mathlib.Tactic.FinCases
import OAI.Geometry.NodalSets.Coefficients.RealFintypeCoefficientBound
import OAI.Geometry.NodalSets.Elliptic.RealWeakSecondForcing

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_second_scalar_forcing_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (B : Coord n → ℝ) (hB : ContDiff ℝ ∞ B) (k l : Fin n) :
    ∃ C > 0, ∀ (w : Coord n → ℝ) (U : Fin n → Coord n → ℝ)
      (H : Fin n → Fin n → Coord n → ℝ),
      MemLp w 2 (volume.restrict K) → (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∫ x in K, (w x)^2) ≤ E →
      (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
        MemLp (realSecondScalarForcing B w U H k l) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondScalarForcing B w U H k l x)^2) ≤ C*E := by
  let A : Coord n → Fin 4 → ℝ := fun x ↦
    ![B x,coordPartial B x l,coordPartial B x k,coordPartial (fun y ↦ coordPartial B y k) x l]
  have hA (a : Fin 4) : Continuous (fun x ↦ A x a) := by
    fin_cases a
    · exact hB.continuous
    · exact (real_coordPartial_smooth B hB l).continuous
    · exact (real_coordPartial_smooth B hB k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth B hB k) l).continuous
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨C,hC,fun w U H hw hU hH E hE hwE hUE hHE ↦ ?_⟩
  let V : Fin 4 → Coord n → ℝ := ![H k l,U k,U l,w]
  have hV (a : Fin 4) : MemLp (V a) 2 (volume.restrict K) := by
    fin_cases a
    · exact hH k l
    · exact hU k
    · exact hU l
    · exact hw
  have hVE (a : Fin 4) : (∫ x in K, (V a x)^2) ≤ E := by
    fin_cases a
    · exact hHE k l
    · exact hUE k
    · exact hUE l
    · exact hwE
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ a, A x a*V a x)=realSecondScalarForcing B w U H k l := by
    funext x
    simp [A,V,realSecondScalarForcing,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
