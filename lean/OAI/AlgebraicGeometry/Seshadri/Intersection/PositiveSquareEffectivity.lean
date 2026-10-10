import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.GeneralSurfaceEuler
import OAI.AlgebraicGeometry.Seshadri.Cohomology.GeneralSurfaceH2

namespace OAI


                                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.positive_square_eventually_effective (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hq : 0 < selfIntersection S M) (hm : 0 ≤ mixedEuler S L M) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 := by
  obtain ⟨B,C,hB⟩ := S.power_H2_linear_bound L hL M hm
  obtain ⟨N,hN,hpos⟩ := quadratic_lower_eventually_pos (selfIntersection S M)
    (eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) - C)
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) hq B
  refine ⟨N,hN,fun n hn => ?_⟩
  have hd : 0 < cohomologyDimension S.structureMap (M.pow n).sheaf 0 := by
    have hp := hpos n hn
    have he := S.arbitrary_power_euler_quadratic L hL M n
    rw [surface_euler_expansion] at he
    have hb : (cohomologyDimension S.structureMap (M.pow n).sheaf 2 : ℤ) ≤
        B+(C:ℤ)*n := by exact_mod_cast hB n
    have hi : (0 : ℤ) ≤ cohomologyDimension S.structureMap (M.pow n).sheaf 1 := Nat.cast_nonneg _
    have H : (0 : ℤ) < 2*(cohomologyDimension S.structureMap (M.pow n).sheaf 0 : ℤ) := by
      nlinarith
    exact_mod_cast (by omega : (0 : ℤ) < cohomologyDimension S.structureMap (M.pow n).sheaf 0)
  let := Module.compHom (cohomology (M.pow n).sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite L hL (M.pow n)
  let : Nontrivial (cohomology (M.pow n).sheaf 0) := Module.finrank_pos_iff.mp hd
  obtain ⟨x,hx⟩ := exists_ne (0 : cohomology (M.pow n).sheaf 0)
  refine ⟨Ext.homEquiv₀ x,?_⟩
  intro hs
  apply hx
  have he := congrArg Ext.mk₀ hs
  exact (Ext.mk₀_homEquiv₀_apply x).symm.trans (he.trans (Ext.mk₀_zero _ _))

theorem Surface.positive_square_effective_divisible (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hq : 0 < selfIntersection S M) (hm : 0 ≤ mixedEuler S L M)
    (q : ℕ) (hqpos : 0 < q) :
    ∃ K : ℕ, 0 < K ∧ ∀ k : ℕ, K ≤ k → q ∣ k →
      ∃ s : O S.scheme ⟶ (M.pow (k/q)).sheaf, s ≠ 0 := by
  obtain ⟨N,hN,h⟩ := S.positive_square_eventually_effective L hL M hq hm
  refine ⟨q*N,Nat.mul_pos hqpos hN,fun k hk hdiv => h _ ?_⟩
  rw [Nat.le_div_iff_mul_le hqpos]
  simpa only [Nat.mul_comm] using hk

end
end MaximalSeshadri.Geometry

end


end OAI
