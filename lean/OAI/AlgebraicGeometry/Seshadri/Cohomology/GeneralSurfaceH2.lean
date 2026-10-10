import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPowerDistribution
import OAI.AlgebraicGeometry.Seshadri.Intersection.MixedIntersection
import OAI.AlgebraicGeometry.Seshadri.Geometry.AmpleFromCover
import OAI.AlgebraicGeometry.Seshadri.Geometry.AmplePowers
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfacePositiveSquare
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH2Untwist

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.power_H2_linear_bound (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hM : 0 ≤ mixedEuler S L M) :
    ∃ B C : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (M.pow n).sheaf 2 ≤ B+C*n := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  let P := L.pow d
  have hP : P.IsAmple := hL.pow d hd
  have hdegP : 0 ≤ curveDegree S P C := le_of_lt (C.ample_degree_positive S P hP)
  have hdegM : 0 ≤ curveDegree S M C := by
    have H := generated_curveDegree_eq_mixedEuler S L hL M d k s hs v hne hC
    change curveDegree S M C = (d : ℤ)*mixedEuler S L M at H
    rw [H]
    exact mul_nonneg (Nat.cast_nonneg _) hM
  obtain ⟨e,he,hA⟩ := P.exists_ample_twist M hP
  let A := (P.pow e).tensor M
  obtain ⟨B,hB⟩ := S.power_H2_bounded A hA
  let g := cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1
  refine ⟨B,e*g,fun n => ?_⟩
  let T (j : ℕ) := (P.pow j).tensor (M.pow n)
  let f (j : ℕ) := cohomologyDimension S.structureMap (T j).sheaf 2
  have hstep (j : ℕ) : f j ≤ g+f (j+1) := by
    have hdeg : 0 ≤ curveDegree S (P.tensor (T j)) C := by
      rw [curveDegree_tensor S L hL]
      change 0 ≤ curveDegree S P C + curveDegree S ((P.pow j).tensor (M.pow n)) C
      rw [curveDegree_tensor S L hL (P.pow j) (M.pow n) C,
        curveDegree_pow S L hL P C j,curveDegree_pow S L hL M C n]
      exact add_nonneg hdegP (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hdegP) (mul_nonneg (Nat.cast_nonneg _) hdegM))
    have H := generated_section_H2_untwist S L hL P (T j) k s hs v hne hC hdeg
    let e' : (P.tensor (T j)).sheaf ≅ (T (j+1)).sheaf :=
      (lineTensorAssoc P (P.pow j) (M.pow n)).symm
    have E := cohomologyDimension_iso S.structureMap e' 2
    rw [E] at H
    exact H
  have H (j : ℕ) : f 0 ≤ j*g+f j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hstep j
      rw [Nat.succ_mul]
      omega
  have E := cohomologyDimension_iso S.structureMap (lineTwistPower P M e n) 2
  change cohomologyDimension S.structureMap (A.pow n).sheaf 2 = f (e*n) at E
  have hlast : f (e*n) ≤ B := E ▸ hB n
  have hzero : f 0 = cohomologyDimension S.structureMap (M.pow n).sheaf 2 :=
    cohomologyDimension_iso S.structureMap (moduleTensorUnit (M.pow n).sheaf) 2
  calc
    cohomologyDimension S.structureMap (M.pow n).sheaf 2 = f 0 := hzero.symm
    _ ≤ (e*n)*g+f (e*n) := H (e*n)
    _ ≤ (e*n)*g+B := Nat.add_le_add_left hlast _
    _ = B+(e*g)*n := by ring

end
end MaximalSeshadri.Geometry

end


end OAI
