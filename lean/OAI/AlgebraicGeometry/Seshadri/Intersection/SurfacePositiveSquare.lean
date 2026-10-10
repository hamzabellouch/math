import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PullbackSectionOpenExact
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceTopGrowth

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ample_degree_positive (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C := by
  obtain ⟨m,hm,hp⟩ := C.exists_positive_ambient_power S L hL
  rw [curveDegree_pow S L hL] at hp
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  nlinarith

theorem Surface.selfIntersection_pos (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    0 < selfIntersection S L := by
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have hp := C.ample_degree_positive S L hL
  have he := generated_curveDegree_eq_power_selfIntersection S L hL d k s hs v hne hC
  change curveDegree S L C = (d : ℤ)*selfIntersection S L at he
  rw [he] at hp
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

theorem generated_power_curveDegree_eq (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (d a : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(S.scheme,⊤)) (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S (L.pow a) C = (a : ℤ)*d*selfIntersection S L := by
  dsimp only
  rw [curveDegree_pow S L hL,generated_curveDegree_eq_power_selfIntersection S L hL d k s hs v hne hd]
  ring

lemma quadratic_lower_eventually_pos (q l c : ℤ) (hq : 0 < q) (B : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      0 < (n : ℤ)*((n : ℤ)-1)*q + 2*(n : ℤ)*l + 2*c - 2*B := by
  let N := (2*|l|+2*|c|+2*(B : ℤ)+3).toNat
  have hN : (N : ℤ) = 2*|l|+2*|c|+2*(B : ℤ)+3 := Int.toNat_of_nonneg (by positivity)
  refine ⟨N,?_,fun n hn => ?_⟩
  · have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  · have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
    rw [hN] at hn'
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    have hB : (0 : ℤ) ≤ B := Nat.cast_nonneg B
    have hq' : 1 ≤ q := hq
    have hbase : 0 ≤ (n : ℤ)*((n : ℤ)-1) := mul_nonneg hn0 (by omega)
    have hmul := mul_le_mul_of_nonneg_left hq' hbase
    have hl := neg_abs_le l
    have hc := neg_abs_le c
    have hlmul := mul_le_mul_of_nonneg_left hl
      (show (0 : ℤ) ≤ 2 * (n : ℤ) by positivity)
    have habsl := abs_nonneg l
    have habsc := abs_nonneg c
    nlinarith

theorem Surface.eventually_nonzero_power_section (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (L.pow n).sheaf, s ≠ 0 := by
  obtain ⟨B,hB⟩ := S.power_H0_quadratic_lower L hL
  obtain ⟨N,hN,hpos⟩ := quadratic_lower_eventually_pos (selfIntersection S L)
    (eulerCharacteristic S.structureMap 2 L.sheaf - eulerCharacteristic S.structureMap 2 (O S.scheme))
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) (S.selfIntersection_pos L hL) B
  refine ⟨N,hN,fun n hn => ?_⟩
  have hd : 0 < cohomologyDimension S.structureMap (L.pow n).sheaf 0 := by
    have hp := hpos n hn
    have hb := hB n
    omega
  let := Module.compHom (cohomology (L.pow n).sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite L hL (L.pow n)
  let : Nontrivial (cohomology (L.pow n).sheaf 0) := Module.finrank_pos_iff.mp hd
  obtain ⟨x,hx⟩ := exists_ne (0 : cohomology (L.pow n).sheaf 0)
  refine ⟨Ext.homEquiv₀ x,?_⟩
  intro hs
  apply hx
  have he := congrArg Ext.mk₀ hs
  exact (Ext.mk₀_homEquiv₀_apply x).symm.trans (he.trans (Ext.mk₀_zero _ _))

end
end MaximalSeshadri.Geometry

end

end OAI
