import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntersectionBilinear
import OAI.AlgebraicGeometry.Seshadri.Blowup.EventualExceptionalAmple
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupIntersectionGrowth

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

lemma LineBundle.ample_of_iso {X : Scheme.{0}} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (hL : L.IsAmple) : M.IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let c := (modulePowFunctor n).mapIso e
  have he : sectionOpen X (s ≫ c.hom) = sectionOpen X s :=
    SectionOpens.isoOpen_postcomp _ _
  exact ⟨n,hn,s ≫ c.hom,he ▸ hs,he ▸ hsub,he ▸ ha⟩

lemma IsBlowup.eventual_ample_power_twist {X Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [CompactSpace X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (hb : IsBlowup I f) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      (((L.pullback f).pow (a*(n+1))).tensor J).IsAmple := by
  obtain ⟨a,N,ha,h⟩ := hb.eventual_ample_exceptional_twist L hL J ι hJ
  refine ⟨a,N,ha,fun n hn => ?_⟩
  apply LineBundle.ample_of_iso _ _ _ (h n hn)
  exact moduleTensorIso ((modulePowFunctor (n+1)).mapIso (PullbackTensor.powIso f L a) ≪≫
    linePowerMul (L.pullback f) a (n+1)) (Iso.refl _)

theorem Surface.blowup_intersections (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
    (hf : f ≫ S.structureMap = T.structureMap)
    (hbl : IsBlowup (centreIdeal S r p) f)
    (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι) :
    selfIntersection T (L.pullback f) = selfIntersection S L ∧
    mixedEuler T (L.pullback f) J = 0 ∧
    -(r:ℤ) ≤ selfIntersection T J ∧ selfIntersection T J ≤ 0 := by
  obtain ⟨a,N,ha,hA⟩ := hbl.eventual_ample_power_twist L hL J ι hJ
  let P := L.pullback f
  let A := (P.pow (a*(N+1))).tensor J
  have hAA : A.IsAmple := hA N le_rfl
  let q := selfIntersection T P-selfIntersection S L
  let b := mixedEuler T P J
  let c := selfIntersection T J
  have H (n : ℕ) : -(r:ℤ) ≤ (a:ℤ)^2*q*(n:ℤ)^2+
      (2*(a:ℤ)^2*(N+1)*q+2*a*b)*n+
      ((a:ℤ)^2*(N+1)^2*q+2*a*(N+1)*b+c) ∧
      (a:ℤ)^2*q*(n:ℤ)^2+(2*(a:ℤ)^2*(N+1)*q+2*a*b)*n+
      ((a:ℤ)^2*(N+1)^2*q+2*a*(N+1)*b+c) ≤ 0 := by
    have hh := S.ample_exceptional_square_squeeze T L hL p f hf hbl J ι hJ
      (a*((n+N)+1)) (hA (n+N) (by omega))
    rw [T.selfIntersection_tensor_general A hAA,T.selfIntersection_pow A hAA,
      mixedEuler_pow_left_general T A hAA] at hh
    dsimp [q,b,c,P]
    push_cast at hh
    constructor <;> nlinarith only [hh.1,hh.2]
  obtain ⟨hq,hb,hlo,hhi⟩ := quadratic_bounded _ _ _ (-(r:ℤ)) 0 H
  have haZ : (a:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hq0 : q = 0 := (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ haZ)
  have hb0 : b = 0 := by
    rw [hq0,mul_zero,zero_add] at hb
    exact (mul_eq_zero.mp hb).resolve_left (mul_ne_zero (by norm_num) haZ)
  dsimp [q] at hq0
  refine ⟨sub_eq_zero.mp hq0,hb0,?_,?_⟩
  · simpa only [show q=0 from sub_eq_zero.mpr (sub_eq_zero.mp hq0),hb0,mul_zero,zero_add] using hlo
  · simpa only [show q=0 from sub_eq_zero.mpr (sub_eq_zero.mp hq0),hb0,mul_zero,zero_add] using hhi

end
end MaximalSeshadri.Geometry

end



end OAI
