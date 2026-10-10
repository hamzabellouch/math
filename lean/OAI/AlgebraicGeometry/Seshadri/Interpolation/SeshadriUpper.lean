import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCurveBound
import OAI.AlgebraicGeometry.Seshadri.Interpolation.SeshadriUpperNumerics
import OAI.AlgebraicGeometry.Seshadri.Jets.EffectiveJets
import OAI.AlgebraicGeometry.Seshadri.Interpolation.AllCurveLowerBound

namespace OAI


                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.exists_curve_ratio_lt (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r) (a : ℝ)
    (ha : Real.sqrt ((selfIntersection S L:ℝ)/r) < a) :
    ∃ C : IntegralCurve S, 0 < totalMultiplicity S r C p ∧
      (curveDegree S L C:ℝ)/(totalMultiplicity S r C p:ℝ) < a := by
  classical
  by_contra hno
  have ha0 : 0 ≤ a := (Real.sqrt_nonneg _).trans ha.le
  have hC (C : IntegralCurve S) : a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ) := by
    by_cases hμ : 0 < totalMultiplicity S r C p
    · have hh : a ≤ (curveDegree S L C:ℝ)/(totalMultiplicity S r C p:ℝ) :=
        le_of_not_gt fun hh => hno ⟨C,hμ,hh⟩
      exact (le_div_iff₀ (show (0:ℝ) < totalMultiplicity S r C p by exact_mod_cast hμ)).mp hh
    · have hz : totalMultiplicity S r C p = 0 := by omega
      rw [hz,Nat.cast_zero,mul_zero]
      exact_mod_cast (C.ample_degree_positive S L hL).le
  obtain ⟨k,m,hk,hm,hquad,hlinear⟩ := NefNumerics.exists_homogeneous_surplus
    (selfIntersection S L) r a (S.selfIntersection_pos L hL) hr ha
  have hmix : 0 ≤ mixedEuler S L (L.pow k) := by
    rw [mixedEuler_pow_right S L hL,mixedEuler_self]
    exact mul_nonneg (Nat.cast_nonneg _) (S.selfIntersection_pos L hL).le
  have hsq : (∑ _i : Fin r, m^2:ℕ) < selfIntersection S (L.pow k) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
      S.selfIntersection_pow L hL] using hquad
  choose U hp hU e t het using fun i : Fin r => S.etale_line_frame_inside (L.pow k) ⊤
    (p.val i).image (by trivial)
  choose ρ hρ using fun i => affineComplexPoint_factor S.structureMap (U i) (p.val i) (hp i)
  obtain ⟨N,hN,hEff⟩ := S.eventually_effective_with_jets L hL (L.pow k) hmix
    (fun _ : Fin r => m) hsq U e t het ρ
  obtain ⟨s,hs,horders⟩ := hEff N le_rfl
  have hb := section_bound_of_curve_bound S L hL p a ha0 hC ((L.pow k).pow N) s hs U
    (fun i => localPowerFrame (U i).1 (e i) N) ρ hρ (fun _ : Fin r => N*m) horders
  rw [mixedEuler_pow_right S L hL,mixedEuler_pow_right S L hL,mixedEuler_self] at hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    Nat.cast_mul,Int.cast_mul,Int.cast_natCast] at hb
  have hh := mul_lt_mul_of_pos_left hlinear (show (0:ℝ) < N by exact_mod_cast hN)
  nlinarith only [hb,hh]

lemma Surface.seshadri_ratios_nonempty (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r) :
    {a : ℝ | ∃ C : IntegralCurve S, 0 < totalMultiplicity S r C p ∧
      a = (curveDegree S L C:ℝ)/(totalMultiplicity S r C p:ℝ)}.Nonempty := by
  obtain ⟨C,hC,-⟩ := S.exists_curve_ratio_lt L hL hr p
    (Real.sqrt ((selfIntersection S L:ℝ)/r)+1) (by linarith)
  exact ⟨_,C,hC,rfl⟩

lemma Surface.seshadri_ratios_bddBelow (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) :
    BddBelow {a : ℝ | ∃ C : IntegralCurve S, 0 < totalMultiplicity S r C p ∧
      a = (curveDegree S L C:ℝ)/(totalMultiplicity S r C p:ℝ)} := by
  refine ⟨0,?_⟩
  rintro a ⟨C,hC,rfl⟩
  exact div_nonneg (by exact_mod_cast (C.ample_degree_positive S L hL).le) (Nat.cast_nonneg _)

theorem Surface.seshadri_le_sqrt (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r) :
    seshadriConstant S L r p ≤ Real.sqrt ((selfIntersection S L:ℝ)/r) := by
  apply le_of_forall_gt
  intro a ha
  obtain ⟨C,hC,hlt⟩ := S.exists_curve_ratio_lt L hL hr p a ha
  exact (csInf_le (S.seshadri_ratios_bddBelow L hL p) ⟨C,hC,rfl⟩).trans_lt hlt

lemma Surface.seshadri_eq_of_curve_lower (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r)
    (hC : ∀ C : IntegralCurve S,
      Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
        (curveDegree S L C:ℝ)) :
    seshadriConstant S L r p = Real.sqrt ((selfIntersection S L:ℝ)/r) := by
  apply le_antisymm (S.seshadri_le_sqrt L hL hr p)
  apply le_csInf (S.seshadri_ratios_nonempty L hL hr p)
  rintro a ⟨C,hμ,rfl⟩
  exact (le_div_iff₀ (show (0:ℝ)<totalMultiplicity S r C p by exact_mod_cast hμ)).mpr (hC C)

theorem Surface.eventual_seshadri_equality (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) : EventualSeshadriEquality S L := by
  obtain ⟨r₀,hr₀,h⟩ := S.eventual_very_general_curve_lower L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,hC⟩ := h r hr
  exact ⟨Z,hZ,hne,fun p hp => S.seshadri_eq_of_curve_lower L hL (hr₀.trans_le hr) p (hC p hp)⟩
end
end MaximalSeshadri.Geometry

end



end OAI
