import OAI.Geometry.SurfaceImmersion.Geometry.AxisDirectionJet

namespace OAI

/-! A source coordinate change preserves the regular direction zero of
the standard crosscap when the vertical direction is its kernel. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscap_composed_direction_bijective {g : Base → Base} (hg : ContDiff ℝ ∞ g)
    (p : Base) (hp : g p = 0) (hD : Function.Bijective (fderiv ℝ g p))
    (hy : fderiv ℝ g p (![0,1] : Base) 0 = 0) :
    Function.Bijective (axisDirectionJet (standardCrosscap ∘ g) p) := by
  have hc := bijective_base_vertical_columns (fderiv ℝ g p) hD hy
  have hfirst : ∀ v : Base, fderiv ℝ (standardCrosscap ∘ g) p v =
      standardCrosscapDerivative 0 (fderiv ℝ g p v) := by
    intro v
    rw [fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _)
      (hg.differentiable (by simp) p),hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    rfl
  have hsecond : ∀ v w : Base,
      fderiv ℝ (fderiv ℝ (standardCrosscap ∘ g)) p v w =
        (![fderiv ℝ g p v 1 * fderiv ℝ g p w 0 + fderiv ℝ g p v 0 * fderiv ℝ g p w 1,
          2 * fderiv ℝ g p v 1 * fderiv ℝ g p w 1],(0:ℝ)) +
          standardCrosscapDerivative 0 (fderiv ℝ (fderiv ℝ g) p v w) := by
    intro v w
    rw [SphericalJets.secondDerivative_comp hg isOpen_univ standardCrosscap_smooth.contDiffOn
      (mem_univ _) v w,hp,standardCrosscap_second,(standardCrosscap_hasFDerivAt 0).fderiv]
  have hker : ∀ z : Base × ℝ, axisDirectionJet (standardCrosscap ∘ g) p z = 0 → z = 0 := by
    intro z hz
    rw [axisDirectionJet_apply,hfirst,hsecond] at hz
    simp only [standardCrosscapDerivative_zero_apply] at hz
    have hz0 := congrFun (congrArg Prod.fst hz) 0
    have hz1 := congrFun (congrArg Prod.fst hz) 1
    have hz2 := congrArg Prod.snd hz
    have hb0 : fderiv ℝ g p z.1 0 = 0 := by
      have hh : fderiv ℝ g p z.1 0 * fderiv ℝ g p (![0,1] : Base) 1 = 0 := by
        simpa [hy] using hz0
      exact (mul_eq_zero.mp hh).resolve_right hc.1
    have hb1 : fderiv ℝ g p z.1 1 = 0 := by
      have hh : 2 * fderiv ℝ g p z.1 1 * fderiv ℝ g p (![0,1] : Base) 1 = 0 := by
        simpa using hz1
      have hmul := (mul_eq_zero.mp hh).resolve_right hc.1
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    have hzfirst : z.1 = 0 := by
      apply hD.1
      rw [map_zero]
      ext i
      fin_cases i
      · exact hb0
      · exact hb1
    have hzlast : z.2 = 0 := by
      have hh : z.2 * fderiv ℝ g p (![1,0] : Base) 0 = 0 := by
        simpa [hzfirst] using hz2
      exact (mul_eq_zero.mp hh).resolve_right hc.2
    exact Prod.ext hzfirst hzlast
  have hi : Function.Injective (axisDirectionJet (standardCrosscap ∘ g) p) := by
    intro z w he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,he,sub_self]
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
