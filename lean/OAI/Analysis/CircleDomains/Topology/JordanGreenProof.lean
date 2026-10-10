import OAI.Analysis.CircleDomains.Modulus.FixedNormalOrientation
import OAI.Analysis.CircleDomains.Sobolev.InteriorLocalGreen
import OAI.Analysis.CircleDomains.Sobolev.FiniteGreenAssembly
import OAI.Analysis.CircleDomains.Sobolev.FiniteSmoothCover

namespace OAI

/-! The signed Green formula on a regular Jordan disk, proved by a finite
smooth partition and the actual local normal charts. -/
open Set Function MeasureTheory Metric Bornology
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_green {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    ∃ ε : ℝ, |ε| = 1 ∧ ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
      ε * planarFormIntegral P Q γ =
        ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  classical
  obtain ⟨ε,hε,hboundary⟩ := regular_jordan_local_green_sign hγ
  let K := closure (jordanInterior H)
  have hloc (x : K) : ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ IsBounded U ∧
      ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        HasCompactSupport P → HasCompactSupport Q → tsupport P ⊆ U → tsupport Q ⊆ U →
        ε * planarFormIntegral P Q γ =
          ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    by_cases hx : (x : ℂ) ∈ jordanInterior H
    · refine ⟨jordanInterior H ∩ ball (x : ℂ) 1,
        (jordanInterior_isOpen H).inter isOpen_ball,⟨hx,mem_ball_self zero_lt_one⟩,
        isBounded_ball.subset inter_subset_right,?_⟩
      intro P Q hP hQ hcP hcQ hPs hQs
      exact interior_local_green hγ ε hP hQ hcP hcQ
        (hPs.trans inter_subset_left) (hQs.trans inter_subset_left)
    · have hxf : (x : ℂ) ∈ frontier (jordanInterior H) := by
        rw [frontier,(jordanInterior_isOpen H).interior_eq]
        exact ⟨x.property,hx⟩
      obtain ⟨t,_,ht⟩ := hγ.boundary.symm ▸ hxf
      obtain ⟨U,hU,htU,hUb,hh⟩ := hboundary t
      refine ⟨U,hU,ht ▸ htU,hUb,?_⟩
      intro P Q hP hQ _ _ hPs hQs
      exact hh P Q hP hQ hPs hQs
  choose U hU hxU hb hgreen using hloc
  obtain ⟨I,ρ,hρ,hρc,hρU,hρsum⟩ := exists_finite_smooth_cover
    (isCompact_closure_jordanInterior H) U hU hxU hb
  refine ⟨ε,hε,?_⟩
  intro P Q hP hQ
  apply finite_green_assembly hγ ρ hρ hρsum ε hP hQ
  intro i
  exact hgreen i.val (fun z => ρ i z * P z) (fun z => ρ i z * Q z)
    ((hρ i).mul hP) ((hρ i).mul hQ) (hρc i).mul_right (hρc i).mul_right
    (tsupport_mul_subset_left.trans (hρU i)) (tsupport_mul_subset_left.trans (hρU i))

end CircleDomainRigidity

end

end OAI
