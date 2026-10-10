import OAI.Analysis.CircleDomains.Reflection.PrincipalReflectionSourceError
import OAI.Analysis.CircleDomains.Modulus.VariableWeightedPullback
import OAI.Analysis.CircleDomains.Topology.CompactMapContainment

namespace OAI

/-! The exact reflection error stays strongly small after transport by the
varying smooth principal inverses. Every compact set avoiding the limiting
pole has a common compact inverse collar avoiding the source pole. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma inverse_compact_away_pole (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∃K : Set ℂ,IsCompact K ∧ D.center i∉K ∧
      ∀ᶠn in atTop,MapsTo (D.approximation.map (D.limitData.index n)).symm T K := by
  have hsub : D.principal.symm '' T⊆({D.center i} : Set ℂ)ᶜ := by
    rintro _ ⟨z,hz,rfl⟩ heq
    apply hpole
    have hh : z=D.principal (D.center i) := by
      calc
        z=D.principal (D.principal.symm z) := (D.principal.apply_symm_apply z).symm
        _=D.principal (D.center i) := congrArg D.principal heq
    exact hh ▸ hz
  obtain ⟨V,hV,hTV,hVc,hK⟩ := exists_open_between_and_isCompact_closure
    (hT.image D.principal.symm.continuous) isOpen_compl_singleton hsub
  refine ⟨closure V,hK,fun h => hVc h rfl,?_⟩
  have ht := eventually_mapsTo_of_compact_convergence D.limitData.inverse hT hV
    (fun z hz => hTV (mem_image_of_mem _ hz))
  exact ht.mono fun n hn z hz => subset_closure (hn hz)

lemma reflection_target_error (D : AnalyticReflectionData C) (i : I)
    {T : Set ℂ} (hT : IsCompact T) (hpole : D.principal (D.center i)∉T) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀ᵐz ∂volume,z∈T → partialBar (D.reflectedApproximation i n) z=q n z := by
  obtain ⟨K,hK,hc,hretain⟩ := D.inverse_compact_away_pole i hT hpole
  let R := roundReflectionPlane (D.center i) (D.radius i)
  have hRK : IsCompact (R '' K) := hK.image_of_continuousOn
    (fun z hz => (roundReflectionPlane_differentiable (show z≠D.center i from fun h => hc (h ▸ hz))).continuousAt.continuousWithinAt)
  obtain ⟨e,he,her⟩ := D.reflection_source_error i hRK.measurableSet hRK.measure_lt_top.ne
  let P (n : ℕ) := (D.approximation.map (D.limitData.index n)).symm
  let B := (1+D.bound)/(1-D.bound)
  have hB : 0≤B := div_nonneg (by linarith [D.bound_nonneg]) (by linarith [D.bound_lt_one])
  have hdist (n : ℕ) := (smooth_beltrami_two_sided_distortion
    (D.approximation.map (D.limitData.index n)) (D.approximation.smooth _)
    (D.approximation.inverse_smooth _) (D.approximation.coefficient _)
    D.bound_nonneg D.bound_lt_one (D.approximation.coefficient_bound _)
    (D.approximation.equation _)).2
  obtain ⟨q,hq,hqr⟩ := exists_strong_variable_weighted_pullback P
    (fun n => D.approximation.inverse_smooth _) (fun n => D.approximation.smooth _) hB hdist e he
  refine ⟨q,hq,?_⟩
  filter_upwards [hretain] with n hn
  have hP := differentiable_homeomorph_quasiMeasurePreserving (P n)
    ((D.approximation.smooth _).differentiable (by simp))
  filter_upwards [hqr n,hP.ae (her n)] with z hqz hez hzT
  have hzK := hn hzT
  have hzc : P n z≠D.center i := fun h => hc (h ▸ hzK)
  have hRz : R (P n z)∈R '' K := mem_image_of_mem _ hzK
  have herr := D.reflectedApproximation_error i n hzc
  have hw := (roundReflectionPlane_partials (r:=D.radius i) hzc).2
  change partialBar (D.reflectedApproximation i n)
      (D.approximation.map (D.limitData.index n) (P n z))=_ at herr
  simp only [P,Homeomorph.apply_symm_apply] at herr
  rw [hqz,hez hRz]
  rw [herr]
  change star (partialZ (D.approximation.map (D.limitData.index n)) (R (P n z)))*
      star (partialBar R (P n z))*D.reflectionDefect i n (P n z)*star (partialZ (P n) z)=_
  change partialBar R (P n z)=roundReflectionWeight (D.center i) (D.radius i) (P n z) at hw
  rw [hw]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
