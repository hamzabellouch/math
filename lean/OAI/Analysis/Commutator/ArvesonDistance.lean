import Mathlib
import OAI.Analysis.Commutator.ArvesonAnnihilator
import OAI.Analysis.Commutator.WOTCompact

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Pointwise

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutant_membership (M : VonNeumannAlgebra H) (T : H →WOT[ℂ] H) :
    T∈commutant (M : Set (H →L[ℂ] H)) ↔ T.toCLM∈M.commutant := by
  change (∀ a∈M,ofCLM a*T=T*ofCLM a) ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  constructor <;> intro h a ha
  · exact congrArg toCLM (h a ha)
  · apply toCLM_injective
    exact h a ha

lemma ball_functional_bound (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    {c u : ℝ} (hc : 0<c) (hu : 0≤u)
    (hφ : ∀ T∈normBall (H:=H) c, (φ T).re≤u) :
    c*‖φ.comp ContinuousLinearMap.WOTofCLM‖≤u := by
  let ψ : StrongDual ℂ (H →L[ℂ] H) := φ.comp ContinuousLinearMap.WOTofCLM
  let ψr : StrongDual ℝ (H →L[ℂ] H) := (StrongDual.extendRCLikeₗᵢ (𝕜:=ℂ)).symm ψ
  have hn : ‖ψr‖=‖ψ‖ := LinearIsometryEquiv.norm_map _ _
  have hnorm : ‖ψr‖≤u/c := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hu hc.le)
    intro T hT
    have hp := hφ (ofCLM (c • T)) (by
      change ‖c • T‖≤c
      simp [norm_smul,hT,abs_of_pos hc])
    have hm := hφ (ofCLM ((-c) • T)) (by
      change ‖(-c) • T‖≤c
      simp [norm_smul,hT,abs_of_pos hc])
    have hp' : c*ψr T≤u := by
      change ψr (c • T)≤u at hp
      simpa only [map_smul,smul_eq_mul] using hp
    have hm' : -(c*ψr T)≤u := by
      change ψr ((-c) • T)≤u at hm
      simpa only [map_smul,smul_eq_mul,neg_mul] using hm
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · apply (le_of_mul_le_mul_left ?_ hc)
      rw [mul_neg, mul_div_cancel₀ _ hc.ne']
      linarith
    · exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hp')
  rw [hn] at hnorm
  simpa only [mul_comm] using (le_div_iff₀ hc).mp hnorm

theorem exists_commutant_approximation (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
    {c : ℝ} (hc : 0≤c) (hcb : AmplifiedBound M G c) :
    ∃ T : H →L[ℂ] H, T∈M.commutant ∧ ‖G-T‖≤c := by
  classical
  let s := (commutant (M : Set (H →L[ℂ] H)) : Set (H →WOT[ℂ] H))+normBall c
  have hs0 : (0 : H →WOT[ℂ] H)∈s := by
    exact Set.mem_add.mpr ⟨0,(commutant _).zero_mem,0,by simpa [normBall] using hc,add_zero _⟩
  have hs : ofCLM G∈s := by
    by_contra hG
    have hsv : Convex ℝ s := ((commutant _).restrictScalars ℝ).convex.add (convex_normBall c)
    have hsc : IsClosed s := isClosed_commutant_add_ball _ hc
    obtain ⟨φ,u,hφ,hu⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜:=ℂ) hsv hsc hG
    have hu0 : 0<u := by simpa using hφ 0 hs0
    have hzero : ∀ T∈M.commutant,φ (ofCLM T)=0 := by
      intro T hT
      by_contra hn
      let z : ℂ := ((u+1 : ℝ) : ℂ)/φ (ofCLM T)
      have hz : z • ofCLM T∈s := by
        apply Set.mem_add.mpr
        refine ⟨z • ofCLM T, (commutant _).smul_mem z ?_,0,?_,add_zero _⟩
        · exact (commutant_membership M _).mpr hT
        · simpa [normBall] using hc
      have hh := hφ (z • ofCLM T) hz
      rw [map_smul,smul_eq_mul] at hh
      dsimp [z] at hh
      rw [div_mul_cancel₀ _ hn,Complex.ofReal_re] at hh
      linarith
    have hb : ∀ V∈normBall (H:=H) c,(φ V).re≤u := by
      intro V hV
      exact (hφ V (Set.mem_add.mpr ⟨0,(commutant _).zero_mem,V,hV,zero_add _⟩)).le
    have hnorm := annihilator_bound M G hc hcb φ hzero
    have hup : c*‖φ.comp ContinuousLinearMap.WOTofCLM‖≤u := by
      rcases hc.eq_or_lt with h|h
      · simp [←h,hu0.le]
      · exact ball_functional_bound φ h hu0.le hb
    change u < (φ (ofCLM G)).re at hu
    have hre := Complex.re_le_norm (φ (ofCLM G))
    linarith
  obtain ⟨T,hT,V,hV,hTV⟩ := Set.mem_add.mp hs
  refine ⟨T.toCLM,(commutant_membership M T).mp hT,?_⟩
  have hG : G-T.toCLM=V.toCLM := by
    have hh := congrArg toCLM hTV
    change T.toCLM+V.toCLM=G at hh
    rw [←hh,add_sub_cancel_left]
  rw [hG]
  exact hV

end Kadison.WOTDistance

end

end
end

end OAI
