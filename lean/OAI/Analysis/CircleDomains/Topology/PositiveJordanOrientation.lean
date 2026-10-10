import OAI.Analysis.CircleDomains.Topology.JordanArgumentIncrement

namespace OAI

/-! Every regular Jordan parametrization has one of two orientations.
The fixed Green sign gives an actual positive parametrization. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma RegularJordanParametrization.injective_Ioc
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    InjOn γ (Ioc 0 1) := by
  intro s hs t ht he
  have h10 : γ 1 = γ 0 := by simpa using hγ.periodic 0
  by_cases hs1 : s = 1
  · by_cases ht1 : t = 1
    · exact hs1.trans ht1.symm
    · have hh : γ 0 = γ t := by simpa only [hs1, h10] using he
      have := hγ.injective (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
        ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ hh
      linarith [ht.1]
  · by_cases ht1 : t = 1
    · have hh : γ s = γ 0 := by simpa only [ht1, h10] using he
      have := hγ.injective ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
        (show (0 : ℝ) ∈ Ico 0 1 by norm_num) hh
      linarith [hs.1]
    · exact hγ.injective ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
        ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ he

lemma RegularJordanParametrization.reverse
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    RegularJordanParametrization H (fun t => γ (1-t)) := by
  refine ⟨hγ.smooth.comp (contDiff_const.sub contDiff_id), ?_, ?_, ?_, ?_⟩
  · intro t
    change γ (1-(t+1)) = γ (1-t)
    rw [show 1-(t+1) = -t by ring, show 1-t = -t+1 by ring]
    exact (hγ.periodic (-t)).symm
  · intro s hs t ht he
    have hh := hγ.injective_Ioc (show 1-s ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show 1-t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) he
    linarith
  · intro t
    have hi : HasDerivAt (fun s : ℝ => 1-s) (-1) t := by
      simpa only [id_eq, neg_mul, one_mul] using (hasDerivAt_id t).const_sub 1
    have hh := (hγ.smooth.differentiable (by simp) (1-t)).hasDerivAt.scomp t hi
    change deriv (γ ∘ (fun s : ℝ => 1-s)) t ≠ 0
    rw [hh.deriv]
    simpa using hγ.regular (1-t)
  · rw [← hγ.boundary]
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨1-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
      exact congrArg γ (by ring)

lemma exists_positive_jordan_parametrization
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : RegularJordanParametrization H γ) :
    ∃ δ : ℝ → ℂ, PositiveJordanParametrization H δ := by
  obtain ⟨e, he, harg⟩ := regular_jordan_argument_increment hgreen H γ hγ
  rcases le_total 0 e with hpos | hneg
  · have he1 : e = 1 := by simpa only [abs_of_nonneg hpos] using he
    refine ⟨γ, hγ.smooth, hγ.periodic, hγ.injective, hγ.regular, hγ.boundary, ?_⟩
    intro z hz
    obtain ⟨v, hv, hp, hi⟩ := harg z hz
    refine ⟨⟨fun t => v t, hv.continuous.comp continuous_subtype_val⟩, (fun t => hp t), ?_⟩
    change v 1 = v 0+1
    linarith
  · have he1 : e = -1 := by rw [abs_of_nonpos hneg] at he; linarith
    have hr := hγ.reverse
    refine ⟨_, hr.smooth, hr.periodic, hr.injective, hr.regular, hr.boundary, ?_⟩
    intro z hz
    obtain ⟨v, hv, hp, hi⟩ := harg z hz
    refine ⟨⟨fun t => v (1-t), hv.continuous.comp
      (continuous_const.sub continuous_subtype_val)⟩, ?_, ?_⟩
    · intro t
      exact hp (1-t)
    · change v (1-1) = v (1-0)+1
      simp only [sub_self, sub_zero]
      linarith

end CircleDomainRigidity

end

end OAI
