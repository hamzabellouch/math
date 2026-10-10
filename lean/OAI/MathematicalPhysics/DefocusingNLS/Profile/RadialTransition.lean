import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialNoReturn

namespace OAI

/-! The limiting amplitude has one plateau and one nonunit exterior component. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_limit_single_transition (R r₀ : ℝ) (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (A D V : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Ioc 0 1)
    (hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo 0 R, A r < 1 → HasDerivAt D (-11/r*D r-V r*A r) r)
    (hV : ∀ r ∈ Ioo 0 R, 0 < V r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 r₀)) (hAR : A R < 1) :
    ∃ ρ ∈ Ico r₀ R, EqOn A (fun _ => 1) (Icc 0 ρ) ∧
      (∀ r ∈ Ioc ρ R, A r < 1) ∧ D ρ=0 := by
  let S := Icc 0 R ∩ A ⁻¹' {1}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_singleton.preimage hA)
  have hr₀S : r₀ ∈ S := ⟨⟨hr₀.le,hr₀R.le⟩,hcore ⟨hr₀.le,le_rfl⟩⟩
  obtain ⟨ρ,hρ⟩ := hS.exists_isGreatest ⟨r₀,hr₀S⟩
  have hρR : ρ < R := lt_of_le_of_ne hρ.1.1.2 (by
    intro he
    have h := hρ.1.2
    change A ρ=1 at h
    rw [he] at h
    linarith)
  have hr₀ρ : r₀ ≤ ρ := hρ.2 hr₀S
  have hρ0 : 0 < ρ := hr₀.trans_le hr₀ρ
  have hρA : A ρ=1 := hρ.1.2
  refine ⟨ρ,⟨hr₀ρ,hρR⟩,?_,?_,?_⟩
  · exact radial_subunit_no_return R A D V hA hAI hAD hDE hV 0 ρ le_rfl hρ0 hρR.le
      (hcore ⟨le_rfl,hr₀.le⟩) hρA
  · intro r hr
    have hrR : r ∈ Icc 0 R := ⟨hρ0.le.trans hr.1.le,hr.2⟩
    apply lt_of_le_of_ne (hAI r hrR).2
    intro he
    have hrS : r ∈ S := ⟨hrR,he⟩
    exact hr.1.not_ge (hρ.2 hrS)
  · have hm : IsLocalMax A ρ := by
      filter_upwards [Ioo_mem_nhds hρ0 hρR] with r hr
      show A r ≤ A ρ
      rw [hρA]
      exact (hAI r ⟨hr.1.le,hr.2.le⟩).2
    rw [← (hAD ρ ⟨hρ0,hρR⟩).deriv]
    exact hm.deriv_eq_zero

end DefocusingNLS

end OAI
