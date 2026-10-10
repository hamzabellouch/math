import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CapInformationBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.InverseNetPropagationBarrier
import OAI.Analysis.CoulombIonization.Localization.InverseNetEventsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UniformNetErrors_barrier_scope

open Filter
open scoped Topology

lemma uniform_power_error_eventually {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} {a C eps : ℝ} (ha : 0 < a) (heps : 0 < eps)
    (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ u : ℝ, 0 < u → u ≤ s i → C*u^a ≤ eps := by
  let A : ι → Type := fun i => {u : ℝ // 0 < u ∧ u ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  let u : (Σ i, A i) → ℝ := fun q => q.2.1
  have ht : Tendsto π L l := tendsto_comap
  have hu0 : Tendsto u L (𝓝 0) := squeeze_zero
    (fun q => q.2.2.1.le) (fun q => q.2.2.2) (hs0.comp ht)
  have hp : Tendsto (fun q => C*u q^a) L (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne',mul_zero] using (tendsto_const_nhds (x := C)).mul (hu0.rpow_const (Or.inr ha.le))
  have he := Filter.eventually_comap.mp (hp.eventually (gt_mem_nhds heps))
  filter_upwards [he] with i hi
  intro v hv hvs
  exact (hi ⟨i,⟨v,hv,hvs⟩⟩ rfl).le

end Work_UniformNetErrors_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem original_spatial_inverse_propagation {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ : ℝ) (j : Fin K) (q : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    {u lo hi xi eta D L A : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hxi : 0 < xi) (hlo : 16*xi < lo) (hD : 0 ≤ D) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (H : Finset ℝ) (Q : Finset Space)
    (hQ : ∀ x ∈ Q, 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8)
    (hcover : ∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ∃ x ∈ Q, ‖x-y‖ ≤ u^2)
    (hmargin : ∀ h ∈ Icc lo hi, localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8))
    (hheight : ∀ h ∈ Icc lo hi, (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
      (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4))
    (hsmallA : A*(16*(tfPatchCapConstant+3)*100000^4+D)*u^(1-3*masterExponent) ≤ xi/4)
    (hsmallB : A*u ≤ 1)
    (hsmallD : (64*L+192*D)*u^(1-4*masterExponent) ≤ eta)
    (hden : ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ 2*u →
      originalQueryDensity F r₀ j c₁ r₀ s q y ≤ D*u^(-6-3*masterExponent))
    (hquery : ∀ y z : Space, u ≤ ‖y‖ → ‖y‖ ≤ 2*u → u ≤ ‖z‖ → ‖z‖ ≤ 2*u →
      ‖originalQueryDensity F r₀ j c₁ r₀ s q y-originalQueryDensity F r₀ j c₁ r₀ s q z‖ ≤
        L*u^(-7-4*masterExponent)*‖y-z‖)
    (hfield : ∀ y x : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ‖x-y‖ ≤ u^2 →
      |‖x‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q x-
        ‖y‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y| ≤
        A*(16*(tfPatchCapConstant+3)*100000^4+D)*u^(1-3*masterExponent)+
          A*u*max (-(‖y‖^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y)) 0)
    (hgood : q ∉ ⋃ k ∈ H, ⋃ x ∈ Q,
      originalLowFailure F Z lam r₀ s c₁ k (xi/4) j x ∪
        originalHighFailure F Z lam r₀ s c₁ k (xi/4) j x) :
    ∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 → ∀ h ∈ Icc lo hi,
      (localTFResponse h < (localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y →
        h-xi ≤ (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y) ∧
      ((localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y < localTFResponse h →
        (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y ≤ h+xi) := by
  have hcap : 0 < tfPatchCapConstant+3 := by linarith [tfPatchCapConstant_pos]
  have hnorm := inverse_net_propagation (B := {y : Space | 11*u/8 ≤ ‖y‖ ∧ ‖y‖ ≤ 13*u/8})
    (Q := Q) (H := H)
    (v := fun y => (localCellRadius y)^4*originalQueryField F Z lam r₀ j c₁ r₀ s q y)
    (rho := fun y => (localCellRadius y)^6*originalQueryDensity F r₀ j c₁ r₀ s q y)
    hxi hlo hsmallA hsmallB hmargin hheight
  apply fun y hyl hyh => hnorm ?_ ?_ y ⟨hyl,hyh⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy.1 hy.2
    refine ⟨x,hx,?_,?_⟩
    · simp only [localCellRadius_normalized]
      apply divided_net_field_variation (by norm_num : (1:ℝ) ≤ 100000^4)
        (by positivity) (hfield y x hy.1 hy.2 hxy)
    · have hyl : u ≤ ‖y‖ := by linarith [hy.1]
      have hyh : ‖y‖ ≤ 2*u := by linarith [hy.2]
      have hxl : u ≤ ‖x‖ := by linarith [(hQ x hx).1]
      have hxh : ‖x‖ ≤ 2*u := by linarith [(hQ x hx).2]
      have hn : 0 ≤ originalQueryDensity F r₀ j c₁ r₀ s q y :=
        jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _
      have hd := normalized_density_net_variation hu hD hL hxh hyh hxy hn (hden y hyl hyh)
        (hquery x y hxl hxh hyl hyh)
      have hp : u^(1-3*masterExponent) ≤ u^(1-4*masterExponent) :=
        Real.rpow_le_rpow_of_exponent_ge hu hu1 (by norm_num [masterExponent])
      have hd' : |‖x‖^6*originalQueryDensity F r₀ j c₁ r₀ s q x-
          ‖y‖^6*originalQueryDensity F r₀ j c₁ r₀ s q y| ≤ eta := by
        apply le_trans hd
        calc _ ≤ 64*L*u^(1-4*masterExponent)+192*D*u^(1-4*masterExponent) := by gcongr
             _ = (64*L+192*D)*u^(1-4*masterExponent) := by ring
             _ ≤ eta := hsmallD
      simp only [localCellRadius_normalized]
      rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 100000^6)]
      exact (div_le_self (abs_nonneg _) (by norm_num)).trans hd'
  · intro x hx k hk
    have hfail : q ∉ originalLowFailure F Z lam r₀ s c₁ k (xi/4) j x ∪
        originalHighFailure F Z lam r₀ s c₁ k (xi/4) j x := by
      intro hq
      apply hgood
      exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,hq⟩⟩⟩⟩
    have hr : 0 < localCellRadius x := by
      dsimp [localCellRadius]
      have hn : 0 < ‖x‖ := by linarith [(hQ x hx).1]
      positivity
    have h4 := pow_pos hr 4
    have h6 := pow_pos hr 6
    constructor
    · intro hh
      apply hfail
      right
      exact ⟨(le_div_iff₀ h4).mpr (by nlinarith [hh.1]),
        (div_le_iff₀ h6).mpr (by nlinarith [hh.2])⟩
    · intro hh
      apply hfail
      left
      exact ⟨(div_le_iff₀ h4).mpr (by nlinarith [hh.1]),
        (le_div_iff₀ h6).mpr (by nlinarith [hh.2])⟩

end CoulombAtom

end

end OAI
