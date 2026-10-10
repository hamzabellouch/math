import Mathlib
import OAI.Combinatorics.UniformKServer.EpochSide

namespace OAI

                                            
section

/-! Evaluation of the actual epoch proportion parameters in the feasibility
inequalities.  All formulas use the persistent vector epoch, and retain the
zero-side/singleton case. -/
noncomputable section
namespace UniformKServer.EpochOutputParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem eta_range {p : AlphaEmpty.Config ι} (hp : AlphaEmpty.valid p) (i : ι) :
    AlphaEmpty.eta p i ∈ Set.Icc (0:ℝ) 1 := by
  cases p with
  | none => simp [AlphaEmpty.eta]
  | some p =>
    change AdaptiveAlpha.valid p at hp
    change DomainTransport.extend p.active (ProportionParameters.eta p.param) i ∈ Set.Icc (0:ℝ) 1
    unfold DomainTransport.extend
    split_ifs with hi
    · exact ⟨ProportionParameters.eta_nonneg hp.2 ⟨i,hi⟩, hp.2.2.2.2.1 ⟨i,hi⟩⟩
    · simp

theorem eta_regular {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) {U ell ct C : ℝ} (hl : 0 < ell) (hc : 0 ≤ ct)
    (i : ι) (hai : 0 < a i) (hi : EpochGeometry.dominant s ≠ some i) :
    AlphaEmpty.eta (EpochAlphaSchedule.config a s U ell ct C) i ≤
      ct*SideParameters.height (EpochGeometry.total s.base) (a i)/ell := by
  have hia := EpochParameters.mem_active.mpr hai
  have hn : (EpochParameters.active a).Nonempty := ⟨i,hia⟩
  have hh := EpochParameters.regular_height hs hai hi
  unfold EpochAlphaSchedule.config
  rw [ite_eq_left hn]
  cases ho : EpochGeometry.dominant s with
  | none =>
    simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.regular,DomainTransport.extend,
      ProportionParameters.eta,hia]
  | some o =>
    have hoa := EpochAlphaSchedule.dominant_active hs ho
    have hio : i ≠ o := by intro he; apply hi; simpa [he] using ho
    simp only [dite_eq_left hoa]
    split_ifs with hz
    · simp only [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.singleton,
        DomainTransport.extend,dite_eq_left hia,ProportionParameters.eta,mul_zero,zero_div]
      exact div_nonneg (mul_nonneg hc (by linarith)) hl.le
    · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.marked,DomainTransport.extend,
        ProportionParameters.eta,hia,hio,Subtype.ext_iff]

theorem eta_dominant {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (U ell ct C : ℝ) (o : ι)
    (ho : EpochGeometry.dominant s=some o) :
    AlphaEmpty.eta (EpochAlphaSchedule.config a s U ell ct C) o =
      ct*(U/EpochGeometry.total s.base)/ell := by
  have hoa := EpochAlphaSchedule.dominant_active hs ho
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hoa⟩
  unfold EpochAlphaSchedule.config
  rw [ite_eq_left hn,ho]
  simp only [dite_eq_left hoa]
  split_ifs with hz
  · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.singleton,DomainTransport.extend,
      ProportionParameters.eta,hoa,hz]
  · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.marked,DomainTransport.extend,
      ProportionParameters.eta,hoa]

theorem theta_active {a : ι → ℝ} {s : EpochGeometry.State ι}
    (ell cw b : ℝ) {i : ι} (hi : i ∈ EpochSide.active a s) :
    AdaptiveSide.theta (EpochSide.config a s ell cw b) i =
      cw*SideParameters.height (EpochGeometry.total s.base) (a i)/ell := by
  simp [AdaptiveSide.theta,EpochSide.config,DomainTransport.extend,hi,SideParameters.slack]

theorem side_product {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (ell cw b : ℝ) (o : ι) (ho : EpochGeometry.dominant s=some o) (i : ι) :
    AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i =
      cw/ell*((if i=o then 0 else a i)/EpochGeometry.total s.base) := by
  by_cases hi : i=o
  · subst i
    simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,EpochSide.active,ho,
      DomainTransport.extend]
  · by_cases hai : 0 < a i
    · have hmem : i ∈ EpochSide.active a s := by
        simp [EpochSide.active,ho,hi,EpochParameters.mem_active.mpr hai]
      have hreg : EpochGeometry.dominant s ≠ some i := by simpa [ho] using Ne.symm hi
      have hh : SideParameters.height (EpochGeometry.total s.base) (a i) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one (EpochParameters.regular_height hs hai hreg))
      simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,DomainTransport.extend,
        hmem,SideParameters.slack,SideParameters.offset,hi]
      field_simp [hh]
    · have hz : a i=0 := le_antisymm (le_of_not_gt hai) (ha i)
      have hmem : i ∉ EpochSide.active a s := by
        simp [EpochSide.active,ho,EpochParameters.mem_active,hz]
      simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,DomainTransport.extend,
        hmem,hi,hz]

theorem side_sum {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (ell cw b : ℝ) (o : ι) (ho : EpochGeometry.dominant s=some o) :
    (∑ i ∈ univ.erase o, AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i) =
      cw/ell*(EpochGeometry.side o a/EpochGeometry.total s.base) := by
  have he : (∑ i ∈ univ.erase o, if i=o then (0:ℝ) else a i) = EpochGeometry.side o a := by
    rw [EpochGeometry.side,←sum_erase_add _ _ (mem_univ o)]
    simp
  simp_rw [side_product hs ha ell cw b o ho]
  rw [←mul_sum,←sum_div,he]

theorem side_sum_bound {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    {ell cw : ℝ} (hl : 0 < ell) (hc : 0 ≤ cw) (b : ℝ)
    (o : ι) (ho : EpochGeometry.dominant s=some o) {U : ℝ}
    (hU : EpochParameters.sideReference a o U) :
    (∑ i ∈ univ.erase o, AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i) ≤
      (1001/1000)*cw/ell*(U/EpochGeometry.total s.base) := by
  rw [side_sum hs ha ell cw b o ho]
  have hp := (EpochGeometry.dominant_spec ho).1
  have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hU.2.2 hp.le)
    (div_nonneg hc hl.le)
  calc
    _ ≤ cw/ell*((1001/1000)*U/EpochGeometry.total s.base) := h
    _ = _ := by ring

end UniformKServer.EpochOutputParameters

end


end

end OAI
