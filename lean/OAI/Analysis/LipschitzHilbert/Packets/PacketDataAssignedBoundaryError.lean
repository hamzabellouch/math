import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedBoundaryPrefix
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryIntegratedError
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPathRegularity

namespace OAI

/-! The integrated boundary error for the original selected physical
packets. Raw assigned-reference concentration supplies the prefix bounds;
the top cutoff and every packet cutoff are their actual last eligible levels. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assigned_boundary_integrated_error
    (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (tops : Finset τ) (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (test : ℝ×ℝ → EuclideanSpace ℂ κ)
    (g : AngularGrid) (L maskExponent cutoff Kw D : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (hshort : ∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length)
    (hcondition : ∀ s ∈ packets, P.referenceCondition oldSlope (T (assigned s)).slope
      (R (assigned s)) cone w s.1 s.2.1)
    (hstart : ∀ j, g.eligible cutoff (w/P.length j) 0)
    (htopstart : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) 0)
    (a A H : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (μ : Measure (ℝ×ℝ)) [SFinite μ] (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good μ)
    (hlog : ∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H) :
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    (∀ x ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v test j (orig t j l) u.val)
        0 lower upper x.1 (x.2-(T t).slope*x.1)‖ ≤ A*((T t).weight Kw D x)^8) →
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let value := P.physicalMaskedValue alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let C := 8*a*A*epsilon*((2:ℝ)^D)^7*(1+H)
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod (μ.restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂μ) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂μ)/g.rootWidth ≤
        C*(∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂μ) := by
  intro Q orig alts halt hinterval stop value epsilon C err
  let M := fun t => g.lastEligible cutoff (w/(T t).length) (div_pos hw (T t).length_pos)
  have he (t : τ) (ht : t ∈ tops) : g.eligible cutoff (w/(T t).length) (M t) :=
    g.eligible_lastEligible cutoff (w/(T t).length) (div_pos hw (T t).length_pos) (htopstart t ht)
  have hmax (s : P.PacketIndex) (hs : s ∈ packets) : stop s ≤ M (assigned s) :=
    g.lastEligible_antitone_precision cutoff (w/(T (assigned s)).length) (w/P.length s.1)
      (div_pos hw (T (assigned s)).length_pos) (div_pos hw (P.length_pos s.1))
      (div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs))
      (htopstart (assigned s) (hassigned s hs)) (hstart s.1)
  have hv (s : P.PacketIndex) : Measurable (fun x => value x s) :=
    (P.physicalMaskedValue_continuous alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent s).measurable
  have hprefix (x : ℝ×ℝ) (hx : x ∈ good) (t : τ) (ht : t ∈ tops) (k : ℕ) (_hk : k ≤ M t) :
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value x s‖ ≤
        A*((T t).weight Kw D x)^8 := by
    apply P.assignedPhysicalSourcePrefix_norm_le packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v test L maskExponent x t
      (fun s hs hst => by simpa only [hst] using hcondition s hs)
      (A*((T t).weight Kw D x)^8) (hinterval x hx t ht) g cutoff hstart k
  exact g.source_boundary_integrated_error L hbranch hsmall tops T w cutoff Kw D hw hKw hD hK
    M he a ha packets assigned hassigned stop value hv hmax A H hA μ good hgood hweight hlog hprefix

end LipschitzHilbert.PacketLatticeData

end

end OAI
