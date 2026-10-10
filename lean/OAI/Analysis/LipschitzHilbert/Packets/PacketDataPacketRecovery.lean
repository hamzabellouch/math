import OAI.Analysis.LipschitzHilbert.Trees.SourceOriginalRecovery
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataOriginalIntegrability
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryIntegrability
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral

namespace OAI

/-! Recovery for the literal original packet sum. Integrability of the
original, masked, and translated boundary sums follows from their actual
Schwartz packets; the hypotheses here are the quantitative local budgets. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem eventually_physical_packet_recovery (q m decay : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (oldSlope : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (tops : Finset τ) (T : τ → SlopeBox) (g : AngularGrid)
      (w cutoff Kw D maskExponent a : ℝ),
    ∀ (hw : 0 < w), 0 < Kw → 0 ≤ a →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length) →
      (∀ j, g.eligible cutoff (w/P.length j) 0) →
    ∀ K : ℕ, 0 < K → ∀ gap : ℕ → ℝ,
    let value := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let original := fun z => ∑ s ∈ packets,
      P.crossPacketValue alt hAlt oldSlope b v f z s
    let masked := fun z => ∑ s ∈ packets, value z s
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let weight := fun t z => (T t).weight Kw D z
    let central := fun origin z => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff weight K gap (stop s) (assigned s) a z : ℝ):ℂ) •
          value z s
    ∀ (F source Z0 : Set (ℝ×ℝ)) (Z : ℝ → Set (ℝ×ℝ)),
      MeasurableSet F → MeasurableSet Z0 → (∀ origin, MeasurableSet (Z origin)) →
      (volume.prod volume) F ≠ ∞ → Z0 ⊆ F → (∀ origin, Z origin ⊆ Z0) →
    ∀ Nmass : ℝ, 0 ≤ Nmass →
      (volume.prod volume).real source = Nmass^2*(volume.prod volume).real F →
      Nmass ≤ Real.exp (2*L) →
      (∫ z, ‖original z‖^2 ∂volume.prod volume) ≤ (L^q)^2*(volume.prod volume).real source →
      (volume.prod volume).real (F\Z0) ≤ (L^(-q-(decay+1)))^2*(volume.prod volume).real F →
      (∀ origin, (volume.prod volume).real (Z0\Z origin) ≤
        L^m*(volume.prod volume).real source*Real.exp (-9*L)) →
      (∫ z in Z0, ‖original z-masked z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*(volume.prod volume).real F →
      (∀ origin, (∫ z in Z origin, ‖central origin z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*(volume.prod volume).real F) →
      IntervalIntegrable (fun origin => ∫ z in Z0, ‖masked z-central origin z‖ ∂volume.prod volume)
        volume 0 g.rootWidth →
      (∫ origin in (0:ℝ)..g.rootWidth,
        ∫ z in Z0, ‖masked z-central origin z‖ ∂volume.prod volume)/g.rootWidth ≤
          L^(-(decay+1))*Nmass*(volume.prod volume).real F →
      (∫ z in F, ‖original z‖ ∂volume.prod volume) ≤
        L^(-decay)*Nmass*(volume.prod volume).real F := by
  filter_upwards [eventually_original_recovery q m decay] with L hrec
  intro τ κ _ N Label Item _ P alt hAlt oldSlope b v f packets assigned tops T g
    w cutoff Kw D maskExponent a hw hKw ha hassigned hshort hstart K hK gap
    value original masked stop weight central F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0
    Nmass hN hratio hNexp henergy hfixed hmove hmask hcentral hinterval hboundary
  have horiginal : Integrable original (volume.prod volume) :=
    memLp_one_iff_integrable.mp (P.crossSum_memLp alt hAlt oldSlope b v f 1 packets)
  have hmasked : Integrable masked (volume.prod volume) :=
    P.physicalMaskedSum_integrable alt hAlt oldSlope b v f _ L maskExponent packets
  have hcent (origin : ℝ) : Integrable (central origin) (volume.prod volume) := by
    apply g.source_boundary_sum_integrable tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff weight
      (fun t _ => (div_pos hw (T t).length_pos).le)
      (fun t z => (T t).weight_pos hKw D z)
      (fun t => ((T t).continuous_weight hKw D).measurable)
      hK gap packets assigned stop hassigned _ a ha (volume.prod volume) value
      (fun s _ => P.physicalMaskedValue_integrable alt hAlt oldSlope b v f _ L maskExponent s)
    intro s hs
    have hle : w/(T (assigned s)).length ≤ w/P.length s.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cutoff (w/P.length s.1) (div_pos hw (P.length_pos s.1)) (hstart s.1))
  exact hrec (ℝ×ℝ) (EuclideanSpace ℂ κ) (volume.prod volume) original masked central
    (P.crossSum_memLp alt hAlt oldSlope b v f 2 packets)
    F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0 Nmass hN hratio hNexp henergy hfixed hmove
    (horiginal.sub hmasked).norm.integrableOn
    (fun origin => (hmasked.sub (hcent origin)).norm.integrableOn)
    (fun origin => (hcent origin).norm.integrableOn)
    hmask hcentral g.rootWidth g.rootWidth_pos hinterval hboundary

end LipschitzHilbert.PacketLatticeData

end

end OAI
