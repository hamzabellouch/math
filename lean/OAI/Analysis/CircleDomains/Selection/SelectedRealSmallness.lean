import OAI.Analysis.CircleDomains.Selection.RealTestCoordinateFamily
import OAI.Analysis.CircleDomains.Selection.GradedRealSelection
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! At every unmarked end the actual selected family contains arbitrarily
small anchored plateaus, with its real boundary-band norm. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def SmallAnchoredPlateaus {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (F : FiniteTransfer.CountableRealCoordinates G π σ)
    (EStar : Set Sphere) (p : Sphere) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (i : ℕ) (U : Set Sphere), IsOpen U ∧ p ∈ U ∧
    (∀ x ∈ U ∩ F.source, F.coordinate i x = 1) ∧
    (∀ x ∈ EStar, F.coordinate i x = 0) ∧
    Real.sqrt (∫ x in FiniteTransfer.realChartDomain G,
      FiniteTransfer.gradientEnergy (F.physical i)
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
    Real.sqrt (∑' s, (F.upper i s - F.lower i s) ^ 2) < δ

theorem selected_real_family_smallness
    {d : PathCodeData Sphere Sphere} (hdense : Dense d.quotientDomain)
    {π : Sphere → Sphere} {EStar : Set Sphere}
    (A : Set (GradedRealTest d π EStar)) (c : ℕ → UngatedRealTest d π EStar)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (hselected : ∀ b ∈ A, ∃ i, c i = b.toUngatedRealTest)
    (hcover : ∀ p ∈ d.dust \ M, ∀ k, ∃ b ∈ A, b.grade = k ∧ p ∈ b.region)
    (F : FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val))
    (hsource : F.source = d.quotientDomain)
    (hcoordinate : ∀ i, F.coordinate i = (c i).coordinate.quotient)
    (hphysical : ∀ i, F.physical i = (c i).coordinate.physical)
    (hbands : ∀ i (s : M),
      F.lower i s = liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val) ∧
      F.upper i s = limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val))
    (p : Sphere) (hp : p ∈ d.dust \ M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (i : ℕ) (U : Set Sphere), IsOpen U ∧ p ∈ U ∧
      (∀ x ∈ U ∩ F.source, F.coordinate i x = 1) ∧
      (∀ x ∈ EStar, F.coordinate i x = 0) ∧
      Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
        FiniteTransfer.gradientEnergy (F.physical i)
          (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (F.upper i s - F.lower i s) ^ 2) < δ := by
  obtain ⟨k, hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hδ)).exists
  obtain ⟨b, hb, hbk, hpb⟩ := hcover p hp k
  obtain ⟨i, hi⟩ := hselected b hb
  refine ⟨i, b.region, b.region_open, hpb, ?_, ?_, ?_⟩
  · intro x hx
    rw [hcoordinate i, hi]
    exact b.one x ⟨hx.1, hsource ▸ hx.2⟩
  · intro x hx
    rw [hcoordinate i, hi]
    exact b.zero x hx
  · have hn := (c i).ordinary_norm_le_size
      (by rw [hdense.closure_eq]; exact subset_univ _) (fun s : M => s.val)
      Subtype.val_injective (by simpa only [Subtype.range_val] using hMB)
    have hbsmall : (c i).size.toReal < 1 / ((k : ℝ) + 1) := by
      apply ENNReal.toReal_lt_of_lt_ofReal
      rw [hi, ← hbk]
      exact b.small
    apply lt_of_le_of_lt _ (hbsmall.trans hk)
    simpa only [hphysical, fun i s => (hbands i s).1, fun i s => (hbands i s).2] using hn

end CircleDomainRigidity

end

end OAI
