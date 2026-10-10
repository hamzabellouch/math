import OAI.Analysis.CircleDomains.Selection.RealBandPaidThreshold
import OAI.Analysis.CircleDomains.Topology.CompactBandNeighborhood

namespace OAI

/-! On a common branch range shorter than one, the paid circle threshold
is exactly the real threshold. Domain hits contribute a coordinate value;
flagged hits contribute a member of the actual real band. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_band_paid_values
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hav : a < v) (hvb : v < b) (hv : v ∈ Ico c (c + 1))
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ z ∈ range γ ∩ {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f},
      z ∈ B \ Flags →
      ¬ (connectedComponentIn {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f} z).Nontrivial) :
    v ∈ f '' (range γ ∩ D) ∨
      ∃ z ∈ range γ ∩ Flags, (z, v) ∈ intervalFiberHull (clusterGraph D f) := by
  have haV : x ∈ V := hγV ⟨0, γ.source⟩
  have hbV : y ∈ V := hγV ⟨1, γ.target⟩
  have hai := hbranch x haV a ((ha a).mpr rfl)
  have hbi := hbranch y hbV b ((hb b).mpr rfl)
  have hab : b - a < 1 := by linarith [hai.1, hbi.2]
  obtain ⟨z, hz, hp, hc⟩ := real_band_paid_threshold hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hBD hdense hV hinfty hM γ hγV
    ha hb hab hav hvb hfree
  obtain ⟨⟨w, t⟩, ht, he⟩ := hc
  change (w, (t : AddCircle (1 : ℝ))) = (z, (v : AddCircle (1 : ℝ))) at he
  have hw : w = z := congrArg Prod.fst he
  have htv : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
  subst w
  have htEq : t = v := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hbranch z (hγV hz) t ht) hv).mp htv
  subst t
  rcases hp with hzD | hzF
  · exact Or.inl ⟨z, ⟨hz, hzD⟩,
      ((intervalFiberHull_clusterGraph_on_open hD hf hzD).mp ht).symm⟩
  · exact Or.inr ⟨z, ⟨hz, hzF⟩, ht⟩

end CircleDomainRigidity

end

end OAI
