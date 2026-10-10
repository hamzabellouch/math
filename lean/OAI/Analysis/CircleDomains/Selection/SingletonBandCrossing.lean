import OAI.Analysis.CircleDomains.Topology.SingletonPathDetour
import OAI.Analysis.CircleDomains.Topology.CompactBandCrossing

namespace OAI

/-! The topological threshold step in Lemma 6.6. A path joining opposite
band values must have a nonsingleton level contact. Consequently, when
free contacts have singleton components, a threshold is paid at a domain
point or a flagged point. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_nonsingleton_band_contact
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {K : Set (Sphere × ℝ)} (hK : IsCompact K)
    (hne : ∀ z ∈ V, {t : ℝ | (z, t) ∈ K}.Nonempty)
    (hinterval : ∀ z ∈ V, OrdConnected {t : ℝ | (z, t) ∈ K})
    {v : ℝ} (hlevel : ∀ z ∈ V, (z, v) ∈ K → z ∈ H)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V) {a b : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b) :
    ∃ z ∈ range γ ∩ H, (connectedComponentIn H z).Nontrivial := by
  by_contra! hn
  have hs : ∀ z ∈ range γ ∩ H, connectedComponentIn H z = {z} := by
    intro z hz
    exact (hn z hz).eq_singleton_of_mem
      (mem_connectedComponentIn hz.2)
  obtain ⟨δ, hδV, hδH⟩ := exists_path_avoiding_singleton_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hH hV hinfty hx hy γ hγV hs
  obtain ⟨z, hz, hzv⟩ := compact_band_crossing hK
    (isConnected_range δ.continuous).isPreconnected
    (fun z hz => hne z (hδV hz)) (fun z hz => hinterval z (hδV hz))
    ⟨0, δ.source⟩ ⟨1, δ.target⟩ ha hb hav hvb
  exact Set.disjoint_left.mp hδH hz (hlevel z (hδV hz) hzv)

theorem singleton_free_contacts_force_paid_level
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V Free Paid : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {K : Set (Sphere × ℝ)} (hK : IsCompact K)
    (hne : ∀ z ∈ V, {t : ℝ | (z, t) ∈ K}.Nonempty)
    (hinterval : ∀ z ∈ V, OrdConnected {t : ℝ | (z, t) ∈ K})
    {v : ℝ} (hlevel : ∀ z ∈ V, (z, v) ∈ K → z ∈ H)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V) {a b : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b)
    (hcover : range γ ∩ H ⊆ Free ∪ Paid)
    (hfree : ∀ z ∈ range γ ∩ H, z ∈ Free →
      ¬ (connectedComponentIn H z).Nontrivial) :
    (range γ ∩ H ∩ Paid).Nonempty := by
  obtain ⟨z, hz, hnt⟩ := exists_nonsingleton_band_contact hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hH hV hinfty hK hne hinterval
    hlevel hx hy γ hγV ha hb hav hvb
  rcases hcover hz with hf | hp
  · exact (hfree z hz hf hnt).elim
  · exact ⟨z, hz, hp⟩

end CircleDomainRigidity

end

end OAI
