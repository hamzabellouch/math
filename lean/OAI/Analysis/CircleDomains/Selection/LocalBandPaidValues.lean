import OAI.Analysis.CircleDomains.Selection.RealBandPaidValues

namespace OAI

/-! Local real branches may describe a globally defined closed circle level
without extending continuously through its cut. The topological crossing is
performed in that global level; real values are used only inside the branch
neighborhood. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem local_band_paid_values
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hav : a < v) (hvb : v < b) (hv : v ∈ Ico c (c + 1))
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ z ∈ range γ ∩ H (v : UnitAddCircle), z ∈ B \ Flags →
      ¬ (connectedComponentIn (H (v : UnitAddCircle)) z).Nontrivial) :
    v ∈ f '' (range γ ∩ D) ∨
      ∃ z ∈ range γ ∩ Flags, (z, v) ∈ intervalFiberHull (clusterGraph D f) := by
  have hxV : x ∈ V := hγV ⟨0, γ.source⟩
  have hyV : y ∈ V := hγV ⟨1, γ.target⟩
  have hai := hbranch x hxV a ((ha a).mpr rfl)
  have hbi := hbranch y hyV b ((hb b).mpr rfl)
  have hxH : x ∉ H (v : UnitAddCircle) := by
    intro hx
    obtain ⟨⟨z, t⟩, ht, he⟩ := (hlevel x hxV _).mpr hx
    change (z, (t : UnitAddCircle)) = (x, (v : UnitAddCircle)) at he
    have hz : z = x := congrArg Prod.fst he
    subst z
    have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hbranch x hxV t ht) hv).mp (congrArg Prod.snd he)
    exact hav.ne' (htv.symm.trans ((ha t).mp ht))
  have hyH : y ∉ H (v : UnitAddCircle) := by
    intro hy
    obtain ⟨⟨z, t⟩, ht, he⟩ := (hlevel y hyV _).mpr hy
    change (z, (t : UnitAddCircle)) = (y, (v : UnitAddCircle)) at he
    have hz : z = y := congrArg Prod.fst he
    subst z
    have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hbranch y hyV t ht) hv).mp (congrArg Prod.snd he)
    exact hvb.ne (htv.symm.trans ((hb t).mp ht))
  have hcl (z : Sphere) : z ∈ closure D := by rw [hdense.closure_eq]; trivial
  obtain ⟨z, hz, hp⟩ := singleton_free_contacts_force_paid_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad (hH _) hV hinfty
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM))
    (fun z _ => by
      obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z)
      exact ⟨t, subset_intervalFiberHull _ ht⟩)
    (fun z _ => by
      rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) z
        (clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z))]
      exact ordConnected_Icc)
    (fun z hz ht => (hlevel z hz _).mp ⟨(z, v), ht, rfl⟩)
    hxH hyH γ hγV ((ha a).mpr rfl) ((hb b).mpr rfl) hav.le hvb.le
    (Free := B \ Flags) (Paid := D ∪ Flags)
    (by
      intro z _
      by_cases hzB : z ∈ B
      · by_cases hzF : z ∈ Flags
        · exact Or.inr (Or.inr hzF)
        · exact Or.inl ⟨hzB, hzF⟩
      · exact Or.inr (Or.inl (hBD hzB))) hfree
  obtain ⟨⟨w, t⟩, ht, he⟩ := (hlevel z (hγV hz.1) _).mpr hz.2
  change (w, (t : UnitAddCircle)) = (z, (v : UnitAddCircle)) at he
  have hw : w = z := congrArg Prod.fst he
  subst w
  have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hbranch z (hγV hz.1) t ht) hv).mp (congrArg Prod.snd he)
  subst t
  rcases hp with hzD | hzF
  · have hcont : ContinuousAt f z := hf.continuousAt ((hD.inter hV).mem_nhds ⟨hzD, hγV hz.1⟩)
    obtain ⟨r, s, q, hr, hs, _, heq⟩ := mem_intervalFiberHull_iff.mp ht
    rw [clusterGraph_fiber_eq_of_continuousAt hcont hr,
      clusterGraph_fiber_eq_of_continuousAt hcont hs] at heq
    exact Or.inl ⟨z, ⟨hz.1, hzD⟩, by nlinarith [heq]⟩
  · exact Or.inr ⟨z, ⟨hz.1, hzF⟩, ht⟩

end CircleDomainRigidity

end

end OAI
