import OAI.Analysis.CircleDomains.Selection.SingletonBandCrossing

namespace OAI

/-! Actual real-coordinate band levels satisfy the paid-threshold
conclusion used in the local variation argument. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_band_paid_threshold
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hab : b - a < 1) (hav : a < v) (hvb : v < b)
    (hfree : ∀ z ∈ range γ ∩ {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f},
      z ∈ B \ Flags →
      ¬ (connectedComponentIn {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f} z).Nontrivial) :
    ∃ z ∈ range γ, (z ∈ D ∨ z ∈ Flags) ∧
      (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f := by
  let H := {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f}
  have hva : (v : AddCircle (1 : ℝ)) ≠ (a : AddCircle (1 : ℝ)) := by
    intro he
    have hvi : v ∈ Ico a (a + 1) := ⟨hav.le, by linarith⟩
    have hai : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
    exact hav.ne' ((AddCircle.coe_eq_coe_iff_of_mem_Ico hvi hai).mp he)
  have hvb' : (v : AddCircle (1 : ℝ)) ≠ (b : AddCircle (1 : ℝ)) := by
    intro he
    have hvi : v ∈ Ico a (a + 1) := ⟨hav.le, by linarith⟩
    have hbi : b ∈ Ico a (a + 1) := ⟨by linarith, by linarith⟩
    exact hvb.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hvi hbi).mp he)
  have hxH : x ∉ H := by
    rintro ⟨⟨z, t⟩, ht, he⟩
    change (z, (t : AddCircle (1 : ℝ))) = (x, (v : AddCircle (1 : ℝ))) at he
    have hz : z = x := congrArg Prod.fst he
    have htEq : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
    subst z
    exact hva (htEq.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) ((ha t).mp ht)))
  have hyH : y ∉ H := by
    rintro ⟨⟨z, t⟩, ht, he⟩
    change (z, (t : AddCircle (1 : ℝ))) = (y, (v : AddCircle (1 : ℝ))) at he
    have hz : z = y := congrArg Prod.fst he
    have htEq : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
    subst z
    exact hvb' (htEq.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) ((hb t).mp ht)))
  have hcl (z : Sphere) : z ∈ closure D := by rw [hdense.closure_eq]; trivial
  obtain ⟨z, hz, hp⟩ := singleton_free_contacts_force_paid_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad
    (isCompact_circleBandLevel hM (v : AddCircle (1 : ℝ))).isClosed hV hinfty
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM))
    (fun z _ => by
      obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z)
      exact ⟨t, subset_intervalFiberHull _ ht⟩)
    (fun z _ => by
      rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) z
        (clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z))]
      exact ordConnected_Icc)
    (fun z _ hz => ⟨(z, v), hz, rfl⟩)
    hxH hyH γ hγV ((ha a).mpr rfl) ((hb b).mpr rfl) hav.le hvb.le
    (Free := B \ Flags) (Paid := D ∪ Flags)
    (by
      intro z _
      by_cases hzB : z ∈ B
      · by_cases hzF : z ∈ Flags
        · exact Or.inr (Or.inr hzF)
        · exact Or.inl ⟨hzB, hzF⟩
      · exact Or.inr (Or.inl (hBD hzB))) hfree
  exact ⟨z, hz.1, hp, hz.2⟩

end CircleDomainRigidity

end

end OAI
