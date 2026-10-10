import OAI.Analysis.CircleDomains.Topology.GraphFillingDisks
import OAI.Analysis.CircleDomains.Topology.SubordinateFillingDisks

namespace OAI

/-! Closed real and period level graphs supply filling contours which
also remain inside the required local real-branch neighborhoods. -/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_subordinate_filling_disks_of_compatible_graphs
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {n N : ℕ} {P S : Type*} (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (pairs : P → Fin n × Fin n)
    (hpairs : ∀ i j : Fin n, i ≠ j → ∃ p, pairs p = (i, j) ∨ pairs p = (j, i))
    (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    {B A W : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (hnoterm : Disjoint A (σ '' gridTerminalIndices F (reciprocalGridStep N) pairs a b θ))
    (hfree : ∀ x ∈ A, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N A σ)
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j : Fin n, j.val ≠ k →
          Disjoint (frontier (jordanInterior (H i)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R j) (θ j) N l))) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  let L : Fin n → Set Sphere := fun j => ⋃ k, reciprocalGraphLevel (R j) (θ j) N k
  let J : ℕ → Set Sphere := fun j => if hj : j < n then L ⟨j, hj⟩ else ∅
  have hJ (j : ℕ) : IsClosed (J j) := by
    by_cases hj : j < n
    · simpa only [J, dite_eq_left hj] using
        (isClosed_iUnion_of_finite (fun k =>
          isClosed_reciprocalGraphLevel (hR ⟨j, hj⟩) (θ ⟨j, hj⟩) N k))
    · simp only [J, dite_eq_right hj, isClosed_empty]
  have hlower (j : Fin n) : (⋃ k ∈ Finset.range j.val, J k) =
      ⋃ i : Fin n, ⋃ (_ : i.val < j.val), L i := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
      have hkj := Finset.mem_range.mp hk
      have hkn := hkj.trans j.isLt
      exact mem_iUnion₂.mpr ⟨⟨k, hkn⟩, hkj, by simpa only [J, dite_eq_left hkn] using hx⟩
    · intro hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i.val, Finset.mem_range.mpr hi,
        by simpa only [J, dite_eq_left i.isLt] using hx⟩
  have hsingle (j : ℕ) (hj : j < n) (x : Sphere) (hx : x ∈ A ∩ J j) :
      connectedComponentIn (B ∪ ⋃ k ∈ Finset.range j, J k) x = {x} := by
    rw [hlower ⟨j, hj⟩]
    apply lower_obstacle_singleton_of_compatible_graphs R hR σ a b θ pairs
      hpairs F hband hB hTD hAB hnoterm hfree hcompat ⟨j, hj⟩
    simpa only [J, dite_eq_left hj] using hx
  obtain ⟨m, H, γ, hc, hd, hcurves⟩ := exists_subordinate_finite_filling_disks hsard hschoenflies
    G π hπ hclosed hsurj hr hB hTD J hJ hbad n hA hAB hBA hW hAW hinfty hsingle Nbh hNbh haNbh
  refine ⟨m, H, γ, hc, hd, ?_⟩
  intro i
  obtain ⟨hi, hsm, hemb, hfront, hb, ⟨k, hk⟩, ha⟩ := hcurves i
  refine ⟨hi, hsm, hemb, hfront, hb, ⟨k, ?_⟩, ha⟩
  intro j hj
  simpa only [J, dite_eq_left j.isLt] using hk j.val j.isLt hj

end CircleDomainRigidity.FiniteTransfer

end OAI
