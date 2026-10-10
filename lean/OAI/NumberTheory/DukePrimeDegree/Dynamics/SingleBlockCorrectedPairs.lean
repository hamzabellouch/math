import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockClosure
import OAI.NumberTheory.DukePrimeDegree.Geometry.CorrectedPairLimits
import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericMatrixPairs
import OAI.NumberTheory.DukePrimeDegree.Geometry.CompactCorrectionPatches

namespace OAI

/-!
# Normalized generic pairs from null block orbits

The small return matrices, their within-block normalizations and the
common compact corrections are selected in this proof. The correction
group is the closure of the single root block, so it preserves the same
component measure. The conclusion does not assume genericity of the
normalized points or a transverse limiting element.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def singleBlockClosureGroup {n : ℕ} (S : Set (Fin n)) :=
  (singleBlockRootGroup S).topologicalClosure

attribute [local irreducible] singleBlockRootGroup blockMatrixGroup singleBlockClosureGroup

theorem exists_singleBlock_corrected_generic_pairs {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : singleBlockRootGroup (↑S) ≤ invariantRightSubgroup μ)
    (ρ : Measure (singleBlockClosureGroup (n := n) (↑S))) [SFinite ρ] [ρ.IsMulLeftInvariant]
    (K₀ K₁ : Set (singleBlockClosureGroup (n := n) (↑S))) (hK₀ : IsCompact K₀) (hK : K₀ ⊆ K₁)
    (W : Set (singleBlockClosureGroup (n := n) (↑S))) (hW : IsOpen W) (h1W : 1 ∈ W)
    (hpatch : ∀ b ∈ W, ∀ u ∈ K₀, b * u ∈ K₁)
    (G₀ : Set (X n)) (hG₀ : MeasurableSet G₀)
    (t : ℝ≥0∞) (ht : t ≠ 0) (httop : t ≠ ⊤)
    (hsize : t + t < ρ K₀) (hbudget : (ρ K₁ * μ G₀ᶜ) / t < 1)
    (hnull : ∀ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (↑S))))) = 0) :
    ∃ (p q : ℕ → X n) (g : ℕ → G n) (c : ℕ → ℝ),
      Tendsto g atTop (𝓝 1) ∧
      (∀ k, q k = rightAction (p k) (g k) ∧
        g k ∉ blockMatrixGroup (blockComplementSetoid (↑S))) ∧
      (∀ᶠ k in atTop, p k ∈ G₀ ∧ q k ∈ G₀) ∧
      ∀ᶠ k in atTop,
        (∀ i ∈ S, (g k).val i i = c k) ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0 := by
  classical
  let H : Subgroup (G n) := singleBlockClosureGroup (n := n) (↑S)
  let B : Subgroup (G n) := blockMatrixGroup (blockComplementSetoid (↑S))
  have hHμ : H ≤ invariantRightSubgroup μ := by
    simpa only [H, singleBlockClosureGroup] using
      singleBlock_closure_le_stabilizer (S : Set (Fin n)) μ hH
  have hHB : H ≤ B := by
    simpa only [H, B, singleBlockClosureGroup] using
      singleBlock_closure_le_blockComplement (S : Set (Fin n))
  obtain ⟨E, _hE, hEpos, hEfiber⟩ := exists_positive_goodOrbitFiber_set μ ρ
    (fun x u => rightAction x (u : G n))
    (measurable_rightAction_subgroup_uncurry H)
    (fun u => ⟨(continuous_rightAction u.val).measurable, hHμ u.property⟩)
    K₁ G₀ hG₀ t ht httop hbudget
  obtain ⟨x, hx, a, ha, haE⟩ := exists_small_matrix_generic_pairs B μ E hEpos hnull
  obtain ⟨s, b, c, _hs, hb, he, hbH, _hc, hpart⟩ :=
    exists_singleBlock_transverse_sequence S hS a ha
  let β : ℕ → H := fun k => ⟨b k, by
    simpa only [H, singleBlockClosureGroup] using
      (singleBlockRootGroup (S : Set (Fin n))).le_topologicalClosure (hbH k)⟩
  have hβ : Tendsto β atTop (𝓝 (1 : H)) := by
    apply tendsto_subtype_rng.mpr
    exact hb
  have hβpatch : ∀ᶠ k in atTop, ∀ u ∈ K₀, β k * u ∈ K₁ :=
    eventually_maps_compact_correction_patch β hβ W K₀ K₁ hW h1W hpatch
  have hK₀ne : K₀.Nonempty := by
    by_contra hnone
    have hempty : K₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
    rw [hempty, measure_empty] at hsize
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ t + t from zero_le)) hsize
  obtain ⟨u₀, hu₀⟩ := hK₀ne
  have hchoose (k : ℕ) : ∃ u ∈ K₀,
      (∀ v ∈ K₀, β k * v ∈ K₁) →
        rightAction x u.val ∈ G₀ ∧ rightAction (rightAction x (a k)) ((β k * u).val) ∈ G₀ := by
    by_cases hk : ∀ v ∈ K₀, β k * v ∈ K₁
    · obtain ⟨u, hu, hux, huy⟩ := exists_common_goodOrbit_correction ρ
        (fun y v => rightAction y (v : G n))
        (fun y => ((continuous_rightAction_uncurry n).comp
          (continuous_const.prodMk continuous_subtype_val)).measurable)
        K₀ K₁ hK G₀ hG₀ x (rightAction x (a k)) (β k) hk
        ((add_le_add (hEfiber x hx).le (hEfiber _ (haE k).2).le).trans_lt hsize)
      exact ⟨u, hu, fun _ => ⟨hux, huy⟩⟩
    · exact ⟨u₀, hu₀, fun hp => (hk hp).elim⟩
  choose u hu hugood using hchoose
  obtain ⟨_u, _hu, φ, hφ, _hp, _hq, hrelative⟩ :=
    exists_common_corrected_pair_limit H K₀ hK₀ u hu a b ha hb x
  let p (k : ℕ) := rightAction x (u (φ k) : G n)
  let q (k : ℕ) := rightAction x (a (φ k) * b (φ k) * (u (φ k) : G n))
  let g (k : ℕ) := (u (φ k) : G n)⁻¹ * (a (φ k) * b (φ k)) * (u (φ k) : G n)
  refine ⟨p, q, g, c ∘ φ, hrelative, ?_, ?_, ?_⟩
  · intro k
    constructor
    · dsimp only [p, q, g]
      simp only [rightAction_mul]
      congr 1
      group
    · intro hg
      have hab : a (φ k) * b (φ k) ∈ B := by
        have hh := B.mul_mem (B.mul_mem (hHB (u (φ k)).property) hg)
          (B.inv_mem (hHB (u (φ k)).property))
        convert hh using 1
        dsimp only [g]
        group
      exact (haE (φ k)).1 (by
        have hh := B.mul_mem hab (B.inv_mem (hHB (β (φ k)).property))
        simpa only [β, Subgroup.coe_mk, mul_inv_cancel_right] using hh)
  · filter_upwards [hφ.tendsto_atTop.eventually hβpatch] with k hk
    obtain ⟨hpx, hqx⟩ := hugood (φ k) hk
    refine ⟨hpx, ?_⟩
    simpa only [q, β, Subgroup.coe_mul, Subgroup.coe_mk, rightAction_mul, mul_assoc] using hqx
  · filter_upwards [hφ.tendsto_atTop.eventually hpart] with k hk
    have hnormalized := withinBlockPart_singleBlock_closure_conjugation (↑S)
      (s (φ k)) (c (φ k)) hk.1 hk.2 (u (φ k) : G n)⁻¹
      (by simpa only [H, singleBlockClosureGroup] using H.inv_mem (u (φ k)).property)
    have heq : withinBlockPart (blockComplementSetoid (↑S)) (g k).val =
        withinBlockPart (blockComplementSetoid (↑S)) (s (φ k)).val := by
      simpa only [g, he, inv_inv] using hnormalized
    constructor
    · intro i hi
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) heq
      simpa only [withinBlockPart, Setoid.refl, ite_true, hk.1 i hi,
        Function.comp_apply] using ht
    · intro i hi j hj hij
      have hr : blockComplementSetoid (↑S) i j := ⟨fun _ => hj, fun _ => hi⟩
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) heq
      simpa only [withinBlockPart, hr, ite_true, hk.2 i hi j hj hij] using ht

end DukePrimeDegree

end

end OAI
