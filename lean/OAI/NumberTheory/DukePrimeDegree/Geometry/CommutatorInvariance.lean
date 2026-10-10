import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCommutator
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafNullClosure

namespace OAI

/-!
# Invariance under a commutator root

Two nonatomic adjacent root conditionals force invariance under the long
root. This proves EKL (2006), Lemma 3.3 / Einsiedler–Katok (2003), Lemma 6.1,
for the arithmetic quotient. Every vertex is selected outside a common
leafwise saturated null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_nonzero_parameter_of_ae
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hunit : ν (Metric.ball 0 1) = 1) {P : ℝ → Prop} (hP : ∀ᵐ t ∂ν, P t) :
    ∃ t, t ≠ 0 ∧ P t := by
  let : NeZero ν := ⟨by
    intro h
    have he := congrArg (fun μ : Measure ℝ => μ (Metric.ball 0 1)) h
    rw [hunit] at he
    simp at he⟩
  have hn : ∀ᵐ t ∂ν, t ≠ 0 := by rw [ae_iff]; simp
  exact (hn.and hP).exists

theorem root_invariant_of_adjacent_nonatomic_leaves
    (d : ℕ) {a b c : Fin (d + 1)} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hatom_ab : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hab μ x))
    (hatom_bc : ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hbc μ x)) :
    ∀ t : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hac t)) = μ := by
  by_contra hnot
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree (i j : Fin (d + 1)) (hij : i ≠ j) : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hQ : ∀ᵐ x ∂μ,
      NullSingletonClass (intrinsicRootLeaf hab μ x) ∧
      NullSingletonClass (intrinsicRootLeaf hbc μ x) ∧
      intrinsicRootLeaf hab μ x (Metric.ball 0 1) = 1 ∧
      intrinsicRootLeaf hbc μ x (Metric.ball 0 1) = 1 ∧
      ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hac μ x) t =
        intrinsicRootLeaf hac μ x → t = 0 := by
    filter_upwards [hatom_ab, hatom_bc, ae_intrinsicRootLeaf_spec hab μ (hfree a b hab),
      ae_intrinsicRootLeaf_spec hbc μ (hfree b c hbc),
      ae_based_rootLeaf_eq_only_at_zero d hac μ hnot] with x ha hb hsa hsb hs
    exact ⟨ha, hb, hsa.2, hsb.2, hs⟩
  obtain ⟨N5, hbad, hN5, hz5⟩ := exists_measurable_superset_of_null (ae_iff.mp hQ)
  have hf1 : ¬ (a = a ∧ b = c) := by tauto
  have hb1 : ¬ (a = c ∧ b = a) := by tauto
  obtain ⟨N1, hN1, hz1, hconst1⟩ :=
    exists_nullset_nonparallel_root_constancy d hac hab hf1 hb1 μ hA
  have hf2 : ¬ (b = a ∧ c = c) := by tauto
  have hb2 : ¬ (b = c ∧ c = a) := by tauto
  obtain ⟨N2, hN2, hz2, hconst2⟩ :=
    exists_nullset_nonparallel_root_constancy d hac hbc hf2 hb2 μ hA
  have hf3 : ¬ (a = b ∧ b = c) := by tauto
  have hb3 : ¬ (a = c ∧ b = b) := by tauto
  obtain ⟨N3, hN3, hz3, hconst3⟩ :=
    exists_nullset_nonparallel_root_constancy d hbc hab hf3 hb3 μ hA
  obtain ⟨ell, hell, hn, hw⟩ := exists_neutral_expanding_weights d hac hab hf1 hb1
  obtain ⟨N4, hN4, hz4, hhol⟩ := exists_nullset_neutral_root_holonomy d hac μ hA ell hell hn
  let B := N1 ∪ (N2 ∪ (N3 ∪ (N4 ∪ N5)))
  have hB : MeasurableSet B := hN1.union (hN2.union (hN3.union (hN4.union hN5)))
  have hBzero : μ B = 0 := measure_union_null hz1
    (measure_union_null hz2 (measure_union_null hz3 (measure_union_null hz4 hz5)))
  obtain ⟨M, hM, hMzero, hBM, hleaf⟩ := enlarge_nullset_all_roots d μ hA B hB hBzero
  have hout (w : X (d + 1)) (hwM : w ∉ M) :
      w ∉ N1 ∧ w ∉ N2 ∧ w ∉ N3 ∧ w ∉ N4 ∧ w ∉ N5 := by
    have hb : w ∉ B := fun h => hwM (hBM h)
    simpa only [B, mem_union, not_or] using hb
  have hgood (w : X (d + 1)) (hwM : w ∉ M) :
      NullSingletonClass (intrinsicRootLeaf hab μ w) ∧
      NullSingletonClass (intrinsicRootLeaf hbc μ w) ∧
      intrinsicRootLeaf hab μ w (Metric.ball 0 1) = 1 ∧
      intrinsicRootLeaf hbc μ w (Metric.ball 0 1) = 1 ∧
      ∀ t : ℝ, basedRealMeasure (intrinsicRootLeaf hac μ w) t =
        intrinsicRootLeaf hac μ w → t = 0 := by
    by_contra h
    exact (hout w hwM).2.2.2.2 (hbad h)
  have hae : ∀ᵐ z ∂μ, z ∉ M := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hMzero
  obtain ⟨z, hz⟩ := hae.exists
  let : NullSingletonClass (intrinsicRootLeaf hab μ z) := (hgood z hz).1
  let : NullSingletonClass (intrinsicRootLeaf hbc μ z) := (hgood z hz).2.1
  obtain ⟨r, hr, hzr⟩ := exists_nonzero_parameter_of_ae (intrinsicRootLeaf hab μ z)
    (hgood z hz).2.2.1 (hleaf z hz a b hab)
  let z' := rightAction z (Matrix.SpecialLinearGroup.transvection hab r)
  have hbcEq : intrinsicRootLeaf hbc μ z' = intrinsicRootLeaf hbc μ z :=
    hconst3 z (hout z hz).2.2.1 r (hout z' hzr).2.2.1
  have hs' : ∀ᵐ s ∂intrinsicRootLeaf hbc μ z,
      rightAction z' (Matrix.SpecialLinearGroup.transvection hbc s) ∉ M := by
    rw [← hbcEq]
    exact hleaf z' hzr b c hbc
  obtain ⟨s, hs, hx, hy⟩ := exists_nonzero_parameter_of_ae (intrinsicRootLeaf hbc μ z)
    (hgood z hz).2.2.2.1 ((hleaf z hz b c hbc).and hs')
  let x := rightAction z (Matrix.SpecialLinearGroup.transvection hbc s)
  let y := rightAction z' (Matrix.SpecialLinearGroup.transvection hbc s)
  let g := Matrix.SpecialLinearGroup.transvection hbc (-s) *
    Matrix.SpecialLinearGroup.transvection hab r * Matrix.SpecialLinearGroup.transvection hbc s
  have hxy : rightAction x g = y := by
    dsimp only [x, y, z', g]
    simp only [rightAction_mul]
    congr 1
    rw [← Matrix.SpecialLinearGroup.transvection_inv hbc s]
    group
  have heq : intrinsicRootLeaf hac μ y = intrinsicRootLeaf hac μ x := by
    calc
      intrinsicRootLeaf hac μ y = intrinsicRootLeaf hac μ z' :=
        hconst2 z' (hout z' hzr).2.1 s (hout y hy).2.1
      _ = intrinsicRootLeaf hac μ z := hconst1 z (hout z hz).1 r (hout z' hzr).1
      _ = intrinsicRootLeaf hac μ x := (hconst2 z (hout z hz).2.1 s (hout x hx).2.1).symm
  have hh := hhol x (hout x hx).2.2.2.1 y (hout y hy).2.2.2.1 g hxy (r * s)
    (adjacent_root_conjugate_limit hab hbc hac ell hell hn (by linarith) r s)
  have he : r * s = 0 := (hgood x hx).2.2.2.2 (r * s) (hh.symm.trans heq)
  exact mul_ne_zero hr hs he

end DukePrimeDegree

end

end OAI
