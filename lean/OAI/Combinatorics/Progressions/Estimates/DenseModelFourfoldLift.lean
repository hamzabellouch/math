import OAI.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_model_with_fourfold_lift {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (I → ℤ)) (B : Finset (ZMod N))
      (f : (I → ℤ) → ZMod N) (L : ZMod N → (I → ℤ)),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧ A.card ≤ 16 * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ 16 * A.card ∧
      (32 * K ^ 16)⁻¹ ≤ (B.card : ℝ) / N ∧
      Set.MapsTo L (2 • B - 2 • B : Finset _) (2 • J - 2 • J : Finset _) ∧
      Set.InjOn L (2 • B - 2 • B : Finset _) ∧
      L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  classical
  obtain ⟨N, J, B, f, hN, hJ, hJA, hsize, hB, hBimage, hBcard, hf, hNsize, hdensity⟩ :=
    exists_dense_cyclic_model_of_integer_vectors A hA hK hsmall 8 (by decide)
  let g := Function.invFunOn f (J : Set (I → ℤ))
  have hg : IsAddFreimanIso 8 (B : Set (ZMod N)) (J : Set (I → ℤ)) g := hf.invFunOn
  let L := freimanFourfoldLift B hB g
  have hg4 : IsAddFreimanIso 4 (B : Set (ZMod N)) (J : Set (I → ℤ)) g :=
    hg.mono (hmn := by decide)
  have hmap : Set.MapsTo L (2 • B - 2 • B : Finset _) (2 • J - 2 • J : Finset _) := by
    intro x hx
    exact freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul hB hg.bijOn.mapsTo hx
  have hinj : Set.InjOn L (2 • B - 2 • B : Finset _) :=
    freimanFourfoldLift_injOn hB hg4
  have hzero : L 0 = 0 := by
    obtain ⟨b, hb⟩ := hB.exists_mem
    let p : FourfoldPresentation (ZMod N) := ⟨b, b, b, b⟩
    have hp : p.Mem B := ⟨hb, hb, hb, hb⟩
    have hpx : p.eval = 0 := by simp [p, FourfoldPresentation.eval]
    have hz : (0 : ZMod N) ∈ 2 • B - 2 • B :=
      mem_two_nsmul_sub_two_nsmul_iff.mpr ⟨p, hp, hpx⟩
    change freimanFourfoldLift B hB g 0 = 0
    rw [freimanFourfoldLift_eq_of_presentation hB hg4 hz hp hpx]
    simp [fourfoldMapValue, p]
  refine ⟨N, J, B, f, L, hN, hJ, hJA, ?_, hB, hBimage, hBcard, hf,
    ?_, ?_, hmap, hinj, hzero, ?_⟩
  · simpa only [Nat.reduceMul] using hsize
  · simpa only [Nat.reduceMul] using hNsize
  · norm_num at hdensity ⊢
    exact hdensity
  · intro x hx y hy z hz w hw
    exact freimanFourfoldLift_add_eq_add hB hg hx hy hz hw

end Erdos3.FreimanModel

end

end OAI
