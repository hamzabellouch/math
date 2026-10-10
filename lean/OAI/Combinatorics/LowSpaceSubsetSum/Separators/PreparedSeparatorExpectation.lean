import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorContext
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerCoupling

namespace OAI

/-! # The measured checker under the actual independent family law

The ideal subset draws are identified with their stored bit codes. Decoding
these codes preserves every sampled occurrence, so the existing scan
expectation applies to the measured checker without changing its law.
-/

noncomputable section

namespace LowSpaceSubsetSum.PreparedSeparatorExpectation

open SeparatorExpectation RepresentationMoments

variable {n g : ℕ} (S : RoundedParameters g)

private instance sampleNonempty (i : Fin 4) :
    Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i)) :=
  ⟨⟨initialSubset g (S.e i) (S.size_le i),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, initialSubset_card _ _ _⟩⟩⟩

def codes (draws : IndependentFamilies g S.e S.counts) : Fin 4 → Array (Fin (2 ^ g)) :=
  fun i => (familyArrays draws i).map SeparatorStoredMasks.code

theorem codes_size (draws : IndependentFamilies g S.e S.counts) (i : Fin 4) :
    (codes S draws i).size ≤ 11 * 2 ^ g := by
  simpa only [codes, familyArrays, Array.size_map, Array.size_ofFn] using S.counts_le i

theorem codes_decode (draws : IndependentFamilies g S.e S.counts) :
    (fun i => (codes S draws i).map SeparatorStoredMasks.decode) = familyArrays draws := by
  funext i
  simp only [codes, Array.map_map]
  have h : SeparatorStoredMasks.decode ∘ SeparatorStoredMasks.code =
      (id : Finset (Fin g) → Finset (Fin g)) := by
    funext a
    exact SeparatorStoredMasks.decode_code a
  rw [h, Array.map_id]

def prepare (rows : Fin 4 → Vector (Fin n) g)
    (draws : IndependentFamilies g S.e S.counts) : List (StoredSeparatorCheck.Block n g) × ℕ :=
  PreparedSeparatorContext.prepare rows (codes S draws) (codes_size S draws)

def check (rows : Fin 4 → Vector (Fin n) g)
    (draws : IndependentFamilies g S.e S.counts)
    (capacity : ℕ) (target : ℤ) (xs ys : List (StoredEntry n)) : Bool × ℕ :=
  StoredSeparatorCheck.run capacity target (prepare S rows draws).1 xs ys

theorem acceptance (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (draws : IndependentFamilies g S.e S.counts)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (check S rows draws capacity target xs ys).1 =
      (C.check (familyArrays draws) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).accepted := by
  have h := PreparedSeparatorContext.acceptance C rows hrows (codes S draws)
    (codes_size S draws) capacity hcap target xs ys
  rw [codes_decode] at h
  exact h

theorem check_work (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (draws : IndependentFamilies g S.e S.counts)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (check S rows draws capacity target xs ys).2 ≤ inputScale I ^ 4 *
      ((C.check (familyArrays draws) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).scans +
        xs.length + ys.length + 1) := by
  have h := PreparedSeparatorContext.run_work I hn hg C rows hrows (codes S draws)
    (codes_size S draws) capacity hcap target xs ys
  rw [codes_decode] at h
  exact h

theorem prepare_work (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (draws : IndependentFamilies g S.e S.counts) :
    (prepare S rows draws).2 ≤ inputScale I ^ 2 * C :=
  PreparedSeparatorContext.prepare_work_scale I hn hg C hC rows (codes S draws)
    (codes_size S draws)

theorem mean_check_work (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n))
    (hleft : ∀ x ∈ xs, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry x.semantic).mask).card = S.c i)
    (hright : ∀ y ∈ ys, ∀ i,
      (SeparatorCheck.localMask i (C.encodeEntry y.semantic).mask).card = g / 2 - S.c i) :
    mean (fun draws : IndependentFamilies g S.e S.counts =>
      ((check S rows draws capacity target xs ys).2 : ℝ)) ≤
      (inputScale I : ℝ) ^ 4 *
        (((xs.length + ys.length : ℕ) : ℝ) * (inputScale I : ℝ) ^ 22 *
          (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4))) +
          ((xs.length + ys.length : ℕ) : ℝ) + 1) := by
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hscan := C.mean_scans_polynomial S (inputScale I) (by omega) (by omega) (by omega)
    target (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)
    (by
      intro x hx i
      obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hx
      exact hleft x hxMem i)
    (by
      intro y hy i
      obtain ⟨y, hyMem, rfl⟩ := List.mem_map.mp hy
      exact hright y hyMem i)
  simp only [List.length_map] at hscan
  have hpoint (draws : IndependentFamilies g S.e S.counts) :
      ((check S rows draws capacity target xs ys).2 : ℝ) ≤
        (inputScale I : ℝ) ^ 4 *
          (((C.check (familyArrays draws) target
            (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).scans : ℝ) +
            ((xs.length + ys.length : ℕ) : ℝ) + 1) := by
    have hw := check_work S I hn hg C rows hrows draws capacity hcap target xs ys
    simp only [Nat.add_assoc] at hw
    exact_mod_cast hw
  have hm := mean_mono hpoint
  simp_rw [mean_mul_left, mean_add, mean_const] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end LowSpaceSubsetSum.PreparedSeparatorExpectation

end

end OAI
