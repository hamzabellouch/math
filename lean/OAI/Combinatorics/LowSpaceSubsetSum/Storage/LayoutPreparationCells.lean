import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LayoutSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalMixerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLayoutPreparation

namespace OAI

/-! # Executed canonical layout preparation and its retained arrays

The sampled permutation and sign mask remain live while the three mixer
counts and integer widths are prepared. The mixer preparation already
accounts for its shared arrays and merge state.
-/

noncomputable section
namespace LowSpaceSubsetSum.LayoutPreparationCells

variable {n : ℕ}

def assemble
    (layout : (Option (Vector (Fin n) n × IndexedMask n) × ℕ) × ℕ)
    (prepare : Vector (Fin n) n →
      ((Vector (List (Fin n)) 3 × MixerParameterExecution.Parameters) × ℕ) × ℕ) :
    (Option (RepresentationLayoutPreparation.Data n) × ℕ) × ℕ :=
  match layout.1.1 with
  | none => ((none, layout.1.2+1), layout.2+32)
  | some (v, signs) =>
    let prepared := prepare v
    ((some ⟨v, signs, prepared.1.1.1, prepared.1.1.2⟩, layout.1.2+prepared.1.2+1),
      layout.2+prepared.2+8*n+64)

def run (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.layoutCoupling.Seed) :
    (Option (RepresentationLayoutPreparation.Data n) × ℕ) × ℕ :=
  assemble (LayoutSamplerCells.run (canonicalRepresentationData I).zeroSetup s)
    (CanonicalMixerCells.prepare I)

theorem value (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.layoutCoupling.Seed) :
    (run I s).1 = RepresentationLayoutPreparation.run (canonicalRepresentationData I) s := by
  have h := LayoutSamplerCells.run_value (canonicalRepresentationData I).zeroSetup s
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [run, assemble, RepresentationLayoutPreparation.run, h₁, h₂]
  split <;> simp_all only [CanonicalMixerCells.prepare_value]

private theorem scalar_bound (n u C L P : ℕ) (hu : n+2 ≤ u) (hu0 : 10000 ≤ u)
    (hL : L ≤ u^6) (hP : P ≤ u^8*C) : L+P+8*n+64 ≤ u^10*(C+1) := by
  have h68 : u^6 ≤ u^8 := pow_le_pow_right' (by omega) (by decide)
  have hpoly : 8*n+64 ≤ u^8 := by
    have h2 : u^2 ≤ u^8 := pow_le_pow_right' (by omega) (by decide)
    nlinarith only [hu, hu0, h2]
  have hmajor : 3*u^8 ≤ u^10 := by
    have hcoef : 3 ≤ u^2 := by nlinarith only [hu0]
    calc
      _ ≤ u^2*u^8 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  have hL' := hL.trans (h68.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1)))
  have hp' := hP.trans (Nat.mul_le_mul_left (u^8) (show C ≤ C+1 by omega))
  have hsmall := hpoly.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1))
  have hfinal := Nat.mul_le_mul_right (C+1) hmajor
  simp only [Nat.mul_assoc] at hfinal
  omega

private theorem assemble_cells (u C : ℕ)
    (layout : (Option (Vector (Fin n) n × IndexedMask n) × ℕ) × ℕ)
    (prepare : Vector (Fin n) n →
      ((Vector (List (Fin n)) 3 × MixerParameterExecution.Parameters) × ℕ) × ℕ)
    (hu : n+2 ≤ u) (hu0 : 10000 ≤ u) (hL : layout.2 ≤ u^6)
    (hP : ∀ v, (prepare v).2 ≤ u^8*C) :
    (assemble layout prepare).2 ≤ u^10*(C+1) := by
  unfold assemble
  cases h : layout.1.1 with
  | none =>
    change layout.2+32 ≤ _
    have hs := scalar_bound n u C layout.2 0 hu hu0 hL (Nat.zero_le _)
    omega
  | some pair =>
    rcases pair with ⟨v, signs⟩
    exact scalar_bound n u C layout.2 (prepare v).2 hu hu0 hL (hP v)

private theorem raw_bound (n u : ℕ) (hu : n+1 ≤ u) (hu0 : 10000 ≤ u) :
    (n+1)*(3*n^3+128)+32*(n+1)^2 ≤ u^6 := by
  have hp3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have hp2 := Nat.pow_le_pow_left hu 2
  have hu3 : u ≤ u^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
  have ht : 3*n^3+128 ≤ 4*u^3 := by nlinarith only [hp3, hu3, hu0]
  have hm := Nat.mul_le_mul hu ht
  have hm' : (n+1)*(3*n^3+128) ≤ 4*u^4 := by convert hm using 1; ring
  have h24 : u^2 ≤ u^4 := pow_le_pow_right' (by omega) (by decide)
  have h46 : 36*u^4 ≤ u^6 := by
    have hcoef : 36 ≤ u^2 := by nlinarith only [hu0]
    calc
      _ ≤ u^2*u^4 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  nlinarith only [hm', hp2, h24, h46]

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (s : (canonicalRepresentationData I).zeroSetup.layoutCoupling.Seed) :
    (run I s).2 ≤ inputScale I^10*(compressionDictionaryCapacity n+1) := by
  apply assemble_cells (inputScale I) (compressionDictionaryCapacity n)
  · unfold inputScale; omega
  · unfold inputScale; omega
  · exact (LayoutSamplerCells.run_cells (canonicalRepresentationData I).zeroSetup s).trans
      (raw_bound n (inputScale I) (by unfold inputScale; omega) (by unfold inputScale; omega))
  · intro v
    exact CanonicalMixerCells.prepare_cells_capacity I v hn

end LowSpaceSubsetSum.LayoutPreparationCells

end

end OAI
