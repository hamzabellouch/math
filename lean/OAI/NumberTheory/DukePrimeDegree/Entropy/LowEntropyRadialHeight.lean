import OAI.NumberTheory.DukePrimeDegree.Geometry.ControlledRadialHeight
import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallHeightEntropy

namespace OAI

/-! # Controlled radial heights with arbitrarily small truncation entropy

Coarsening retains a subsequence of the radial thresholds, so their
uniform boundary estimate survives unchanged.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_low_entropy_controlled_radial_height {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ] (a : G n)
    (ha : MeasurePreserving (fun x => rightAction x a) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B D : ℝ) (t : ℕ → ℝ) (H : X n → ℕ),
      0 < B ∧ 0 ≤ D ∧ Measurable H ∧
      (∀ m, t m ≤ 2*B*(m:ℝ)+B) ∧
      (∀ x m, H x ≤ m ↔
        quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t m) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1) ∧
      (∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x=t m}=0) ∧
      (∀ m k, μ (realBoundaryStrip
        (quotientLogDistance (Quotient.mk _ (1 : G n))) (t m) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (D*(1/2:ℝ)^k)) ∧
      ∀ N, observationEntropyRate μ (fun x => rightAction x a) (heightClip H N) < ε := by
  obtain ⟨B,t,H,hB,_,hH,ht,hlevel,hcompact,hstep,hboundary⟩ :=
    exists_controlled_radial_height μ a
  obtain ⟨q,r,hq,hr,hent⟩ := exists_coarse_height_small_entropy μ ha H hH hstep hε
  let J : X n → ℕ := fun x => (H x+r)/q
  let idx : ℕ → ℕ := fun m => q*(m+1)-1-r
  let B' : ℝ := 2*B*q
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hj (x : X n) (m : ℕ) : J x ≤ m ↔ H x ≤ idx m := by
    have hqm : r < q*(m+1) := by nlinarith
    change (H x+r)/q ≤ m ↔ H x ≤ q*(m+1)-1-r
    rw [Nat.le_iff_lt_add_one,Nat.div_lt_iff_lt_mul hq,Nat.mul_comm (m+1) q]
    omega
  have hsets (m : ℕ) : {x | J x ≤ m}={x | H x ≤ idx m} :=
    Set.ext fun x => hj x m
  have hlev (x : X n) (m : ℕ) : J x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t (idx m) := by
    rw [hj]
    change x ∈ {x | H x ≤ idx m} ↔
      x ∈ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t (idx m)}
    rw [hlevel]
  refine ⟨B',16/B,(fun m => t (idx m)),J,hB',by positivity,
    (measurable_of_countable (fun k : ℕ => (k+r)/q)).comp hH,?_,hlev,?_,?_,
    (fun m => (hboundary (idx m)).1),(fun m k => (hboundary (idx m)).2 k),hent⟩
  · intro m
    have hidx : idx m+1 ≤ q*(m+1) := by
      dsimp only [idx]
      have hqm : 0 < q*(m+1) := by positivity
      omega
    have hcast : (idx m:ℝ)+1 ≤ (q:ℝ)*((m:ℝ)+1) := by exact_mod_cast hidx
    calc
      t (idx m) ≤ B*(2*(idx m:ℝ)+1) := (ht (idx m)).2.le
      _ ≤ B*(2*((q:ℝ)*((m:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ = B'*(m:ℝ)+B' := by dsimp [B']; ring
      _ ≤ 2*B'*(m:ℝ)+B' := by nlinarith [mul_nonneg hB'.le (Nat.cast_nonneg m)]
  · intro m
    rw [hsets]
    exact hcompact _
  · intro x
    have hs := hstep x
    constructor
    · calc
        _ ≤ (H x+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    · calc
        _ ≤ (H (rightAction x a)+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq

end DukePrimeDegree

end

end OAI
