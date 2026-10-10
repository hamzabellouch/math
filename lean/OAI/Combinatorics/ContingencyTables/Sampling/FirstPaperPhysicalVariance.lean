import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFullVariance
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileEncoding

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PhysicalStates (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {z : Profiles small B // 0 < hardMarginal small B r c L (naturalProfile z.val)}

noncomputable instance physicalStatesFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (PhysicalStates small B r c L) := by
  unfold PhysicalStates
  infer_instance

noncomputable def physicalProfile (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) : SmallProfile small :=
  naturalProfile z.val.val

lemma physicalProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    Function.Injective (physicalProfile small B r c L) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact naturalProfile_injective small B h

noncomputable def physicalExtension (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (H : PhysicalStates small B r c L → ℝ) : SmallProfile small → ℝ :=
  Function.extend (physicalProfile small B r c L) H (fun _ => 0)

lemma physicalExtension_at (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (H : PhysicalStates small B r c L → ℝ)
    (z : PhysicalStates small B r c L) :
    physicalExtension small B r c L H (physicalProfile small B r c L z)=H z :=
  (physicalProfile_injective small B r c L).extend_apply H (fun _ => 0) z

/-- Zero-weight bounded profiles can be removed before applying the
full graph estimate, so this quantifies over every observable on the
actual positive-weight state space. -/
theorem firstPaper_physical_variance (r : I → ℕ) (c : J → ℕ) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let L := d^12
    let small := paperSmall r c
    let B := paperCapacity small r d L U
    let hB := fun i j (hij : small i j=true) => show B i j=U by simp only [B,paperCapacity,hij,ite_true]
    ∀ H : PhysicalStates small B r c L → ℝ,
      variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
        770*(d:ℝ)^4*(U:ℝ)^6*
          fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := paperCapacity small r d L U
  have hB : ∀ i j,small i j=true → B i j=U := fun i j hij => by simp only [B,paperCapacity,hij,ite_true]
  intro H
  let G := physicalExtension small B r c L H
  have hext : ∀ z : PhysicalStates small B r c L,G (naturalProfile z.val.val)=H z :=
    physicalExtension_at small B r c L H
  have hv := variance_positive_support
    (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
    (fun z => G (naturalProfile z.val)) (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hv' : variance (fun z : PhysicalStates small B r c L =>
      hardMarginal small B r c L (physicalProfile small B r c L z)) H =
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => G (naturalProfile z.val)) := by
    simpa only [physicalProfile,hext] using hv
  rw [hv',← encoding_variance_eq small B r c L U hB G]
  exact firstPaper_full_variance r c G

end ContingencyTables.SmallGraphProfiles

end OAI
