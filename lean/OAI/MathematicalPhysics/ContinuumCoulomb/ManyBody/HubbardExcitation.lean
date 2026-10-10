import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardSpin
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ChargeTransfer

namespace OAI

/-! Actual occupation-diagonal inverse and charge-selection rules. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def fockDiagonal (f : Finset (Fin (Q + 1)) → ℂ) : Module.End ℂ (Space Q) :=
  (fockBasis Q).constr ℂ (fun A => f A • fockBasis Q A)

theorem fockDiagonal_basis (f : Finset (Fin (Q + 1)) → ℂ)
    (A : Finset (Fin (Q + 1))) :
    fockDiagonal f (fockBasis Q A) = f A • fockBasis Q A :=
  (fockBasis Q).constr_basis ℂ _ A

theorem fockDiagonal_coordinate (f : Finset (Fin (Q + 1)) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q + 1))) :
    (fockBasis Q).repr (fockDiagonal f x) A = f A * (fockBasis Q).repr x A := by
  have h : ((fockBasis Q).coord A).comp (fockDiagonal f) =
      f A • (fockBasis Q).coord A := by
    apply (fockBasis Q).ext
    intro S
    change (fockBasis Q).repr (fockDiagonal f (fockBasis Q S)) A =
      f A * (fockBasis Q).repr (fockBasis Q S) A
    rw [fockDiagonal_basis, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hSA : S = A
    · subst S
      simp
    · simp [Module.Basis.repr_self, hSA]
  exact LinearMap.congr_fun h x

def siteNumber (m : ℕ) (i : Fin (m + 1)) : Module.End ℂ (Space (2 * m + 1)) :=
  number (siteMode m i 0) + number (siteMode m i 1)

def occupationAt (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) (i : Fin (m + 1)) : Fin 3 :=
  ⟨(if siteMode m i 0 ∈ A then 1 else 0) + (if siteMode m i 1 ∈ A then 1 else 0),
    by split_ifs <;> omega⟩

theorem siteNumber_basis (m : ℕ) (i : Fin (m + 1))
    (A : Finset (Fin ((2 * m + 1) + 1))) :
    siteNumber m i (fockBasis (2 * m + 1) A) =
      ((occupationAt m A i : ℕ) : ℂ) • fockBasis (2 * m + 1) A := by
  simp only [siteNumber, LinearMap.add_apply, number_basis, occupationAt]
  split_ifs <;> simp [two_smul]

theorem siteNumber_eq_diagonal (m : ℕ) (i : Fin (m + 1)) :
    siteNumber m i = fockDiagonal (fun A => ((occupationAt m A i : ℕ) : ℂ)) := by
  apply (fockBasis (2 * m + 1)).ext
  intro A
  rw [siteNumber_basis, fockDiagonal_basis]

theorem numberEigen_coordinate_zero (m : ℕ) (i : Fin (m + 1))
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m i x = η • x)
    (A : Finset (Fin ((2 * m + 1) + 1)))
    (hne : ((occupationAt m A i : ℕ) : ℂ) ≠ η) :
    (fockBasis (2 * m + 1)).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis (2 * m + 1)).repr y A) hx
  rw [siteNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hz : (((occupationAt m A i : ℕ) : ℂ) - η) *
      (fockBasis (2 * m + 1)).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

def occupationDiagonal (m : ℕ) (f : (Fin (m + 1) → Fin 3) → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) := fockDiagonal (fun A => f (occupationAt m A))

/-- A joint local-number eigenvector has the corresponding value of
every actual occupation-diagonal operator. -/
theorem occupationDiagonal_eigen (m : ℕ) (f : (Fin (m + 1) → Fin 3) → ℂ)
    (o : Fin (m + 1) → Fin 3) (x : Space (2 * m + 1))
    (hx : ∀ i, siteNumber m i x = ((o i : ℕ) : ℂ) • x) :
    occupationDiagonal m f x = f o • x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [occupationDiagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases ho : occupationAt m A = o
  · rw [ho]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ho
    have hne : ((occupationAt m A i : ℕ) : ℂ) ≠ ((o i : ℕ) : ℂ) := by
      intro h
      apply hi
      apply Fin.ext
      exact_mod_cast h
    rw [numberEigen_coordinate_zero m i x _ (hx i) A hne]
    simp

def lowProjection (m : ℕ) : Module.End ℂ (Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => if ∀ i, o i = 1 then 1 else 0)

def chargeInverse (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Module.End ℂ (Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => ((chargePenalty U V o)⁻¹ : ℝ))

theorem lowProjection_eq_zero_of_numberEigen (m : ℕ) (i : Fin (m + 1))
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m i x = η • x) (hη : η ≠ 1) :
    lowProjection m x = 0 := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [lowProjection, occupationDiagonal, fockDiagonal_coordinate, map_zero,
    Finsupp.zero_apply]
  by_cases hs : ∀ k, occupationAt m A k = 1
  · have hne : ((occupationAt m A i : ℕ) : ℂ) ≠ η := by
      simpa only [hs i, Fin.val_one, Nat.cast_one] using Ne.symm hη
    rw [numberEigen_coordinate_zero m i x η hx A hne]
    simp
  · simp [hs]

def chargeShift {m : ℕ} (k i j : Fin (m + 1)) : ℂ :=
  (if k = i then 1 else 0) - (if k = j then 1 else 0)

theorem siteMode_delta_sum (m : ℕ) (k i : Fin (m + 1)) (σ : Fin 2) :
    delta (siteMode m k 0) (siteMode m i σ) +
      delta (siteMode m k 1) (siteMode m i σ) = if k = i then 1 else 0 := by
  by_cases hki : k = i
  · subst k
    fin_cases σ <;> simp [delta, siteMode_eq_iff]
  · simp [delta, siteMode_eq_iff, hki]

theorem siteNumber_transfer_commutator (m : ℕ) (k i j : Fin (m + 1)) (σ τ : Fin 2) :
    siteNumber m k * transfer (siteMode m i σ) (siteMode m j τ) -
      transfer (siteMode m i σ) (siteMode m j τ) * siteNumber m k =
        chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) := by
  let E := transfer (siteMode m i σ) (siteMode m j τ)
  let n₀ := number (siteMode m k 0)
  let n₁ := number (siteMode m k 1)
  have h₀ := number_transfer_commutator (siteMode m k 0) (siteMode m i σ) (siteMode m j τ)
  have h₁ := number_transfer_commutator (siteMode m k 1) (siteMode m i σ) (siteMode m j τ)
  change (n₀ + n₁) * E - E * (n₀ + n₁) = chargeShift k i j • E
  calc
    _ = (n₀ * E - E * n₀) + (n₁ * E - E * n₁) := by noncomm_ring
    _ = ((delta (siteMode m k 0) (siteMode m i σ) -
          delta (siteMode m k 0) (siteMode m j τ)) +
        (delta (siteMode m k 1) (siteMode m i σ) -
          delta (siteMode m k 1) (siteMode m j τ))) • E := by
      rw [h₀, h₁, ← add_smul]
    _ = ((delta (siteMode m k 0) (siteMode m i σ) +
          delta (siteMode m k 1) (siteMode m i σ)) -
        (delta (siteMode m k 0) (siteMode m j τ) +
          delta (siteMode m k 1) (siteMode m j τ))) • E := by
      congr 1
      ring
    _ = _ := by rw [siteMode_delta_sum, siteMode_delta_sum]; rfl

/-- Hopping shifts the destination and source local particle numbers
by exactly plus and minus one. -/
theorem siteNumber_transfer_eigen (m : ℕ) (k i j : Fin (m + 1)) (σ τ : Fin 2)
    (x : Space (2 * m + 1)) (η : ℂ) (hx : siteNumber m k x = η • x) :
    siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) x) =
      (η + chargeShift k i j) • transfer (siteMode m i σ) (siteMode m j τ) x := by
  have h := LinearMap.congr_fun (siteNumber_transfer_commutator m k i j σ τ) x
  change siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) x) -
    transfer (siteMode m i σ) (siteMode m j τ) (siteNumber m k x) =
      chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) x at h
  rw [hx, map_smul] at h
  calc
    _ = chargeShift k i j • transfer (siteMode m i σ) (siteMode m j τ) x +
        η • transfer (siteMode m i σ) (siteMode m j τ) x := (sub_eq_iff_eq_add).mp h
    _ = _ := by rw [add_smul]; abel

theorem siteNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) (k : Fin (m + 1)) :
    siteNumber m k (spinWedge m s) = (1 : ℂ) • spinWedge m s := by
  simpa only [siteNumber, one_smul] using local_number_spinWedge m s k

theorem lowProjection_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    lowProjection m (spinWedge m s) = spinWedge m s := by
  have h := occupationDiagonal_eigen m (fun o => if ∀ i, o i = 1 then 1 else 0)
    (fun _ => 1) (spinWedge m s) (fun k => by simpa using siteNumber_spinWedge m s k)
  simpa [lowProjection] using h

/-- A genuine single hop creates the exact hole/double virtual charge
sector. Its inverse denominator retains the direct repulsion `V i j`. -/
theorem chargeInverse_transfer_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    chargeInverse m U V (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) •
        transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s) := by
  have hvalue (k : Fin (m + 1)) :
      1 + chargeShift k i j = ((chargeTransferOccupation j i k : ℕ) : ℂ) := by
    by_cases hki : k = i
    · subst k
      norm_num [chargeShift, chargeTransferOccupation, hij]
    · by_cases hkj : k = j
      · subst k
        norm_num [chargeShift, chargeTransferOccupation, Ne.symm hij]
      · norm_num [chargeShift, chargeTransferOccupation, hki, hkj]
  have heigen (k : Fin (m + 1)) :
      siteNumber m k (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) =
        ((chargeTransferOccupation j i k : ℕ) : ℂ) •
          transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s) := by
    rw [← hvalue]
    exact siteNumber_transfer_eigen m k i j σ τ _ _ (siteNumber_spinWedge m s k)
  have h := occupationDiagonal_eigen m
    (fun o => (((chargePenalty U V o)⁻¹ : ℝ) : ℂ))
    (chargeTransferOccupation j i)
    (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) heigen
  simpa only [chargeInverse, chargeTransfer_penalty U V j i (Ne.symm hij) hsymm hdiag,
    hsymm j i] using h

/-- Two transfers cannot return to the singly occupied sector unless
their oriented site changes are exact reverses. -/
theorem lowProjection_transfer_transfer_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j k l : Fin (m + 1)) (hij : i ≠ j) (hreverse : ¬(i = l ∧ j = k))
    (σ τ ρ υ : Fin 2) :
    lowProjection m
      (transfer (siteMode m i σ) (siteMode m j τ)
        (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s))) = 0 := by
  have heigen (r : Fin (m + 1)) :
      siteNumber m r
          (transfer (siteMode m i σ) (siteMode m j τ)
            (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s))) =
        ((1 + chargeShift r k l) + chargeShift r i j) •
          transfer (siteMode m i σ) (siteMode m j τ)
            (transfer (siteMode m k ρ) (siteMode m l υ) (spinWedge m s)) :=
    siteNumber_transfer_eigen m r i j σ τ _ _
      (siteNumber_transfer_eigen m r k l ρ υ _ _ (siteNumber_spinWedge m s r))
  by_cases hil : i = l
  · have hjk : j ≠ k := fun h => hreverse ⟨hil, h⟩
    have hjl : j ≠ l := fun h => hij (hil.trans h.symm)
    apply lowProjection_eq_zero_of_numberEigen m j _ _ (heigen j)
    norm_num [chargeShift, hjk, hjl, Ne.symm hij]
  · apply lowProjection_eq_zero_of_numberEigen m i _ _ (heigen i)
    by_cases hik : i = k
    · subst k
      norm_num [chargeShift, hij, hil]
    · norm_num [chargeShift, hij, hil, hik]

def siteHopping (m : ℕ) (i j : Fin (m + 1)) : Module.End ℂ (Space (2 * m + 1)) :=
  twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)

theorem chargeInverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) :
    chargeInverse m U V (siteHopping m i j (spinWedge m s)) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) • siteHopping m i j (spinWedge m s) := by
  simp [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    chargeInverse_transfer_spinWedge m U V hsymm hdiag s i j hij,
    chargeInverse_transfer_spinWedge m U V hsymm hdiag s j i (Ne.symm hij),
    hsymm j i, smul_add]

/-- Different unordered edges have zero second-order low compression,
with every spin channel and fermionic spectator retained. -/
theorem lowProjection_hopping_hopping_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j k l : Fin (m + 1)) (hij : i ≠ j)
    (hsame : ¬(i = k ∧ j = l)) (hreverse : ¬(i = l ∧ j = k)) :
    lowProjection m (siteHopping m i j (siteHopping m k l (spinWedge m s))) = 0 := by
  have hsame' : ¬(j = l ∧ i = k) := fun h => hsame ⟨h.2, h.1⟩
  have hreverse' : ¬(j = k ∧ i = l) := fun h => hreverse ⟨h.2, h.1⟩
  simp [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    lowProjection_transfer_transfer_zero m s i j k l hij hreverse,
    lowProjection_transfer_transfer_zero m s i j l k hij hsame,
    lowProjection_transfer_transfer_zero m s j i k l (Ne.symm hij) hsame',
    lowProjection_transfer_transfer_zero m s j i l k (Ne.symm hij) hreverse']

/-- The same-edge inverse compression, with the exact Coulomb-modified
denominator, acts as the expected Heisenberg superexchange numerator. -/
theorem hopping_inverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j : Fin (m + 1)) (hij : i ≠ j) :
    lowProjection m (siteHopping m i j (chargeInverse m U V (siteHopping m i j (spinWedge m s)))) =
      (((U - V i j)⁻¹ : ℝ) : ℂ) •
        ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap i j s))) := by
  rw [chargeInverse_hopping_spinWedge m U V hsymm hdiag s i j hij, map_smul, map_smul]
  have h := twoSiteHopping_sq_spinWedge m s i j hij
  change siteHopping m i j (siteHopping m i j (spinWedge m s)) = _ at h
  rw [h, map_smul, map_sub, lowProjection_spinWedge, lowProjection_spinWedge]

/-- All distinct-edge terms of the actual inverse compression vanish. -/
theorem cross_hopping_inverse_hopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (s : SourceSpinBasis (m + 1)) (i j k l : Fin (m + 1)) (hij : i ≠ j) (hkl : k ≠ l)
    (hsame : ¬(i = k ∧ j = l)) (hreverse : ¬(i = l ∧ j = k)) :
    lowProjection m (siteHopping m i j (chargeInverse m U V (siteHopping m k l (spinWedge m s)))) =
      0 := by
  rw [chargeInverse_hopping_spinWedge m U V hsymm hdiag s k l hkl, map_smul, map_smul,
    lowProjection_hopping_hopping_zero m s i j k l hij hsame hreverse, smul_zero]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
