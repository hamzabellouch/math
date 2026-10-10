import OAI.Geometry.HeilbronnTriangle.Definitions
import OAI.Geometry.HeilbronnTriangle.CRTLifting
import OAI.Geometry.HeilbronnTriangle.LiftingProbability

namespace OAI


noncomputable section

namespace Problem355.IntegerSampling

abbrev Box (N d : ℕ) (shift : Fin d → ℤ) :=
  (i : Fin d) → Set.Ico (shift i) (shift i + N)

def residue (m : ℕ) {N d : ℕ} {shift : Fin d → ℤ} (x : Box N d shift) :
    Fin d → ZMod m := fun i => ((x i).val : ZMod m)

theorem card_joint_residue_fibre (h q L d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (shift : Fin d → ℤ)
    (r : (Fin d → ZMod h) × (Fin d → ZMod q)) :
    (Finset.univ.filter (fun x : Box (L * (h * q)) d shift =>
      (residue h x, residue q x) = r)).card = L ^ d := by
  classical
  calc
    (Finset.univ.filter (fun x : Box (L * (h * q)) d shift =>
      (residue h x, residue q x) = r)).card =
        Fintype.card {x : Box (L * (h * q)) d shift //
          (residue h x, residue q x) = r} := (Fintype.card_subtype _).symm
    _ = Fintype.card {x : Box (L * (h * q)) d shift // ∀ i,
        ((x i).val : ZMod h) = r.1 i ∧ ((x i).val : ZMod q) = r.2 i} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun x => by
        simp only [Prod.ext_iff, residue, funext_iff, forall_and]
    _ = L ^ d := CRT.card_int_crt_vector_lifts h q L d hc shift r.1 r.2

def columnLaw (h q L : ℕ) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Box (L * (h * q)) 3 shift) : ℝ :=
  LiftingProbability.conditionalColumnMass (residue h) (residue q) a V s L x

 theorem columnLaw_nonneg (h q L : ℕ) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Box (L * (h * q)) 3 shift) : 0 ≤ columnLaw h q L shift a V s x :=
  LiftingProbability.conditionalColumnMass_nonneg (residue h) (residue q) a V s L x

theorem sum_columnLaw (h q L : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (shift : Fin 3 → ℤ)
    (a : Fin 3 → ZMod h) (V : Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hs : 0 < s) (hV : V.card = s) :
    (∑ x, columnLaw h q L shift a V s x) = 1 := by
  classical
  apply LiftingProbability.sum_conditionalColumnMass (residue h) (residue q)
    a V s L hs hL hV
  exact card_joint_residue_fibre h q L 3 hc shift

theorem card_triple_joint_residue_fibre (h q L : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (shift : Fin 3 → ℤ)
    (r : (Fin 3 → Fin 3 → ZMod h) × (Fin 3 → Fin 3 → ZMod q)) :
    (Finset.univ.filter (fun x : Fin 3 → Box (L * (h * q)) 3 shift =>
      ((fun i => residue h (x i)), (fun i => residue q (x i))) = r)).card = L ^ 9 := by
  classical
  calc
    (Finset.univ.filter (fun x : Fin 3 → Box (L * (h * q)) 3 shift =>
      ((fun i => residue h (x i)), (fun i => residue q (x i))) = r)).card =
        Fintype.card {x : Fin 3 → Box (L * (h * q)) 3 shift //
          ((fun i => residue h (x i)), (fun i => residue q (x i))) = r} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {x : Fin 3 → Box (L * (h * q)) 3 shift // ∀ i,
        (residue h (x i), residue q (x i)) = (r.1 i, r.2 i)} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun x => by
        simp only [Prod.ext_iff, funext_iff, forall_and]
    _ = Fintype.card (∀ i : Fin 3, {x : Box (L * (h * q)) 3 shift //
        (residue h x, residue q x) = (r.1 i, r.2 i)}) :=
      Fintype.card_congr (Equiv.subtypePiEquivPi
        (β := fun _ : Fin 3 => Box (L * (h * q)) 3 shift)
        (p := fun i x => (residue h x, residue q x) = (r.1 i, r.2 i)))
    _ = ∏ i : Fin 3, Fintype.card {x : Box (L * (h * q)) 3 shift //
        (residue h x, residue q x) = (r.1 i, r.2 i)} := Fintype.card_pi
    _ = L ^ 9 := by
      simp only [Fintype.card_subtype, card_joint_residue_fibre h q L 3 hc shift,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem sum_tripleLaw {Ω : Type*} [Fintype Ω]
    (h q L : ℕ) [NeZero h] [NeZero q] (hc : h.Coprime q) (hL : 0 < L)
    (shift : Fin 3 → ℤ) (O : Finset (Fin 3 → Fin 3 → ZMod h)) (hO : O.Nonempty)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ) (hs : 0 < s)
    (hV : ∀ ω, (V ω).card = s) (hw : ∑ ω, w ω = 1) :
    (∑ x : Fin 3 → Box (L * (h * q)) 3 shift,
      LiftingProbability.liftedMass (fun x i => residue h (x i))
        (fun x i => residue q (x i)) O w V s (L ^ 9) x) = 1 := by
  classical
  apply LiftingProbability.sum_liftedMass _ _ O hO w V s (L ^ 9) hs (pow_pos hL _) hV hw
  exact card_triple_joint_residue_fibre h q L hc shift

def samplingShift (N : ℕ) : Fin 3 → ℤ := ![0, 0, (N : ℤ)]

def project {N : ℕ} (x : Box N 3 (samplingShift N)) : Point :=
  (((x 0).val : ℝ) / ((x 2).val : ℝ), ((x 1).val : ℝ) / ((x 2).val : ℝ))

theorem project_in_unitSquare {N : ℕ} (hN : 0 < N)
    (x : Box N 3 (samplingShift N)) : pointInUnitSquare (project x) := by
  have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
    simpa [samplingShift] using (x 0).property
  have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
    simpa [samplingShift] using (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := by
    exact (x 2).property
  have hzpos : 0 < ((x 2).val : ℝ) := by
    have : (0 : ℤ) < (x 2).val := lt_of_lt_of_le (by exact_mod_cast hN) hz.1
    exact_mod_cast this
  unfold pointInUnitSquare project
  exact ⟨div_nonneg (by exact_mod_cast hx.1) hzpos.le,
    (div_le_one hzpos).mpr (by exact_mod_cast hx.2.le.trans hz.1),
    div_nonneg (by exact_mod_cast hy.1) hzpos.le,
    (div_le_one hzpos).mpr (by exact_mod_cast hy.2.le.trans hz.1)⟩

end Problem355.IntegerSampling

end

end OAI
