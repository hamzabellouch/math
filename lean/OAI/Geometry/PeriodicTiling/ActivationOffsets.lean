import OAI.Geometry.PeriodicTiling.CyclicCoordinates
import OAI.Geometry.PeriodicTiling.ShiftMultiplicity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace OAI

universe uJ

namespace PeriodicTilingThree

noncomputable section

def separatedResidueLift {J : Type uJ} [Fintype J] (M : ℕ) [NeZero M]
    (v : J → ZMod M) (j : J) : ℤ :=
  ((v j).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J j).val : ℤ)

@[simp] theorem separatedResidueLift_cast {J : Type uJ} [Fintype J]
    (M : ℕ) [NeZero M] (v : J → ZMod M) (j : J) :
    (separatedResidueLift M v j : ZMod M) = v j := by
  simp [separatedResidueLift]

theorem separatedResidueLift_injective {J : Type uJ} [Fintype J]
    (M : ℕ) [NeZero M] (v : J → ZMod M) :
    Function.Injective (separatedResidueLift M v) := by
  intro i j hij
  change ((v i).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J i).val : ℤ) =
    ((v j).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J j).val : ℤ) at hij
  have he : (v i).val + M * (Fintype.equivFin J i).val =
      (v j).val + M * (Fintype.equivFin J j).val := by
    exact_mod_cast hij
  apply (Fintype.equivFin J).injective
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hlt)
    have hi := ZMod.val_lt (v i)
    nlinarith
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hgt)
    have hj := ZMod.val_lt (v j)
    nlinarith

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

abbrev ActivationIndex (i : Channel p) :=
  K E i × ShiftIndex (E.a i) (E.b i)

abbrev SeedActivationIndex (t : Fin 2) := ActivationIndex E (.inr t) × Residues p

def otherSeed (t : Fin 2) : Fin 2 := ⟨1 - t.val, by omega⟩

@[simp] theorem otherSeed_ne_self (t : Fin 2) : otherSeed t ≠ t := by
  fin_cases t <;> decide

@[simp] theorem otherSeed_otherSeed (t : Fin 2) : otherSeed (otherSeed t) = t := by
  fin_cases t <;> decide

def activationModulus (i : Channel p) : ℕ := (E.r i * E.a i) * E.b i

instance activationModulus_neZero (i : Channel p) : NeZero (activationModulus E i) := by
  unfold activationModulus
  infer_instance

private theorem activationCoprime (i : Channel p) :
    Nat.Coprime (E.r i * E.a i) (E.b i) := by
  rw [Nat.coprime_mul_iff_left]
  exact ⟨E.r_coprime_b i i, E.a_coprime_b i⟩

def activationCRT (i : Channel p) :
    ZMod (activationModulus E i) ≃+* ((K E i × ZMod (E.a i)) × ZMod (E.b i)) :=
  (ZMod.chineseRemainder (activationCoprime E i)).trans
    (RingEquiv.prodCongr (ZMod.chineseRemainder (E.r_coprime_a i i))
      (RingEquiv.refl _))

def activationResidue (i : Channel p) (j : ActivationIndex E i) :
    ZMod (activationModulus E i) :=
  (activationCRT E i).symm
    ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.2)

def ordinaryFirst (n : Column p) : ActivationIndex E (.inl n) → ℤ :=
  separatedResidueLift (activationModulus E (.inl n)) (activationResidue E (.inl n))

def ordinaryOffset (n : Column p) (j : ActivationIndex E (.inl n)) : Plane :=
  (ordinaryFirst E n j, -(n.val : ℤ) * ordinaryFirst E n j)

theorem ordinaryFirst_residues (n : Column p) (j : ActivationIndex E (.inl n)) :
    (((ordinaryFirst E n j : K E (.inl n)),
       (ordinaryFirst E n j : ZMod (E.a (.inl n)))),
       (ordinaryFirst E n j : ZMod (E.b (.inl n)))) =
      ((j.1, rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2),
        rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2) := by
  have h := congrArg (activationCRT E (.inl n))
    (separatedResidueLift_cast (activationModulus E (.inl n))
      (activationResidue E (.inl n)) j)
  rw [activationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1) h
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [ordinaryFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem ordinaryOffset_low (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : K E (.inl n)) = j.1 :=
  congrArg (fun z => z.1.1) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoA (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.a (.inl n))) =
      rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg (fun z => z.1.2) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoB (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.b (.inl n))) =
      rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg Prod.snd (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_lineValue (n : Column p) (j : ActivationIndex E (.inl n)) :
    lineValue n (ordinaryOffset E n j) = 0 := by
  simp [lineValue, ordinaryOffset]

theorem ordinaryOffset_injective (n : Column p) : Function.Injective (ordinaryOffset E n) := by
  intro i j hij
  exact separatedResidueLift_injective _ _ (congrArg Prod.fst hij)

def seedModulus (t : Fin 2) : ℕ :=
  (activationModulus E (.inr t) * p ^ 2) * E.a (.inr (otherSeed t))

instance seedModulus_neZero (t : Fin 2) : NeZero (seedModulus E t) := by
  unfold seedModulus
  infer_instance

private theorem activationCoprime_p (i : Channel p) :
    Nat.Coprime (activationModulus E i) (p ^ 2) := by
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  exact ⟨⟨E.r_coprime_p i, E.prime_coprime_p (.inl i)⟩,
    E.prime_coprime_p (.inr (.inl i))⟩

private theorem seedCoprime_other (t : Fin 2) :
    Nat.Coprime (activationModulus E (.inr t) * p ^ 2)
      (E.a (.inr (otherSeed t))) := by
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  refine ⟨⟨⟨E.r_coprime_a _ _, ?_⟩, ?_⟩, ?_⟩
  · apply E.prime_coprime
    simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq]
    exact (otherSeed_ne_self t).symm
  · apply E.prime_coprime
    simp
  · exact (E.prime_coprime_p (.inl (.inr (otherSeed t)))).symm.pow_left 2

def seedCRT (t : Fin 2) :
    ZMod (seedModulus E t) ≃+*
      ((((K E (.inr t) × ZMod (E.a (.inr t))) × ZMod (E.b (.inr t))) ×
        ZMod (p ^ 2)) × ZMod (E.a (.inr (otherSeed t)))) :=
  (ZMod.chineseRemainder (seedCoprime_other E t)).trans
    (RingEquiv.prodCongr
      ((ZMod.chineseRemainder (activationCoprime_p E (.inr t))).trans
        (RingEquiv.prodCongr (activationCRT E (.inr t)) (RingEquiv.refl _)))
      (RingEquiv.refl _))

def seedActivationResidue (t : Fin 2) (j : SeedActivationIndex E t) :
    ZMod (seedModulus E t) :=
  (seedCRT E t).symm
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0)

def seedFirst (t : Fin 2) : SeedActivationIndex E t → ℤ :=
  separatedResidueLift (seedModulus E t) (seedActivationResidue E t)

def seedOffset (t : Fin 2) (j : SeedActivationIndex E t) : Plane :=
  (seedFirst E t j, (j.2.2.val : ℤ))

theorem seedFirst_residues (t : Fin 2) (j : SeedActivationIndex E t) :
    (((((seedFirst E t j : K E (.inr t)),
      (seedFirst E t j : ZMod (E.a (.inr t)))),
      (seedFirst E t j : ZMod (E.b (.inr t)))),
      (seedFirst E t j : ZMod (p ^ 2))),
      (seedFirst E t j : ZMod (E.a (.inr (otherSeed t))))) =
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0) := by
  have h := congrArg (seedCRT E t)
    (separatedResidueLift_cast (seedModulus E t) (seedActivationResidue E t) j)
  rw [seedActivationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_) ?_
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1.1.1) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem seedOffset_low (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : K E (.inr t)) = j.1.1 :=
  congrArg (fun z => z.1.1.1.1) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoA (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr t))) =
      rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoB (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.b (.inr t))) =
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_other (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr (otherSeed t)))) = 0 :=
  congrArg Prod.snd (seedFirst_residues E t j)

@[simp] theorem seedOffset_residue (t : Fin 2) (j : SeedActivationIndex E t) :
    (((seedOffset E t j).1 : ZMod (p ^ 2)),
      ((seedOffset E t j).2 : ZMod (p ^ 2))) = j.2 := by
  apply Prod.ext
  · exact congrArg (fun z => z.1.2) (seedFirst_residues E t j)
  · simp [seedOffset]

theorem seedOffset_injective (t : Fin 2) : Function.Injective (seedOffset E t) := by
  intro i j hij
  exact separatedResidueLift_injective _ _ (congrArg Prod.fst hij)

end

end PeriodicTilingThree

end OAI
