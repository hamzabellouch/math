import OAI.Geometry.PeriodicTiling.Stacking
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OAI

universe uV uι

namespace PeriodicTilingThree

theorem not_dvd_card_of_lt (V : Type uV) [AddCommGroup V] [Finite V]
    {q : ℕ} (hq : Nat.card V < q) : ¬ q ∣ Nat.card V := by
  intro hdiv
  exact (Nat.not_le_of_gt hq) (Nat.le_of_dvd Nat.card_pos hdiv)

theorem cyclicStackOrder_pos (V : Type uV) [AddCommGroup V] [Finite V]
    (q : ℕ) (hq : q.Prime) : 0 < q * Nat.card V :=
  Nat.mul_pos hq.pos Nat.card_pos

noncomputable def freshCyclicEquiv
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V) :
    V × ZMod q ≃+ ZMod (q * Nat.card V) := by
  let eV : V ≃+ ZMod (Nat.card V) :=
    (zmodAddCyclicAddEquiv (G := V) inferInstance).symm
  let hcop : q.Coprime (Nat.card V) :=
    hq.coprime_iff_not_dvd.mpr havoid
  exact
    ((eV.prodCongr (AddEquiv.refl (ZMod q))).trans
      (AddEquiv.prodComm :
        ZMod (Nat.card V) × ZMod q ≃+
          ZMod q × ZMod (Nat.card V))).trans
      (ZMod.chineseRemainder hcop).toAddEquiv.symm

noncomputable def cyclicStackEquiv
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V) :
    ((Plane × V) × ZMod q) ≃+ Plane × ZMod (q * Nat.card V) :=
  (AddEquiv.prodAssoc :
    ((Plane × V) × ZMod q) ≃+ Plane × (V × ZMod q)).trans
      ((AddEquiv.refl Plane).prodCongr (freshCyclicEquiv V q hq havoid))

@[simp]
theorem cyclicStackEquiv_fst
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)
    (x : (Plane × V) × ZMod q) :
    (cyclicStackEquiv V q hq havoid x).1 = x.1.1 := rfl

section Transport

variable (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
variable (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)

noncomputable def cyclicStackComplement (A : Set (Plane × V)) :
    Set (Plane × ZMod (q * Nat.card V)) :=
  cyclicStackEquiv V q hq havoid '' (A ×ˢ ({0} : Set (ZMod q)))

noncomputable def cyclicStackProjection
    (B : Set (Plane × ZMod (q * Nat.card V))) : Set (Plane × V) :=
  Prod.fst '' (cyclicStackEquiv V q hq havoid ⁻¹' B)

theorem fullyPeriodic_cyclicStackComplement {A : Set (Plane × V)}
    (hA : FullyPeriodic A) :
    FullyPeriodic (cyclicStackComplement V q hq havoid A) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  exact (fullyPeriodic_image_addEquiv_iff
    (cyclicStackEquiv V q hq havoid)).mpr hA.prod_singleton_zero

theorem fullyPeriodic_cyclicStackProjection
    {B : Set (Plane × ZMod (q * Nat.card V))} (hB : FullyPeriodic B) :
    FullyPeriodic (cyclicStackProjection V q hq havoid B) := by
  exact FullyPeriodic.image_of_surjective
    (AddMonoidHom.fst (Plane × V) (ZMod q))
    (fun x => ⟨(x, 0), rfl⟩)
    (FullyPeriodic.preimage_addEquiv (cyclicStackEquiv V q hq havoid) hB)

end Transport

section FiniteFamily

variable {ι : Type uι} [Fintype ι]
variable (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
variable (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)

noncomputable def cyclicStackTile
    (F : ι → Finset (Plane × V)) (E : ι → Finset (ZMod q)) :
    Finset (Plane × ZMod (q * Nat.card V)) := by
  classical
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact (stack F E).image (cyclicStackEquiv V q hq havoid)

theorem tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) {A : Set (Plane × V)}
    (hA : ∀ ν, Tiles (F ν) A) :
    Tiles (cyclicStackTile V q hq havoid F E)
      (cyclicStackComplement V q hq havoid A) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  exact Tiles.image_addEquiv (cyclicStackEquiv V q hq havoid)
    (tiles_stack_lift hpart hA)

theorem tiles_stack_of_tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    {B : Set (Plane × ZMod (q * Nat.card V))}
    (hB : Tiles (cyclicStackTile V q hq havoid F E) B) :
    Tiles (stack F E) (cyclicStackEquiv V q hq havoid ⁻¹' B) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  simpa only [cyclicStackTile, Finset.image_image, Function.comp_def,
    AddEquiv.symm_apply_apply, Finset.image_id'] using
    Tiles.preimage_addEquiv (cyclicStackEquiv V q hq havoid) hB

theorem tiles_of_tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty)
    {B : Set (Plane × ZMod (q * Nat.card V))}
    (hB : Tiles (cyclicStackTile V q hq havoid F E) B) :
    ∀ ν, Tiles (F ν) (cyclicStackProjection V q hq havoid B) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  exact tiles_of_tiles_stack hpart hfull hE
    (tiles_stack_of_tiles_cyclicStackTile V q hq havoid hB)

theorem cyclicStack_counterexample_of_common_system
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty)
    (hcommon : ∃ A, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    (cyclicStackTile V q hq havoid F E).Nonempty ∧
      (∃ A, Tiles (cyclicStackTile V q hq havoid F E)
        (cyclicStackComplement V q hq havoid A)) ∧
      ∀ B, Tiles (cyclicStackTile V q hq havoid F E) B →
        ¬ FullyPeriodic B := by
  obtain ⟨A, hA⟩ := hcommon
  have ht := tiles_cyclicStackTile V q hq havoid hpart hA
  refine ⟨ht.tile_nonempty, ⟨A, ht⟩, ?_⟩
  intro B hB hperiod
  exact hnone (cyclicStackProjection V q hq havoid B)
    (tiles_of_tiles_cyclicStackTile V q hq havoid hpart hfull hE hB)
    (fullyPeriodic_cyclicStackProjection V q hq havoid hperiod)

end FiniteFamily

end PeriodicTilingThree

end OAI
