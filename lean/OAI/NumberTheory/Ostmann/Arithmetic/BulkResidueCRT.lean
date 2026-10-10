import OAI.NumberTheory.Ostmann.ZeroDensity.PageRegularAverage
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkComparison

namespace OAI

/-! # Exact bulk residue separation, with Page terms in the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

/-- The only moduli remaining after the internal line comparison. -/
def bulkResidueModuli {I : Type*} (r : ℕ) (p : I → ℕ) : Unit ⊕ I → ℕ
  | .inl _ => r
  | .inr i => p i

def bulkResidueAssemble {I : Type*} (r : ℕ) (p : I → ℕ)
    (f : (ZMod r)ˣ) (g : ∀ i, (ZMod (p i))ˣ) :
    ∀ i, (ZMod (bulkResidueModuli r p i))ˣ
  | .inl _ => f
  | .inr i => g i

/-- Simultaneous CRT on all bulk slots, transposed into one frequency block
and one block for each spectator. -/
noncomputable def bulkResidueEquiv {I J : Type*} [Fintype I]
    (r : ℕ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j))) :
    (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) ≃
      (J → (ZMod r)ˣ) × (∀ i, J → (ZMod (p i))ˣ) where
  toFun x := (fun j => crtUnitEquiv (bulkResidueModuli r p) hc (x j) (.inl ()),
    fun i j => crtUnitEquiv (bulkResidueModuli r p) hc (x j) (.inr i))
  invFun z j := (crtUnitEquiv (bulkResidueModuli r p) hc).symm
    (bulkResidueAssemble r p (z.1 j) (fun i => z.2 i j))
  left_inv x := by
    funext j
    apply (crtUnitEquiv (bulkResidueModuli r p) hc).injective
    rw [MulEquiv.apply_symm_apply]
    funext i
    rcases i with u | i
    · cases u; rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext j
      exact congrFun ((crtUnitEquiv (bulkResidueModuli r p) hc).apply_symm_apply _) (.inl ())
    · funext i j
      exact congrFun ((crtUnitEquiv (bulkResidueModuli r p) hc).apply_symm_apply _) (.inr i)

theorem bulkResidueEquiv_frequency_modEq {I J : Type*} [Fintype I]
    (r : ℕ) [NeZero r] (p : I → ℕ)
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) (j : J) :
    Nat.ModEq r (x j).val.val ((bulkResidueEquiv r p hc x).1 j).val.val := by
  apply (ZMod.natCast_eq_natCast_iff _ _ r).mp
  simp only [ZMod.natCast_zmod_val]
  change ((x j).val.val : ZMod r) =
    ((show (ZMod r)ˣ from crtUnitEquiv (bulkResidueModuli r p) hc (x j) (.inl ())) : ZMod r)
  rw [crtUnitEquiv_apply]
  change ((x j).val.val : ZMod r) =
    (ZMod.castHom (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inl () : Unit ⊕ I)))
      (ZMod r)) (x j).val
  have h := congrArg
    (ZMod.castHom (Finset.dvd_prod_of_mem (bulkResidueModuli r p) (Finset.mem_univ (Sum.inl () : Unit ⊕ I)))
      (ZMod r)) (ZMod.natCast_zmod_val (x j).val)
  simpa only [map_natCast] using h

/-- The conductor deletion confines every retained Page factor to the
frequency residue array. -/
theorem bulkResidueEquiv_page {I J : Type*} [Fintype I]
    (r : ℕ) [NeZero r] (p : I → ℕ)
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (x : J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) (j : J) (y : ℝ) :
    pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val y =
      pageGiantWeight P Q r ((bulkResidueEquiv r p hc x).1 j).val.val y := by
  calc
    _ = pageGiantWeight P Q r (x j).val.val y := by simp only [pageGiantWeight, hpage]
    _ = _ := pageGiantWeight_modEq P Q r _ _ (bulkResidueEquiv_frequency_modEq r p hc x j) y

/-- Exact joint factorization, for arbitrary complex frequency amplitudes.
The spectator main terms have no residue-count or partition-count loss. -/
theorem bulk_residue_page_average {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) [NeZero r] (p : I → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (P : PublishedProgressionInput) (Q : ℕ)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (y : J → ℝ) (F : (J → (ZMod r)ˣ) → ℂ) (G : ∀ i, (J → (ZMod (p i))ˣ) → ℂ) :
    (Fintype.card (J → (ZMod (∏ i, bulkResidueModuli r p i))ˣ) : ℂ)⁻¹ *
      (∑ x, (F (bulkResidueEquiv r p hc x).1 *
        ∏ j, pageGiantWeight P Q (∏ i, bulkResidueModuli r p i) (x j).val.val (y j)) *
        ∏ i, G i ((bulkResidueEquiv r p hc x).2 i)) =
      ((Fintype.card (J → (ZMod r)ˣ) : ℂ)⁻¹ *
        ∑ a, F a * ∏ j, pageGiantWeight P Q r (a j).val.val (y j)) *
      ∏ i, ((Fintype.card (J → (ZMod (p i))ˣ) : ℂ)⁻¹ * ∑ b, G i b) := by
  simp_rw [bulkResidueEquiv_page r p hc P Q hpage]
  rw [uniform_equiv_product_average (bulkResidueEquiv (J := J) r p hc)
    (fun a => F a * ∏ j, pageGiantWeight P Q r (a j).val.val (y j))
    (fun b => ∏ i, G i (b i)), product_uniform_mean_complex]

end Ostmann

end OAI
