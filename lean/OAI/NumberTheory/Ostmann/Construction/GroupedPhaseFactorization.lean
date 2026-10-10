import OAI.NumberTheory.Ostmann.Construction.GroupedResidueRow
import OAI.NumberTheory.Ostmann.Construction.RetainedGroupedPhase

namespace OAI

/-! # Exact phase factorization for a supported grouped pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem groupedPivotProduct_pos {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, Fact (P k).Prime] : 0 < ∏ k, P k :=
  Finset.prod_pos fun k _ => (Fact.out : (P k).Prime).pos

/-- All constituents are retained. The pivot row uses the single residue v/H
modulo their product; the retained factor uses that product as an integer. -/
theorem directedPrimePhase_factor_grouped {K I : Type*} [Fintype K] [Fintype I]
    (p : K ⊕ I → ℕ) [∀ j, Fact (p j).Prime]
    (χ : ∀ j, DirichletCharacter ℂ (p j))
    (t : ∀ j, ZMod (p j)) (ν : (K ⊕ I) → ℂ)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ) (b : Option I → Option I → ℤ)
    (κ : K → ℂ) (ε : K → ℤ) (H Y : ℕ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hHY : (∏ i, p (.inr i)) = H * Y)
    (hv : ∀ k, (v : ZMod (p (.inl k))) ≠ 0)
    (hν : ∀ k, ν (.inl k) = κ k * χ (.inl k) (v : ZMod (p (.inl k))) ^ (-ε k))
    (hself : ∀ k, g (.inl k) (.inl k) = 0)
    (hrow : ∀ k j, j ≠ .inl k → g (.inl k) j = ε k)
    (hpivot : ∀ i k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ i j, g (.inr i) (.inr j) = b (some i) (some j)) :
    directedPrimePhase p χ t ν g v =
      groupedResidueRow (fun k => p (.inl k)) (fun k => χ (.inl k)) κ
        (fun k => t (.inl k)) Y ε
        (positiveIntegerPivotKey (∏ k, p (.inl k))
          (groupedPivotProduct_pos (fun k => p (.inl k))) H v) *
      retainedGroupedPhase (fun i => p (.inr i)) (fun i => χ (.inr i))
        (fun i => t (.inr i)) (fun i => ν (.inr i)) b (∏ k, p (.inl k)) v := by
  have hcross (k : K) : (p (.inl k)).Coprime (H * Y) := by
    rw [← hHY]
    exact Nat.coprime_prod_right_iff.mpr fun i _ => hc (by intro he; cases he)
  have hHM : H.Coprime (∏ k, p (.inl k)) := by
    exact Nat.coprime_prod_right_iff.mpr fun k _ =>
      (hcross k).symm.of_dvd_left (Nat.dvd_mul_right H Y)
  have hD (k : K) : (tupleCofactor (fun k => p (.inl k)) k : ZMod (p (.inl k))) ≠ 0 := by
    have hcp : Pairwise (fun i j : K => (p (.inl i)).Coprime (p (.inl j))) := by
      intro i j hij
      exact hc (fun he => hij (Sum.inl.inj he))
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime _ _).mpr
      (tupleCofactor_coprime _ hcp k))
  have hY (k : K) : (Y : ZMod (p (.inl k))) ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime _ _).mpr
      ((hcross k).symm.of_dvd_left (Nat.dvd_mul_left Y H)))
  rw [directedPrimePhase_remove_grouped_pivot p χ t ν g b ε v hself hrow hpivot hrest]
  congr 1
  unfold groupedResidueRow pivotTupleRow
  apply Finset.prod_congr rfl
  intro k _
  rw [hHY, hν]
  have he := grouped_outgoing_local (χ (.inl k)) (κ k) (t (.inl k))
    (tupleCofactor (fun k => p (.inl k)) k) H Y (∏ k, p (.inl k))
    (groupedPivotProduct_pos (fun k => p (.inl k))) v (ε k)
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) hHM (hD k) (hY k) (hv k)
  simpa only [mul_assoc] using he

end Ostmann

end OAI
