import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungClassification
import OAI.Probability.BinarySweep.Representations.MatrixIsotypicWhitening
import OAI.Probability.BinarySweep.Representations.IsotypicOrthogonal

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

abbrev PartitionHilbert {n : ℕ} (p : n.Partition) := SpechtHilbert (diagram p)

def partitionHilbertRep {n : ℕ} (p : n.Partition) :
    Representation ℂ (Equiv.Perm (Fin n)) (PartitionHilbert p) :=
  (hilbertSpecht (diagram p)).comp (cellsEquivFin p).symm.permCongrHom.toMonoidHom

instance {n : ℕ} (p : n.Partition) : (partitionHilbertRep p).IsIrreducible :=
  Irrep.irreducible_comp_equiv _ _

def partitionHilbertEquiv {n : ℕ} (p : n.Partition) :
    (partitionRep p).Equiv (partitionHilbertRep p) :=
  .mk (spechtHilbertEquiv (diagram p)) (by
    intro g
    apply LinearMap.ext
    intro v
    change spechtHilbertEquiv (diagram p) (spechtRep (diagram p) _ v) =
      spechtHilbertEquiv (diagram p) (spechtRep (diagram p) _
        ((spechtHilbertEquiv (diagram p)).symm (spechtHilbertEquiv (diagram p) v)))
    rw [LinearEquiv.symm_apply_apply])

lemma partitionHilbertRep_unitary {n : ℕ} (p : n.Partition)
    (g : Equiv.Perm (Fin n)) (v : PartitionHilbert p) :
    ‖partitionHilbertRep p g v‖=‖v‖ := hilbertSpecht_unitary _ _ _

lemma partitionHilbertRep_equiv_injective {n : ℕ} (p q : n.Partition)
    (e : (partitionHilbertRep p).Equiv (partitionHilbertRep q)) : p=q :=
  partitionRep_equiv_injective p q
    ((partitionHilbertEquiv p).trans (e.trans (partitionHilbertEquiv q).symm))

lemma partitionHilbertRep_complete {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    [σ.IsIrreducible] : ∃ p : n.Partition, Nonempty (σ.Equiv (partitionHilbertRep p)) := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete σ
  exact ⟨p,⟨e.trans (partitionHilbertEquiv p)⟩⟩

lemma partition_isotypic_top {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ (Equiv.Perm (Fin n)) W) :
    (⨆ p : n.Partition, Irrep.isotypicSpan (partitionHilbertRep p) σ)=⊤ := by
  apply Irrep.iSup_isotypic_eq_top σ (fun p => partitionHilbertRep p)
  intro U _ _ _ τ hτ
  have := hτ
  exact partitionHilbertRep_complete τ

lemma partition_isotypic_orthogonal {n : ℕ} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) :
    OrthogonalFamily ℂ (fun p : n.Partition => Irrep.isotypicSpan (partitionHilbertRep p) σ)
      (fun p => (Irrep.isotypicSpan (partitionHilbertRep p) σ).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro p q hpq
  apply Irrep.isotypic_orthogonal (partitionHilbertRep q) (partitionHilbertRep p) σ
    (partitionHilbertRep_unitary q) (partitionHilbertRep_unitary p) hσ
  rintro ⟨e⟩
  exact hpq (partitionHilbertRep_equiv_injective q p e).symm

theorem partition_projection_sum {n : ℕ} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) W)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (v : W) :
    (∑ p : n.Partition, (Irrep.isotypicSpan (partitionHilbertRep p) σ).starProjection v)=v := by
  apply (partition_isotypic_orthogonal σ hσ).sum_projection_of_mem_iSup
  rw [partition_isotypic_top]
  trivial

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed

def pairWeight {n : ℕ} (β : Fin n → Bool) (g : Equiv.Perm (Fin n))
    (a b : Fin n) : ℤˣ :=
  if b<a ∧ β a=true ∧ β b=true then (if g a ≤ g b then -1 else 1) else 1

lemma koszulSign_eq_prod {n : ℕ} (β : Fin n → Bool) (g : Equiv.Perm (Fin n)) :
    koszulSign β g = ∏a, ∏b, pairWeight β g a b := by
  rw [← Fintype.prod_sigma (fun x : Σ _ : Fin n, Fin n => pairWeight β g x.1 x.2)]
  have he : finPairsLT n = Finset.univ.filter (fun x : Σ _ : Fin n, Fin n => x.2<x.1) := by
    ext x
    simp only [mem_finPairsLT,mem_filter,mem_univ,true_and]
  rw [koszulSign,he,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro x _
  dsimp [pairWeight]
  by_cases h : x.2<x.1 <;> by_cases h1 : β x.1=true <;> by_cases h2 : β x.2=true <;> simp [h,h1,h2]

def sumPerm {n m : ℕ} (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (n+m)) := finSumFinEquiv.permCongr (Equiv.sumCongr g h)

@[simp] lemma sumPerm_left {n m : ℕ} (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) (i : Fin n) :
    sumPerm g h (i.castAdd m) = (g i).castAdd m := by
  change sumPerm g h (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (g i))
  simp [sumPerm]

@[simp] lemma sumPerm_right {n m : ℕ} (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) (i : Fin m) :
    sumPerm g h (i.natAdd n) = (h i).natAdd n := by
  change sumPerm g h (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr (h i))
  simp [sumPerm]

theorem koszulSign_sum {n m : ℕ} (β : Fin (n+m) → Bool)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    koszulSign β (sumPerm g h) =
      koszulSign (fun i => β (i.castAdd m)) g * koszulSign (fun i => β (i.natAdd n)) h := by
  have hll (a b : Fin n) : pairWeight β (sumPerm g h) (a.castAdd m) (b.castAdd m) =
      pairWeight (fun i => β (i.castAdd m)) g a b := by
    simp only [pairWeight, sumPerm_left, Fin.lt_def, Fin.le_def, Fin.val_castAdd]
  have hrr (a b : Fin m) : pairWeight β (sumPerm g h) (a.natAdd n) (b.natAdd n) =
      pairWeight (fun i => β (i.natAdd n)) h a b := by
    simp [pairWeight]
  have hlr (a : Fin n) (b : Fin m) : pairWeight β (sumPerm g h) (a.castAdd m) (b.natAdd n) = 1 := by
    simp [pairWeight,Fin.lt_def, show ¬ n+b.val<a.val by omega]
  have hrl (a : Fin m) (b : Fin n) : pairWeight β (sumPerm g h) (a.natAdd n) (b.castAdd m) = 1 := by
    simp [pairWeight,Fin.le_def,show ¬ n+(h a).val ≤ (g b).val by omega]
  rw [koszulSign_eq_prod,Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add,hll,hrr,hlr,hrl]
  simp only [Finset.prod_const_one,mul_one,one_mul,← koszulSign_eq_prod]

end BinaryCoordinateSweeps.Signed

end

end OAI
