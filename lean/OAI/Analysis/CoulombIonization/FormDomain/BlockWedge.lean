import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Form
import OAI.Analysis.CoulombIonization.FormDomain.CosetWedge
import OAI.Analysis.CoulombIonization.Variational.BlockPermutations

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma tensor_subgroupFermion {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevFermion ψ) (hφ : SobolevFermion φ) :
    SubgroupFermion (blockSubgroup N M) (tensorForm ψ φ) := by
  intro κ hκ s
  obtain ⟨π,ρ,rfl⟩ := blockSubgroup_mem.mp hκ
  have hp : ∀ᵐ z : Configuration N × Configuration M,
      ψ.value (leftList s ∘ π) (z.1 ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value (leftList s) z.1) :=
    Measure.quasiMeasurePreserving_fst.ae (hψ.2.2.2 π (leftList s))
  have hq : ∀ᵐ z : Configuration N × Configuration M,
      φ.value (rightList s ∘ ρ) (z.2 ∘ ρ) =
        (((Equiv.Perm.sign ρ : ℤ) : ℂ) * φ.value (rightList s) z.2) :=
    Measure.quasiMeasurePreserving_snd.ae (hφ.2.2.2 ρ (rightList s))
  have ha := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hp
  have hb := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hq
  filter_upwards [ha,hb] with x hx hy
  simp only [configurationJoin_symm_apply] at hx hy
  change ψ.value _ _ * φ.value _ _ = _ * (ψ.value _ _ * φ.value _ _)
  rw [leftList_blockPerm,rightList_blockPerm,leftList_blockPerm,rightList_blockPerm,
    hx,hy,blockPerm_sign,Units.val_mul,Int.cast_mul]
  ring

lemma cosetWedgeTerm_zero {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    {T : FormVector n} (q : Equiv.Perm (Fin n) ⧸ H) {x : Configuration n}
    (hx : FormZeroAt T (x ∘ q.out)) : FormZeroAt (cosetWedgeTerm H T q) x := by
  intro s
  constructor
  · rw [cosetWedgeTerm_value,(hx _).1,mul_zero]
  · intro j a
    change _ * T.gradient (s ∘ q.out.symm.symm) (q.out.symm j) a
      (x ∘ q.out.symm.symm) = 0
    rw [Equiv.symm_symm,(hx _).2,mul_zero]

lemma block_coset_terms_disjoint {N M : ℕ} {T : FormVector (N+M)} (A : Set Space)
    (hc : ∀ x i, x (finSumFinEquiv (Sum.inl i)) ∉ A → FormZeroAt T x)
    (he : ∀ x i, x (finSumFinEquiv (Sum.inr i)) ∈ A → FormZeroAt T x) :
    FormsDisjoint (cosetWedgeTerm (blockSubgroup N M) T) := by
  classical
  have hh (q r : Equiv.Perm (Fin (N+M)) ⧸ blockSubgroup N M) (hqr : q ≠ r)
      (x : Configuration (N+M)) :
      FormZeroAt (cosetWedgeTerm (blockSubgroup N M) T q) x ∨
      FormZeroAt (cosetWedgeTerm (blockSubgroup N M) T r) x := by
    by_cases hq : FormZeroAt T (x ∘ q.out)
    · exact Or.inl (cosetWedgeTerm_zero _ q hq)
    by_cases hr : FormZeroAt T (x ∘ r.out)
    · exact Or.inr (cosetWedgeTerm_zero _ r hr)
    exfalso
    apply hqr
    have hk : q.out⁻¹ * r.out ∈ blockSubgroup N M := by
      apply blockSubgroup_mem_of_maps_left
      intro i
      obtain ⟨j,hj⟩ := finSumFinEquiv.surjective ((q.out⁻¹ * r.out) (finSumFinEquiv (Sum.inl i)))
      cases j with
      | inl j => exact ⟨j,hj.symm⟩
      | inr j =>
        have hrA : x (r.out (finSumFinEquiv (Sum.inl i))) ∈ A := by
          by_contra ha
          exact hr (hc _ i ha)
        have hqA : x (q.out (finSumFinEquiv (Sum.inr j))) ∉ A := by
          intro ha
          exact hq (he _ j ha)
        have hij : q.out (finSumFinEquiv (Sum.inr j)) = r.out (finSumFinEquiv (Sum.inl i)) := by
          rw [hj]
          simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply]
        exact False.elim (hqA (hij ▸ hrA))
    have heq : (q.out : Equiv.Perm (Fin (N+M)) ⧸ blockSubgroup N M) = r.out :=
      QuotientGroup.eq.mpr hk
    simpa only [QuotientGroup.out_eq'] using heq
  constructor
  · intro q r hqr s x
    rcases hh q r hqr x with h | h
    · exact Or.inl (h s).1
    · exact Or.inr (h s).1
  · intro q r hqr s i a x
    rcases hh q r hqr x with h | h
    · exact Or.inl ((h s).2 i a)
    · exact Or.inr ((h s).2 i a)

theorem normalized_block_wedge_trial {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (he : ∀ x i, x i ∈ A → FormZeroAt φ x) (Z : ℝ) :
    ∃ F : FormVector (N+M), FormAdmissible F ∧ formEnergy Z F = formEnergy Z (tensorForm ψ φ) := by
  apply normalized_coset_wedge_trial
    (hψ.sobolevFermion.sobolevVector.tensor hφ.sobolevFermion.sobolevVector)
    (tensor_subgroupFermion hψ.sobolevFermion hφ.sobolevFermion)
  · rw [formMass_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,one_mul]
  · apply block_coset_terms_disjoint A
    · intro x i hx
      exact tensor_zero_left ψ φ (hc (leftList x) i hx)
    · intro x i hx
      exact tensor_zero_right ψ φ (he (rightList x) i hx)

end CoulombAtom

end

end OAI
