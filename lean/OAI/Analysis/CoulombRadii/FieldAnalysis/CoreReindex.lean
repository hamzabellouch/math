import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordJensen

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma potentialForm_reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n)
    (W : Configuration n → ℝ) :
    potentialForm (W ∘ reindexConfiguration e) (u.reindex e)=potentialForm W u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  unfold potentialForm
  have he (s : Spins m) : (∫ x, (W ∘ reindexConfiguration e) x*‖(u.reindex e).value s x‖^2)=
      ∫ x, W x*‖u.value (s ∘ e.symm) x‖^2 := by
    simpa only [Function.comp_apply,H1Vector.reindex_value,reindexConfiguration,permute] using
      (permute_integral_real e.symm (fun x => W x*‖u.value (s ∘ e.symm) x‖^2))
  simp_rw [he]
  exact Equiv.sum_comp (permutationSpins e.symm) (fun s => ∫ x, W x*‖u.value s x‖^2)

def coreReindex (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) : Fin (m+q) ≃ Fin (m+k) :=
  finSumFinEquiv.symm.trans (((Equiv.refl (Fin m)).sumCongr e).trans finSumFinEquiv)

lemma coreReindex_left (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) (i : Fin m) :
    coreReindex m e (Fin.castAdd q i)=Fin.castAdd k i := by simp [coreReindex]
lemma coreReindex_right (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) (i : Fin q) :
    coreReindex m e (Fin.natAdd m i)=Fin.natAdd m (e i) := by simp [coreReindex]
lemma coreReindex_symm (m : ℕ) {q k : ℕ} (e : Fin q ≃ Fin k) :
    (coreReindex m e).symm=coreReindex m e.symm := by
  apply Equiv.symm_bijective.injective
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [coreReindex]

lemma append_coreReindex {m q k : ℕ} (e : Fin q ≃ Fin k) (s : Spins m) (t : Spins q) :
    (Fin.append s t) ∘ (coreReindex m e).symm=Fin.append s (t ∘ e.symm) := by
  rw [coreReindex_symm]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [coreReindex_left,coreReindex_right]

lemma reindex_join_coreReindex {m q k : ℕ} (e : Fin q ≃ Fin k) (x : Configuration m)
    (y : Configuration q) :
    reindexConfiguration (coreReindex m e) (joinConfiguration m q (x,y))=
      joinConfiguration m k (x,reindexConfiguration e y) := by
  ext ⟨i,b⟩
  change joinConfiguration m q (x,y) ((coreReindex m e).symm i,b)=_
  rw [coreReindex_symm]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [coreReindex_left,joinConfiguration_left,joinConfiguration_left]
  · rw [coreReindex_right,joinConfiguration_right,joinConfiguration_right]
    rfl

lemma coreSlice_coreReindex_values {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (s : Spins m) :
    ∀ᵐ x : Configuration m, ∀ t : Spins q, ∀ z : Configuration q,
      ((u.reindex (coreReindex m e)).coreSlice s x).value t z=
        ((u.coreSlice s x).reindex e).value t z := by
  filter_upwards [u.coreSliceRegular_ae s,
    (u.reindex (coreReindex m e)).coreSliceRegular_ae s] with x hx hv
  intro t z
  rw [(u.reindex (coreReindex m e)).coreSlice_value s hv,H1Vector.reindex_value,
    append_coreReindex,reindex_join_coreReindex,H1Vector.reindex_value,u.coreSlice_value s hx]

lemma coreConditionalObservable_coreReindex {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (W : Configuration (m+k) → ℝ) (s : Spins m) :
    ∀ᵐ x : Configuration m,
      mass ((u.reindex (coreReindex m e)).coreSlice s x)=mass (u.coreSlice s x) ∧
      coreConditionalObservable (u.reindex (coreReindex m e))
        (W ∘ reindexConfiguration (coreReindex m e)) s x=coreConditionalObservable u W s x := by
  filter_upwards [coreSlice_coreReindex_values u e s] with x hx
  have hv : ∀ t, ((u.reindex (coreReindex m e)).coreSlice s x).value t =ᵐ[volume]
      ((u.coreSlice s x).reindex e).value t := fun t => Eventually.of_forall (hx t)
  have hm : mass ((u.reindex (coreReindex m e)).coreSlice s x)=mass (u.coreSlice s x) := by
    rw [mass_congr_ae _ _ hv,mass_reindex]
  refine ⟨hm,?_⟩
  unfold coreConditionalObservable
  rw [potentialForm_normalized_eq,potentialForm_normalized_eq,hm,
    potentialForm_congr_values _ _ _ hv]
  congr 1
  simp only [Function.comp_apply,reindex_join_coreReindex]
  exact potentialForm_reindex _ e (fun z => W (joinConfiguration m k (x,z)))

lemma slice_positive_square_coreReindex {m q k : ℕ} (u : H1Vector (m+k))
    (e : Fin q ≃ Fin k) (W : Configuration (m+k) → ℝ) :
    sliceExpectation (u.reindex (coreReindex m e)) (fun s x =>
      (max (coreConditionalObservable (u.reindex (coreReindex m e))
        (W ∘ reindexConfiguration (coreReindex m e)) s x) 0)^2)=
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [coreConditionalObservable_coreReindex u e W s] with x hx
  rw [hx.1,hx.2]

lemma Antisymmetric.reindex {q k : ℕ} {u : H1Vector k} (hu : Antisymmetric u)
    (e : Fin q ≃ Fin k) : Antisymmetric (u.reindex e) := by
  have h : q=k := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst k
  exact hu.permutation _

end Coulomb
end

end
end

end OAI
