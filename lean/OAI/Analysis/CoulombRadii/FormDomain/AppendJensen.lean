import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoreReindex

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def H1Vector.appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) : H1Vector ((m+q)+k) :=
  (((u.labelCut χ hχ hp D hD hd p).reindex (coreReindex m e)).reindex (recordAssoc m q k))

theorem appendCut_positive_jensen {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (q k : (Fin (m+n) → L) → ℕ) (e : (p : Fin (m+n) → L) → Fin (q p+k p) ≃ Fin n)
    (W : Configuration (m+n) → ℝ) (hW : Measurable W) {B : ℝ}
    (hB0 : 0≤B) (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      ∑ p, sliceExpectation (u.appendCut χ hχ hp D hD hd p (e p)) (fun s x =>
        (max (coreConditionalObservable (u.appendCut χ hχ hp D hD hd p (e p))
          (W ∘ reindexConfiguration (coreReindex m (e p)) ∘ reindexConfiguration (recordAssoc m (q p) (k p))) s x) 0)^2) := by
  apply (labelCut_conditional_positive_jensen u χ hχ hp D hD hd W hW hB0 hB).trans
  apply Finset.sum_le_sum
  intro p hp0
  rw [←slice_positive_square_coreReindex _ (e p) W]
  exact record_more_positive_jensen _ _
    (hW.comp (reindexConfiguration_continuous _).measurable) hB0 (fun _ => hB _)

lemma mass_appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) :
    mass (u.appendCut χ hχ hp D hD hd p e)=mass (u.labelCut χ hχ hp D hD hd p) := by
  simp only [H1Vector.appendCut,mass_reindex]

lemma form_appendCut {J m n : ℕ} (S : Nuclei J) {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) :
    form S (u.appendCut χ hχ hp D hD hd p e)=form S (u.labelCut χ hχ hp D hD hd p) := by
  simp only [H1Vector.appendCut,form_reindex]

lemma potentialForm_appendCut {m n : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+n)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (hp : ∀ z, ∑ l, χ l z^2=1)
    (D : ℝ) (hD : 0≤D) (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n)
    (W : Configuration (m+n) → ℝ) :
    potentialForm (W ∘ reindexConfiguration (coreReindex m e) ∘ reindexConfiguration (recordAssoc m q k))
      (u.appendCut χ hχ hp D hD hd p e)=potentialForm W (u.labelCut χ hχ hp D hD hd p) := by
  change potentialForm ((W ∘ reindexConfiguration (coreReindex m e)) ∘ reindexConfiguration (recordAssoc m q k))
    (((u.labelCut χ hχ hp D hD hd p).reindex (coreReindex m e)).reindex (recordAssoc m q k))=_
  rw [potentialForm_reindex,potentialForm_reindex]

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def PartlyAntisymmetric {n : ℕ} (u : H1Vector n) (I : Set (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), (∀ i ∉ I, p i=i) → ∀ s : Spins n,
    ∀ᵐ x, u.value (s ∘ p) (permute p x)=(((p.sign:ℤ):ℂ))*u.value s x

def coreIndexSet (m k : ℕ) : Set (Fin (m+k)) := Set.range (Fin.natAdd m : Fin k → Fin (m+k))

lemma Antisymmetric.partly {n : ℕ} {u : H1Vector n} (hu : Antisymmetric u) (I : Set (Fin n)) :
    PartlyAntisymmetric u I := fun p _ s => hu p s

lemma reindexConfiguration_measurePreserving {m n : ℕ} (e : Fin m ≃ Fin n) :
    MeasurePreserving (reindexConfiguration e) volume volume := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact permute_measurePreserving e.symm

lemma reindex_permute {m n : ℕ} (e : Fin m ≃ Fin n) (p : Equiv.Perm (Fin m)) (x : Configuration m) :
    reindexConfiguration e (permute p x)=permute (e.permCongr p) (reindexConfiguration e x) := by
  ext ⟨i,b⟩
  simp [reindexConfiguration,permute,Equiv.permCongr_apply]

lemma PartlyAntisymmetric.reindex {m n : ℕ} {u : H1Vector n} {I : Set (Fin n)}
    (hu : PartlyAntisymmetric u I) (e : Fin m ≃ Fin n) (K : Set (Fin m))
    (hK : ∀ i∈K, e i∈I) : PartlyAntisymmetric (u.reindex e) K := by
  intro p hp s
  have hfix : ∀ i∉I, e.permCongr p i=i := by
    intro i hi
    have he : e.symm i∉K := fun h => hi (by simpa using hK _ h)
    simp [Equiv.permCongr_apply,hp _ he]
  have H := (reindexConfiguration_measurePreserving e).quasiMeasurePreserving.ae
    (hu (e.permCongr p) hfix (s ∘ e.symm))
  filter_upwards [H] with x hx
  rw [H1Vector.reindex_value,H1Vector.reindex_value,reindex_permute]
  have hs : (s ∘ p) ∘ e.symm=(s ∘ e.symm) ∘ (e.permCongr p) := by
    funext i
    simp [Function.comp_apply,Equiv.permCongr_apply]
  rw [hs]
  simpa only [Equiv.Perm.sign_permCongr] using hx

lemma PartlyAntisymmetric.labelCut {n : ℕ} {u : H1Vector n} {I : Set (Fin n)}
    (hu : PartlyAntisymmetric u I) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (K : Set (Fin n)) (hKI : K⊆I) (l : L)
    (hc : ∀ i∈K, p i=l) : PartlyAntisymmetric (u.labelCut χ hχ hp D hD hd p) K := by
  intro q hq s
  have hfix : ∀ i∉I, q i=i := fun i hi => hq i (fun h => hi (hKI h))
  have hperm (i : Fin n) : p (q i)=p i := by
    by_cases hi : i∈K
    · have hqi : q i∈K := by
        by_contra hh
        have he : q i=i := q.injective (hq _ hh)
        apply hh
        rw [he]
        exact hi
      rw [hc _ hi,hc _ hqi]
    · rw [hq _ hi]
  filter_upwards [hu q hfix s] with x hx
  change (↑(tensorCut χ p (permute q x)):ℂ)*u.value (s ∘ q) (permute q x)=_
  rw [tensorCut_permute_invariant χ p q hperm,hx]
  change (↑(tensorCut χ p x):ℂ)*((((q.sign:ℤ):ℂ))*u.value s x)=
    (((q.sign:ℤ):ℂ))*((↑(tensorCut χ p x):ℂ)*u.value s x)
  ring

lemma PartlyAntisymmetric.coreSlice {m k : ℕ} {u : H1Vector (m+k)}
    (hu : PartlyAntisymmetric u (coreIndexSet m k)) (s : Spins m) :
    ∀ᵐ x, Antisymmetric (u.coreSlice s x) := by
  apply u.coreSlice_antisymmetric
  intro p t
  apply hu (corePerm m p) _ (Fin.append s t)
  intro i hi
  refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) i hi
  · exact corePerm_left m p j
  · exact (hj ⟨j,rfl⟩).elim

lemma appendCut_partlyAntisymmetric {m n : ℕ} {u : H1Vector (m+n)}
    (hu : PartlyAntisymmetric u (coreIndexSet m n)) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin k, p (Fin.natAdd m (e (Fin.natAdd q i)))=l) :
    PartlyAntisymmetric (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin k => Fin.natAdd m (e (Fin.natAdd q i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin k => Fin.natAdd m (Fin.natAdd q i))
  have hI : I⊆coreIndexSet m n := by rintro i ⟨j,rfl⟩; exact ⟨_,rfl⟩
  have hcut := hu.labelCut χ hχ hp D hD hd p I hI l (by rintro i ⟨j,rfl⟩; exact hc j)
  have hsort := hcut.reindex (coreReindex m e) K (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [coreReindex_right]⟩)
  exact hsort.reindex (recordAssoc m q k) (coreIndexSet (m+q) k) (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [recordAssoc_right]⟩)

end Coulomb

end

end OAI
