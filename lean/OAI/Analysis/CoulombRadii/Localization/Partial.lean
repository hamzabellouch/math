import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.AppendJensen

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def PartlySupported {n : ℕ} (u : H1Vector n) (I : Set (Fin n)) (A : Set Space) : Prop :=
  ∀ s : Spins n, ∀ᵐ x, ∀ i∈I, position x i∉A → u.value s x=0

def outIndexSet (m k : ℕ) : Set (Fin (m+k)) := Set.range (Fin.castAdd k : Fin m → Fin (m+k))

lemma position_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (x : Configuration m) (i : Fin m) :
    position (reindexConfiguration e x) (e i)=position x i := by
  ext b
  simp [position,reindexConfiguration]

lemma PartlySupported.reindex {m n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) (e : Fin m ≃ Fin n) (K : Set (Fin m))
    (hK : ∀ i∈K, e i∈I) : PartlySupported (u.reindex e) K A := by
  intro s
  filter_upwards [(reindexConfiguration_measurePreserving e).quasiMeasurePreserving.ae (hu (s ∘ e.symm))] with x hx
  intro i hi hxA
  rw [H1Vector.reindex_value]
  exact hx (e i) (hK i hi) (by rwa [position_reindex])

lemma PartlySupported.mono_space {n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A B : Set Space}
    (hu : PartlySupported u I A) (hAB : A⊆B) : PartlySupported u I B := by
  intro s
  filter_upwards [hu s] with x hx
  exact fun i hi hh => hx i hi (fun h => hh (hAB h))

lemma PartlySupported.union {n : ℕ} {u : H1Vector n} {I K : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) (hv : PartlySupported u K A) : PartlySupported u (I∪K) A := by
  intro s
  filter_upwards [hu s,hv s] with x hx hy
  intro i hi hh
  exact hi.elim (fun h => hx i h hh) (fun h => hy i h hh)

lemma PartlySupported.labelCut {n : ℕ} {u : H1Vector n} {I : Set (Fin n)} {A : Set Space}
    (hu : PartlySupported u I A) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) : PartlySupported (u.labelCut χ hχ hp D hD hd p) I A := by
  intro s
  filter_upwards [hu s] with x hx
  intro i hi hh
  change (↑(tensorCut χ p x):ℂ)*u.value s x=0
  rw [hx i hi hh,mul_zero]

lemma labelCut_partlySupported {n : ℕ} (u : H1Vector n) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (I : Set (Fin n)) (l : L) (hc : ∀ i∈I, p i=l)
    (A : Set Space) (hA : ∀ z∉A, χ l z=0) :
    PartlySupported (u.labelCut χ hχ hp D hD hd p) I A := by
  intro s
  filter_upwards [] with x
  intro i hi hh
  have hzero : tensorCut χ p x=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hc i hi,hA _ hh]
  change (↑(tensorCut χ p x):ℂ)*u.value s x=0
  rw [hzero,Complex.ofReal_zero,zero_mul]

lemma PartlySupported.coreSlice {m k : ℕ} {u : H1Vector (m+k)} {A : Set Space}
    (hu : PartlySupported u (coreIndexSet m k) A) (s : Spins m) :
    ∀ᵐ x, SpatiallySupported (u.coreSlice s x) A := by
  have hall : ∀ᵐ x : Configuration m, ∀ t : Spins k, ∀ᵐ z : Configuration k,
      ∀ i∈coreIndexSet m k, position (joinConfiguration m k (x,z)) i∉A →
        u.value (Fin.append s t) (joinConfiguration m k (x,z))=0 :=
    ae_all_iff.mpr (fun t => Measure.ae_ae_of_ae_prod
      ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hu (Fin.append s t))))
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro t
  filter_upwards [ha t] with z hz hza
  obtain ⟨i,hi⟩ : ∃ i : Fin k, position z i∉A := by
    simpa only [allPositions,Set.mem_ofPred_eq,not_forall] using hza
  rw [u.coreSlice_value s hx]
  exact hz (Fin.natAdd m i) ⟨i,rfl⟩ (by rwa [position_join_right])

lemma PartlySupported.recorded_positions {m k : ℕ} {u : H1Vector (m+k)} {A : Set Space}
    (hu : PartlySupported u (outIndexSet m k) A) (s : Spins m) :
    ∀ᵐ x, mass (u.coreSlice s x)≠0 → ∀ i : Fin m, position x i∈A := by
  have hall : ∀ᵐ x : Configuration m, ∀ t : Spins k, ∀ᵐ z : Configuration k,
      ∀ i∈outIndexSet m k, position (joinConfiguration m k (x,z)) i∉A →
        u.value (Fin.append s t) (joinConfiguration m k (x,z))=0 :=
    ae_all_iff.mpr (fun t => Measure.ae_ae_of_ae_prod
      ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hu (Fin.append s t))))
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro hm i
  by_contra hi
  apply hm
  unfold mass
  apply Finset.sum_eq_zero
  intro t ht
  apply integral_eq_zero_of_ae
  filter_upwards [ha t] with z hz
  rw [u.coreSlice_value s hx,hz (Fin.castAdd k i) ⟨i,rfl⟩ (by rwa [position_join_left])]
  norm_num

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma appendCut_coreSupported {m n : ℕ} (u : H1Vector (m+n)) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin k, p (Fin.natAdd m (e (Fin.natAdd q i)))=l)
    (A : Set Space) (hA : ∀ z∉A, χ l z=0) :
    PartlySupported (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) A := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin k => Fin.natAdd m (e (Fin.natAdd q i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin k => Fin.natAdd m (Fin.natAdd q i))
  have hcut := labelCut_partlySupported u χ hχ hp D hD hd p I l (by rintro i ⟨j,rfl⟩; exact hc j) A hA
  have hsort := hcut.reindex (coreReindex m e) K (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [coreReindex_right]⟩)
  exact hsort.reindex (recordAssoc m q k) (coreIndexSet (m+q) k) (by
    rintro i ⟨j,rfl⟩
    exact ⟨j,by rw [recordAssoc_right]⟩)

lemma appendCut_outSupported {m n : ℕ} {u : H1Vector (m+n)} {A : Set Space}
    (hu : PartlySupported u (outIndexSet m n) A) {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → L) {q k : ℕ} (e : Fin (q+k) ≃ Fin n) (l : L)
    (hc : ∀ i : Fin q, p (Fin.natAdd m (e (Fin.castAdd k i)))=l)
    (B : Set Space) (hB : ∀ z∉B, χ l z=0) :
    PartlySupported (u.appendCut χ hχ hp D hD hd p e) (outIndexSet (m+q) k) (A∪B) := by
  let I : Set (Fin (m+n)) := Set.range (fun i : Fin q => Fin.natAdd m (e (Fin.castAdd k i)))
  let K : Set (Fin (m+(q+k))) := Set.range (fun i : Fin q => Fin.natAdd m (Fin.castAdd k i))
  have hnew := labelCut_partlySupported u χ hχ hp D hD hd p I l (by rintro i ⟨j,rfl⟩; exact hc j) B hB
  have hold := hu.labelCut χ hχ hp D hD hd p
  have hcut := (hold.mono_space (Set.subset_union_left : A⊆A∪B)).union
    (hnew.mono_space (Set.subset_union_right : B⊆A∪B))
  have hsort := hcut.reindex (coreReindex m e) (outIndexSet m (q+k)∪K) (by
    intro i hi
    rcases hi with ⟨j,rfl⟩|⟨j,rfl⟩
    · left
      exact ⟨j,by rw [coreReindex_left]⟩
    · right
      exact ⟨j,by rw [coreReindex_right]⟩)
  apply hsort.reindex (recordAssoc m q k) (outIndexSet (m+q) k)
  rintro i ⟨j,rfl⟩
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · left
    exact ⟨l,by rw [recordAssoc_left]⟩
  · right
    exact ⟨l,by rw [recordAssoc_middle]⟩

theorem binary_append_cut_outcome {m n : ℕ} (u : H1Vector (m+n))
    (hu : PartlyAntisymmetric u (coreIndexSet m n)) {A : Set Space}
    (hA : PartlySupported u (outIndexSet m n) A)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+n) → Fin 2) (B C : Set Space)
    (hB : ∀ z∉B, χ 0 z=0) (hC : ∀ z∉C, χ 1 z=0) :
    ∃ q k : ℕ, ∃ e : Fin (q+k) ≃ Fin n,
      PartlyAntisymmetric (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) ∧
      PartlySupported (u.appendCut χ hχ hp D hD hd p e) (coreIndexSet (m+q) k) C ∧
      PartlySupported (u.appendCut χ hχ hp D hD hd p e) (outIndexSet (m+q) k) (A∪B) := by
  obtain ⟨q,k,e,he0,he1⟩ := exists_binary_order (fun i : Fin n => p (Fin.natAdd m i))
  exact ⟨q,k,e,appendCut_partlyAntisymmetric hu χ hχ hp D hD hd p e 1 he1,
    appendCut_coreSupported u χ hχ hp D hD hd p e 1 he1 C hC,
    appendCut_outSupported hA χ hχ hp D hD hd p e 0 he0 B hB⟩

end Coulomb

end

end OAI
