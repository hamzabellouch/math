import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def RootPartitionMatch {I A B : Type*} {J : I → Type*}
    (xs : (Σ i, J i) → A × B) : Prop :=
  ∀ u v, (xs u).1 = (xs v).1 ↔ u.1 = v.1

def rootPartitionEncode {I A B : Type*} {J : I → Type*}
    (a : I ↪ A) (bs : (Σ i, J i) → B) : (Σ i, J i) → A × B :=
  fun x => (a x.1, bs x)

lemma rootPartitionEncode_matches {I A B : Type*} {J : I → Type*}
    (a : I ↪ A) (bs : (Σ i, J i) → B) :
    RootPartitionMatch (rootPartitionEncode a bs) := by
  intro u v
  exact a.injective.eq_iff

def rootPartitionEquiv {I A B : Type*} {J : I → Type*}
    [∀ i, Nonempty (J i)] :
    ((I ↪ A) × ((Σ i, J i) → B)) ≃
      {xs : (Σ i, J i) → A × B // RootPartitionMatch xs} := by
  classical
  let f : ((I ↪ A) × ((Σ i, J i) → B)) →
      {xs : (Σ i, J i) → A × B // RootPartitionMatch xs} :=
    fun ab => ⟨rootPartitionEncode ab.1 ab.2, rootPartitionEncode_matches ab.1 ab.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro ab cd h
    have he := congrArg Subtype.val h
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun xs => (xs ⟨i, Classical.choice inferInstance⟩).1) he
    · funext x
      exact congrArg (fun xs => (xs x).2) he
  · rintro ⟨xs, hx⟩
    let a : I ↪ A := ⟨(fun i => (xs ⟨i, Classical.choice inferInstance⟩).1), by
      intro i j hij
      exact (hx ⟨i, Classical.choice inferInstance⟩ ⟨j, Classical.choice inferInstance⟩).mp hij⟩
    refine ⟨(a, fun x => (xs x).2), Subtype.ext ?_⟩
    funext x
    apply Prod.ext
    · change (xs ⟨x.1, Classical.choice inferInstance⟩).1 = (xs x).1
      exact (hx _ _).mpr rfl
    · rfl

@[simp] lemma rootPartitionEquiv_apply {I A B : Type*} {J : I → Type*}
    [∀ i, Nonempty (J i)] (a : I ↪ A) (bs : (Σ i, J i) → B) :
    (rootPartitionEquiv (a,bs)).val = rootPartitionEncode a bs := rfl

lemma ennreal_tsum_fin_prod (m : ℕ) (J : Fin m → Type*)
    (f : ∀ i, J i → ℝ≥0∞) :
    (∑' x : ∀ i, J i, ∏ i, f i (x i)) = ∏ i, ∑' y, f i y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← (Fin.consEquiv J).tsum_eq]
    simp only [ENNReal.tsum_prod', Fin.prod_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right]

lemma ennreal_tsum_pi_prod {I : Type*} [Fintype I] (J : I → Type*)
    (f : ∀ i, J i → ℝ≥0∞) :
    (∑' x : ∀ i, J i, ∏ i, f i (x i)) = ∏ i, ∑' y, f i y := by
  let e := (Fintype.equivFin I).symm
  rw [← (Equiv.piCongrLeft J e).tsum_eq]
  simp_rw [← e.prod_comp, Equiv.piCongrLeft_apply_apply]
  exact ennreal_tsum_fin_prod _ _ _

lemma tsum_rootPartition {I A B : Type*} {J : I → Type*}
    [∀ i, Nonempty (J i)] (F : ((Σ i, J i) → A × B) → ℝ≥0∞) :
    (∑' xs, if RootPartitionMatch xs then F xs else 0) =
      ∑' a : I ↪ A, ∑' bs : (Σ i, J i) → B, F (rootPartitionEncode a bs) := by
  classical
  calc
    _ = ∑' xs : {xs : (Σ i, J i) → A × B // RootPartitionMatch xs}, F xs.val := by
      exact (tsum_subtype {xs | RootPartitionMatch xs} F).symm
    _ = ∑' ab : (I ↪ A) × ((Σ i, J i) → B), F (rootPartitionEncode ab.1 ab.2) :=
      (rootPartitionEquiv.tsum_eq (fun xs => F xs.val)).symm
    _ = _ := ENNReal.tsum_prod'

lemma root_partition_sum_factor {I A B : Type*} [Fintype I] {J : I → Type*}
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    (p : A → ℝ≥0∞) (q : A → B → ℝ≥0∞)
    (H : ∀ i, (J i → B) → ℝ≥0∞) :
    (∑' xs : (Σ i, J i) → A × B,
      if RootPartitionMatch xs then
        (∏ u, p (xs u).1 * q (xs u).1 (xs u).2) *
          ∏ i, H i (fun j => (xs ⟨i,j⟩).2) else 0) =
    ∑' a : I ↪ A, ∏ i, (p (a i)) ^ Fintype.card (J i) *
        (∑' ys : J i → B, (∏ j, q (a i) (ys j)) * H i ys) := by
  classical
  rw [tsum_rootPartition]
  apply tsum_congr
  intro a
  rw [← (Equiv.piCurry (fun (i : I) (_ : J i) => B)).symm.tsum_eq]
  simp only [Equiv.piCurry_symm_apply, rootPartitionEncode]
  simp_rw [Fintype.prod_sigma]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [← Finset.prod_mul_distrib, mul_assoc]
  simp only [Sigma.uncurry]
  rw [ennreal_tsum_pi_prod (fun i => J i → B)
    (fun i ys => p (a i) ^ Fintype.card (J i) * ((∏ j, q (a i) (ys j)) * H i ys))]
  apply Finset.prod_congr rfl
  intro i hi
  exact ENNReal.tsum_mul_left

lemma tsum_pi_supported {I U V : Type*} [Fintype I]
    (e : U ↪ V) (w : V → ℝ≥0∞) (hw : ∀ v, v ∉ Set.range e → w v = 0)
    (F : (I → V) → ℝ≥0∞) :
    (∑' xs : I → V, (∏ i, w (xs i)) * F xs) =
      ∑' xs : I → U, (∏ i, w (e (xs i))) * F (fun i => e (xs i)) := by
  classical
  let g : (I → U) → (I → V) := fun xs i => e (xs i)
  have hg : Function.Injective g := by
    intro xs ys he
    funext i
    exact e.injective (congrFun he i)
  exact (hg.tsum_eq (by
    intro xs hxs
    have hx : ∀ i, ∃ u, e u = xs i := by
      intro i
      by_contra h
      have hz := hw (xs i) h
      have hp : (∏ j, w (xs j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      exact hxs (by simp [hp])
    choose ys hy using hx
    exact ⟨ys, funext hy⟩)).symm

lemma indicator_forall_eq_prod {I : Type*} [Fintype I] (P : I → Prop) :
    (if ∀ i, P i then (1 : ℝ≥0∞) else 0) = ∏ i, if P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

def excludedBlockSum {A B : Type*} (label : A → B) :
    List (A → ℝ≥0∞) → {m : ℕ} → (Fin m → B) → ℝ≥0∞
  | [], _, _ => 1
  | f::fs, _, v => ∑' a, if ∃ j, v j = label a then 0 else
      f a * excludedBlockSum label fs (Fin.cons (label a) v)

def DistinctAssignmentGood {A B : Type*} (label : A → B)
    {n m : ℕ} (a : Fin n → A) (v : Fin m → B) : Prop :=
  Function.Injective (label ∘ a) ∧ ∀ i j, v j ≠ label (a i)

lemma distinctAssignmentGood_cons {A B : Type*} (label : A → B)
    {n m : ℕ} (a : A) (as : Fin n → A) (v : Fin m → B) :
    DistinctAssignmentGood label (Fin.cons a as) v ↔
      (¬ ∃ j, v j = label a) ∧
        DistinctAssignmentGood label as (Fin.cons (label a) v) := by
  rw [DistinctAssignmentGood, Fin.comp_cons, Fin.cons_injective_iff]
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    DistinctAssignmentGood, Set.mem_range, not_exists]
  constructor
  · rintro ⟨⟨hdis, hinj⟩, hroot, htail⟩
    exact ⟨hroot, hinj, fun i => ⟨Ne.symm (hdis i), htail i⟩⟩
  · rintro ⟨hroot, hinj, htail⟩
    exact ⟨⟨fun i => Ne.symm (htail i).1, hinj⟩, hroot, fun i => (htail i).2⟩

lemma excludedBlockSum_assignments {A B : Type*} (label : A → B)
    (fs : List (A → ℝ≥0∞)) {m : ℕ} (v : Fin m → B) :
    excludedBlockSum label fs v =
      ∑' a : Fin fs.length → A,
        if DistinctAssignmentGood label a v then ∏ i : Fin fs.length, fs[i] (a i) else 0 := by
  classical
  induction fs generalizing m with
  | nil =>
    simp [excludedBlockSum, DistinctAssignmentGood, Function.Injective]
  | cons f fs ih =>
    simp only [List.length_cons]
    rw [excludedBlockSum, ← (Fin.consEquiv (fun _ : Fin (fs.length+1) => A)).tsum_eq,
      ENNReal.tsum_prod']
    apply tsum_congr
    intro a
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, distinctAssignmentGood_cons]
    by_cases h : ∃ j, v j = label a
    · simp [h]
    · rw [ite_eq_right h, ih, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro as
      simp only [h, not_false_eq_true, true_and]
      by_cases ha : DistinctAssignmentGood label as (Fin.cons (label a) v)
      · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_eq_left ha]
        rfl
      · simp [ha]

lemma excludedBlockSum_embeddings {A B : Type*} (label : A → B)
    (hl : Function.Injective label) (fs : List (A → ℝ≥0∞)) :
    excludedBlockSum label fs (Fin.elim0 : Fin 0 → B) =
      ∑' a : Fin fs.length ↪ A, ∏ i : Fin fs.length, fs[i] (a i) := by
  classical
  rw [excludedBlockSum_assignments]
  have hg (a : Fin fs.length → A) :
      DistinctAssignmentGood label a (Fin.elim0 : Fin 0 → B) ↔ Function.Injective a := by
    simp only [DistinctAssignmentGood, Fin.forall_fin_zero, implies_true, and_true]
    exact ⟨fun h => fun i j he => h (congrArg label he), fun h => hl.comp h⟩
  simp_rw [hg]
  let g : (Fin fs.length ↪ A) → (Fin fs.length → A) := fun a => a
  have hginj : Function.Injective g := by
    intro a b h
    exact Function.Embedding.ext (fun i => congrFun h i)
  have he := hginj.tsum_eq (f := fun a : Fin fs.length → A =>
    if Function.Injective a then ∏ i : Fin fs.length, fs[i] (a i) else 0) (by
      intro a ha
      have hi : Function.Injective a := by
        by_contra hn
        exact ha (ite_eq_right hn)
      exact ⟨⟨a,hi⟩, rfl⟩)
  simpa only [g, Function.Embedding.injective, ↓reduceIte] using he.symm

lemma tsum_embedding_cast {A : Type*} {n m : ℕ} (h : n = m)
    (f : Fin n → A → ℝ≥0∞) :
    (∑' a : Fin n ↪ A, ∏ i : Fin n, f i (a i)) =
      ∑' a : Fin m ↪ A, ∏ i : Fin m, f (Fin.cast h.symm i) (a i) := by
  cases h
  rfl

lemma tsum_embeddings_list_map {A B C : Type*} (xs : List A) (f : A → B)
    (g : B → C → ℝ≥0∞) :
    (∑' a : Fin (xs.map f).length ↪ C,
      ∏ i : Fin (xs.map f).length, g (xs.map f)[i] (a i)) =
      ∑' a : Fin xs.length ↪ C, ∏ i : Fin xs.length, g (f xs[i]) (a i) := by
  rw [tsum_embedding_cast (List.length_map (f := f))]
  simp only [Fin.getElem_fin, Fin.val_cast, List.getElem_map]

end SphericalPerceptronFreeEnergy

end

end OAI
