import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RealCardFiberBound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
section OrderedEmbeddings
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {N : ℕ} (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
variable [DecidableRel J.Adj] [DecidableRel G.Adj]

noncomputable def prefixEmbeddings (k : ℕ) (hk : k ≤ N) : Finset (Fin k ↪ V) :=
  Finset.univ.filter (fun φ => ∀ i j : Fin k,
    J.Adj (Fin.castLE hk i) (Fin.castLE hk j) → G.Adj (φ i) (φ j))

variable {G J}

omit [DecidableEq V] in
lemma mem_prefixEmbeddings {k : ℕ} {hk : k ≤ N} (φ : Fin k ↪ V) :
    φ ∈ prefixEmbeddings J G k hk ↔ ∀ i j : Fin k,
    J.Adj (Fin.castLE hk i) (Fin.castLE hk j) → G.Adj (φ i) (φ j) := by
  simp only [prefixEmbeddings,Finset.mem_filter,Finset.mem_univ,true_and]

def dropLastEmbedding {k : ℕ} (φ : Fin (k+1) ↪ V) : Fin k ↪ V :=
  ⟨fun i => φ i.castSucc,φ.injective.comp (Fin.castSucc_injective k)⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma dropLastEmbedding_apply {k : ℕ} (φ : Fin (k+1) ↪ V) (i : Fin k) :
    dropLastEmbedding φ i = φ i.castSucc := rfl

omit [DecidableEq V] in
lemma dropLastEmbedding_mem {k : ℕ} (hk : k+1 ≤ N) {φ : Fin (k+1) ↪ V}
    (hφ : φ ∈ prefixEmbeddings J G (k+1) hk) :
    dropLastEmbedding φ ∈ prefixEmbeddings J G k (by omega) := by
  apply (mem_prefixEmbeddings _).mpr
  intro i j hij
  apply (mem_prefixEmbeddings φ).mp hφ i.castSucc j.castSucc
  exact hij

def compatibleNext (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel G.Adj] {k : ℕ} (hk : k+1 ≤ N)
    (ψ : Fin k ↪ V) : Finset V := Finset.univ.filter (fun z =>
      ∀ i : Fin k, J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩ → G.Adj (ψ i) z)

lemma embedding_fiber_le {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V) :
    ((prefixEmbeddings J G (k+1) hk).filter (fun φ => dropLastEmbedding φ = ψ)).card ≤
      (compatibleNext J G hk ψ).card := by
  let s := (prefixEmbeddings J G (k+1) hk).filter (fun φ => dropLastEmbedding φ = ψ)
  have hinj : Set.InjOn (fun φ : Fin (k+1) ↪ V => φ (Fin.last k)) s := by
    intro φ hφ χ hχ he
    have hφr := (Finset.mem_filter.mp hφ).2
    have hχr := (Finset.mem_filter.mp hχ).2
    apply Function.Embedding.ext
    intro i
    refine Fin.lastCases he (fun j => ?_) i
    change dropLastEmbedding φ j = dropLastEmbedding χ j
    rw [hφr,hχr]
  calc
    s.card = (s.image (fun φ => φ (Fin.last k))).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card (by
      intro z hz
      obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hφ,hψ⟩ := Finset.mem_filter.mp hφ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro i hi
      have hh := (mem_prefixEmbeddings φ).mp hφ i.castSucc (Fin.last k) hi
      change G.Adj (dropLastEmbedding φ i) _ at hh
      rw [hψ] at hh
      exact hh)

theorem prefixEmbeddings_succ_bound {k : ℕ} (hk : k+1 ≤ N) (b : ℝ)
    (hb : ∀ ψ ∈ prefixEmbeddings J G k (by omega),
      ((compatibleNext J G hk ψ).card : ℝ) ≤ b) :
    ((prefixEmbeddings J G (k+1) hk).card : ℝ) ≤
      b * (prefixEmbeddings J G k (by omega)).card := by
  apply real_card_le_fiber_bound _ _ dropLastEmbedding
      (fun _ hφ => dropLastEmbedding_mem hk hφ) b
  intro ψ hψ
  exact (Nat.cast_le.mpr (embedding_fiber_le hk ψ)).trans (hb ψ hψ)

omit [DecidableEq V] in
lemma prefixEmbeddings_zero : (prefixEmbeddings J G 0 (Nat.zero_le N)).card = 1 := by
  have h : prefixEmbeddings J G 0 (Nat.zero_le N) = Finset.univ := by
    ext φ
    simp [prefixEmbeddings]
  rw [h,Finset.card_univ]
  exact Fintype.card_unique

theorem prefixEmbeddings_product_bound (b : ℕ → ℝ) (hb0 : ∀ k < N, 0 ≤ b k)
    (hb : ∀ k (hk : k+1 ≤ N), ∀ ψ ∈ prefixEmbeddings J G k (by omega),
      ((compatibleNext J G hk ψ).card : ℝ) ≤ b k)
    (k : ℕ) (hk : k ≤ N) :
    ((prefixEmbeddings J G k hk).card : ℝ) ≤ ∏ i ∈ Finset.range k, b i := by
  induction k with
  | zero => simp only [prefixEmbeddings_zero,Nat.cast_one,Finset.range_zero,
      Finset.prod_empty,le_refl]
  | succ k ih =>
    calc
      _ ≤ b k * (prefixEmbeddings J G k (by omega)).card :=
        prefixEmbeddings_succ_bound hk (b k) (hb k hk)
      _ ≤ b k * ∏ i ∈ Finset.range k, b i :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (hb0 k (by omega))
      _ = _ := by rw [Finset.prod_range_succ,mul_comm]

omit [DecidableEq V] in

theorem compatibleNext_le_codegree {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V)
    (i j : Fin k) (hij : i ≠ j)
    (hi : J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩)
    (hj : J.Adj (Fin.castLE (by omega) j) ⟨k,by omega⟩)
    (D : ℝ) (hD : ∀ x y : V, x ≠ y →
      ((Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) ≤ D) :
    ((compatibleNext J G hk ψ).card : ℝ) ≤ D := by
  have hs : compatibleNext J G hk ψ ⊆
      Finset.univ.filter (fun z => G.Adj (ψ i) z ∧ G.Adj (ψ j) z) := by
    intro z hz
    have hh := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh i hi,hh j hj⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hD _ _ (ψ.injective.ne hij))

omit [DecidableEq V] in
theorem compatibleNext_le_degree {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V)
    (i : Fin k) (hi : J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩)
    (Δ : ℝ) (hΔ : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ Δ) :
    ((compatibleNext J G hk ψ).card : ℝ) ≤ Δ := by
  have hs : compatibleNext J G hk ψ ⊆ Finset.univ.filter (G.Adj (ψ i)) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2 i hi⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hΔ _)

omit [DecidableEq V] in
lemma compatibleNext_le_order {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V) :
    (compatibleNext J G hk ψ).card ≤ Fintype.card V := Finset.card_le_univ _

end OrderedEmbeddings
end SharpTerminalLeave

end

end OAI
