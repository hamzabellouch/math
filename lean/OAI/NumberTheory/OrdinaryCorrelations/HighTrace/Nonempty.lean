import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Shape

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

lemma Shape.nonempty {w : ClosedLine h ℓ} (Q : Shape w) : Q.edges.val.Nonempty :=
  nonempty_iff_ne_empty.mpr (mem_erase.mp Q.edges.property).1

lemma Shape.grows {w : ClosedLine h ℓ} (Q : Shape w) : Grows w Q.top.val Q.edges.val :=
  (mem_shapes ..).mp (mem_erase.mp Q.edges.property).2

def Shape.topEdge {w : ClosedLine h ℓ} (Q : Shape w) : Fin ℓ := Q.edges.val.min' Q.nonempty

lemma Shape.topEdge_mem {w : ClosedLine h ℓ} (Q : Shape w) : Q.topEdge ∈ Q.edges.val :=
  min'_mem _ _

lemma Shape.topEdge_origin {w : ClosedLine h ℓ} (Q : Shape w) :
    w.offset Q.topEdge.castSucc=Q.top.val := grows_min_origin w Q.grows Q.nonempty

lemma Shape.unary_edge_eq_topEdge {w : ClosedLine h ℓ} (Q : Shape w)
    (hu : w.children Q.top.val=1) (e : Fin ℓ) (he : e ∈ w.treeSteps)
    (hev : w.offset e.castSucc=Q.top.val) : e=Q.topEdge := by
  let U := w.treeSteps.filter (fun e => w.offset e.castSucc=Q.top.val)
  have hc : U.card≤1 := hu.le
  exact (card_le_one.mp hc) e (mem_filter.mpr ⟨he,hev⟩) Q.topEdge
    (mem_filter.mpr ⟨Q.grows.1 Q.topEdge_mem,Q.topEdge_origin⟩)

lemma Shape.topEdge_le {w : ClosedLine h ℓ} (Q : Shape w) {e : Fin ℓ}
    (he : e ∈ Q.edges.val) : Q.topEdge≤e := min'_le _ _ he

theorem selected_shapes_triangular {w : ClosedLine h ℓ} {n : ℕ}
    (Q : Fin n → Shape w) (horder : StrictMono (fun i => (Q i).topEdge))
    (i j : Fin n) (hcontains : (Q i).topEdge ∈ (Q j).edges.val) : j ≤ i := by
  exact (horder.le_iff_le).mp ((Q j).topEdge_le hcontains)

lemma prod_eq_pivot_prefix {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hf : ∀ j, i < j → f j=1) :
    (∏ j, f j) = f i * ∏ j ∈ univ.filter (fun j => j < i), f j := by
  rw [← mul_prod_erase (univ : Finset (Fin n)) f (mem_univ i)]
  apply congrArg (fun z => f i*z)
  symm
  apply prod_subset
  · intro j hj
    obtain ⟨hj,hji⟩ := mem_filter.mp hj
    exact mem_erase.mpr ⟨ne_of_lt hji,hj⟩
  · intro j hj hn
    have hne : j≠i := (mem_erase.mp hj).1
    have hnot : ¬j < i := by simpa only [mem_filter,mem_univ,true_and] using hn
    exact hf j (lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne))

theorem selected_prime_product {w : ClosedLine h ℓ} {n : ℕ}
    (Q : Fin n → Shape w) (horder : StrictMono (fun i => (Q i).topEdge))
    (x : Fin n → ℝ) (i : Fin n) :
    (∏ j : Fin n, if (Q i).topEdge ∈ (Q j).edges.val then x j else 1) =
      x i * ∏ j ∈ univ.filter (fun j => j < i),
        if (Q i).topEdge ∈ (Q j).edges.val then x j else 1 := by
  have hf : ∀ j, i < j →
      (if (Q i).topEdge ∈ (Q j).edges.val then x j else 1)=1 := by
    intro j hij
    apply ite_eq_right
    intro hc
    exact (not_le.mpr hij) (selected_shapes_triangular Q horder i j hc)
  rw [prod_eq_pivot_prefix _ i hf,ite_eq_left (Q i).topEdge_mem]

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
