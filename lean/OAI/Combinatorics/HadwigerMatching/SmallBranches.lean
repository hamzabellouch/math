import OAI.Combinatorics.HadwigerMatching.Definitions
import OAI.Combinatorics.HadwigerMatching.BranchCounting

namespace OAI

/-! Cliques and touching matchings formed by singleton and doubleton branches. -/
namespace HadwigerMatching
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {t : ℕ}

def singletonVertices (B : Fin t → Finset V) : Finset V :=
  (Finset.univ.filter fun i => (B i).card = 1).biUnion B

def twoVertexBranches (B : Fin t → Finset V) : Finset (Finset V) :=
  (Finset.univ.filter fun i => (B i).card = 2).image B

theorem mem_singletonVertices (B : Fin t → Finset V) (v : V) :
    v ∈ singletonVertices B ↔ ∃ i, (B i).card = 1 ∧ v ∈ B i := by
  simp [singletonVertices]

theorem mem_twoVertexBranches (B : Fin t → Finset V) (e : Finset V) :
    e ∈ twoVertexBranches B ↔ ∃ i, (B i).card = 2 ∧ B i = e := by
  simp [twoVertexBranches]

omit [DecidableEq V] in
/-- Nonemptiness is essential: distinct empty branches would not be injective. -/
theorem branches_injective (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Function.Injective B := by
  intro i j he
  by_contra hij
  obtain ⟨v, hv⟩ := hne i
  exact Finset.disjoint_left.mp (hdisj hij) hv (he ▸ hv)

theorem card_singletonVertices (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (singletonVertices B).card = singletonBranchCount B := by
  unfold singletonVertices singletonBranchCount
  rw [Finset.card_biUnion (fun i _ j _ hij => hdisj hij)]
  calc
    (∑ i ∈ Finset.univ.filter (fun i => (B i).card = 1), (B i).card) =
        ∑ i ∈ Finset.univ.filter (fun i => (B i).card = 1), 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ = _ := by simp

theorem card_twoVertexBranches (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (twoVertexBranches B).card = doubletonBranchCount B := by
  unfold twoVertexBranches doubletonBranchCount
  exact Finset.card_image_of_injective _ (branches_injective B hne hdisj)

omit [DecidableEq V] in
theorem singleton_branch_eq (B : Fin t → Finset V) {i : Fin t} {v : V}
    (hi : (B i).card = 1) (hv : v ∈ B i) : B i = {v} := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hi
  have hvw : v = w := by simpa [hw] using hv
  simpa [hvw] using hw

theorem singletonVertices_isClique (G : SimpleGraph V) (B : Fin t → Finset V)
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    G.IsClique (singletonVertices B : Set V) := by
  intro v hv w hw hvw
  obtain ⟨i, hi, hvi⟩ := (mem_singletonVertices B v).mp hv
  obtain ⟨j, hj, hwj⟩ := (mem_singletonVertices B w).mp hw
  have hBi := singleton_branch_eq B hi hvi
  have hBj := singleton_branch_eq B hj hwj
  have hij : i ≠ j := by
    intro he
    have hmem : v ∈ B j := he ▸ hvi
    have hvw' : v = w := by simpa [hBj] using hmem
    exact hvw hvw'
  obtain ⟨x, hx, y, hy, hxy⟩ := htouch i j hij
  have hxv : x = v := by simpa [hBi] using hx
  have hyw : y = w := by simpa [hBj] using hy
  simpa [hxv, hyw] using hxy

theorem twoVertexBranches_isTouchingMatching (G : SimpleGraph V)
    (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)
    (hclique : ∀ i, (B i).card = 2 → G.IsClique (B i : Set V)) :
    IsTouchingMatching G (twoVertexBranches B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := (mem_twoVertexBranches B e).mp he
    exact ⟨hi, hclique i hi⟩
  · intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := (mem_twoVertexBranches B e).mp he
    obtain ⟨j, _, rfl⟩ := (mem_twoVertexBranches B f).mp hf
    exact hdisj (fun hij => hef (congrArg B hij))
  · intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := (mem_twoVertexBranches B e).mp he
    obtain ⟨j, _, rfl⟩ := (mem_twoVertexBranches B f).mp hf
    exact htouch i j (fun hij => hef (congrArg B hij))

theorem twoVertexBranches_disjoint_singletonVertices (B : Fin t → Finset V)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    {e : Finset V} (he : e ∈ twoVertexBranches B) :
    Disjoint e (singletonVertices B) := by
  obtain ⟨i, hi, rfl⟩ := (mem_twoVertexBranches B e).mp he
  apply Finset.disjoint_left.mpr
  intro v hvi hv
  obtain ⟨j, hj, hvj⟩ := (mem_singletonVertices B v).mp hv
  have hij : i ≠ j := by
    intro heq
    have : (2 : ℕ) = 1 := hi.symm.trans ((congrArg (fun k => (B k).card) heq).trans hj)
    exact (by decide : (2 : ℕ) ≠ 1) this
  exact Finset.disjoint_left.mp (hdisj hij) hvi hvj

theorem singletonVertices_touch_twoVertexBranches (G : SimpleGraph V)
    (B : Fin t → Finset V)
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)
    {v : V} (hv : v ∈ singletonVertices B)
    {e : Finset V} (he : e ∈ twoVertexBranches B) :
    ∃ w ∈ e, G.Adj v w := by
  obtain ⟨i, hi, hvi⟩ := (mem_singletonVertices B v).mp hv
  obtain ⟨j, hj, rfl⟩ := (mem_twoVertexBranches B e).mp he
  have hij : i ≠ j := by
    intro heq
    have : (1 : ℕ) = 2 := hi.symm.trans ((congrArg (fun k => (B k).card) heq).trans hj)
    exact (by decide : (1 : ℕ) ≠ 2) this
  obtain ⟨x, hx, w, hw, hxw⟩ := htouch i j hij
  have hxv : x = v := by simpa [singleton_branch_eq B hi hvi] using hx
  exact ⟨w, hw, hxv ▸ hxw⟩

end HadwigerMatching

end OAI
