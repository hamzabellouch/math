import OAI.Combinatorics.Crossing.DiskPassage
import OAI.Combinatorics.Crossing.ParameterNeighborhoods
import OAI.Combinatorics.Crossing.PathSubarc

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem diskPassage_separated {a b z w : Plane} {γ : Path a b} {r δ : ℝ}
    {s t : unitInterval} (P : DiskPassage γ z r s) (Q : DiskPassage γ w r t)
    (hst : s < t) (hδ : 0 < δ)
    (hd : Disjoint (closure (parameterNeighborhood s δ)) (closure (parameterNeighborhood t δ)))
    (hP : P.leave ∈ parameterNeighborhood s δ) (hQ : Q.enter ∈ parameterNeighborhood t δ) :
    P.leave < Q.enter :=
  parameterNeighborhood_ordered s t δ hδ hst (hd.mono subset_closure subset_closure) P.leave Q.enter hP hQ

def retainedSubarc {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ)
    (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i)) (i : Fin k) :
    Path (γ (P i.castSucc).leave) (γ (P i.succ).enter) :=
  pathSubarc γ (P i.castSucc).leave (P i.succ).enter

theorem ordered_passage_enter_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).enter) := by
  intro i j hij
  exact (P i).enter_lt_leave.trans (hsep i j hij)

theorem ordered_passage_leave_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).leave) := by
  intro i j hij
  exact (hsep i j hij).trans (P j).enter_lt_leave

theorem retained_interval_no_mark {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (hτ : StrictMono τ) (h0 : τ 0=0)
    (h1 : τ (Fin.last k)=1) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (i : Fin k) (t : unitInterval)
    (ht : t ∈ Set.Icc (P i.castSucc).leave (P i.succ).enter) : t ∉ Set.range τ := by
  rintro ⟨j,hj⟩
  have hleft : τ i.castSucc < 1 := by
    rw [← h1]
    exact hτ (show i.castSucc < Fin.last k from i.isLt)
  have hright : 0 < τ i.succ := by
    rw [← h0]
    exact hτ (show (0 : Fin (k+1)) < i.succ by change 0 < i.val+1; omega)
  by_cases hji : j ≤ i.castSucc
  · have hh := (hτ.monotone hji).trans_lt ((P i.castSucc).strict_leave hleft)
    exact hh.not_ge (ht.1.trans_eq hj.symm)
  · have hij : i.succ ≤ j := by
      change i.val+1 ≤ j.val
      have hh : ¬ j.val ≤ i.val := hji
      omega
    have hh := ((P i.succ).strict_enter hright).trans_le (hτ.monotone hij)
    exact hh.not_ge (hj.trans_le ht.2)

theorem retained_interval_pair_disjoint {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter)
    (i j : Fin k) (hij : i < j) :
    Disjoint (Set.Icc (P i.castSucc).leave (P i.succ).enter)
      (Set.Icc (P j.castSucc).leave (P j.succ).enter) := by
  have hi : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
  have hgap := ((ordered_passage_enter_strictMono γ τ r P hsep).monotone hi).trans_lt (P j.castSucc).enter_lt_leave
  apply Set.disjoint_left.mpr
  intro t ht hu
  exact hgap.not_ge (hu.1.trans ht.2)

end Zarankiewicz

end

end OAI
