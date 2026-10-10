import OAI.Combinatorics.ListHadwiger.WeightedBound

namespace OAI

namespace LinearListHadwiger

lemma cliqueBound_hadwiger {V : Type} [Fintype V] (G : SimpleGraph V) :
    ReedSeymour.CliqueBound G (hadwigerNumber G) := by
  classical
  intro I _ B hconn hdisj htouch
  apply cliqueMinor_le_hadwigerNumber
  let e := (Fintype.equivFin I).symm
  refine ⟨fun i => B (e i),fun i => hconn (e i),?_,?_⟩
  · intro i j hij
    exact hdisj _ _ (fun hh => hij (e.injective hh))
  · intro i j hij
    exact htouch _ _ (fun hh => hij (e.injective hh))

namespace Fractional
variable {V : Type} [Fintype V] [DecidableEq V]

lemma Dual.mass_le_one {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w)
    {S : Set V} (hS : ReedSeymour.Independent G S) : ReedSeymour.mass w S ≤ 1 := by
  classical
  have hs : Stable G (Finset.univ.filter (· ∈ S)) := by
    intro v hv z hz
    exact hS v (Finset.mem_filter.mp hv).2 z (Finset.mem_filter.mp hz).2
  simpa [ReedSeymour.mass,Finset.sum_filter] using hw.2 _ hs

theorem number_le_two_hadwiger (G : SimpleGraph V) :
    number G ≤ 2 * (hadwigerNumber G : ℝ) := by
  classical
  obtain ⟨w,hw,he⟩ := duality G
  rw [← he]
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    exact ReedSeymour.dual_weight_bound w (by have hh := one_le_hadwigerNumber G; omega)
      (cliqueBound_hadwiger G) (fun S hS => hw.mass_le_one hS)

theorem number_le_four_hadwiger (G : SimpleGraph V) :
    number G ≤ 4 * (hadwigerNumber G : ℝ) := by
  have hh := number_le_two_hadwiger G
  have hp : (0 : ℝ) ≤ hadwigerNumber G := Nat.cast_nonneg _
  linarith
end Fractional

namespace SmallList
lemma no_fractionalObstruction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ¬ FractionalObstruction G := by
  rintro ⟨S,hS⟩
  exact (not_lt_of_ge (Fractional.number_le_four_hadwiger (G.induce (↑S : Set V)))) hS
end SmallList

theorem main_theorem : MainStatement := by
  obtain ⟨C,hC,h⟩ := Recursion.final_bound_or_obstruction
  refine ⟨C,hC,?_⟩
  intro V _ _ G
  classical
  exact (h V G).resolve_right (SmallList.no_fractionalObstruction G)

end LinearListHadwiger

end OAI
