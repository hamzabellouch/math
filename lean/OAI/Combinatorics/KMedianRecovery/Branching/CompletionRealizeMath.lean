import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealizationChargingAssignment
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFillMath

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
def realize {E R B : Type*} [Fintype B] {a : ℕ} (F S Q : Finset V)
    (part : E→Fin a) (o : Fin a→E) (loc : E→V)
    (redLoc : R→V) (blueLoc blueDest : B→V) (xs : List E) (T : Finset R) : Finset V :=
  pad F ((S \ (Q∪T.image redLoc∪Finset.univ.image blueLoc)) ∪
    (filled part o loc xs∪Finset.univ.image blueDest)) S.card
lemma realize_spec {E R B : Type*} [DecidableEq E] [Fintype R] [Fintype B]
    [DecidableEq R] {a c q : ℕ}
    (D F S Q G : Finset V) (hS : S ⊆ F) (hn : S.Nonempty) (hQ : Q ⊆ S)
    (part : E → Fin a) (o : Fin a → E) (ho : ∀ j,part (o j)=j) (loc : E → V)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts (S \ Q))
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest (S \ Q) w radius M p)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ r, redLoc r ∈ S \ Q) (hblue : ∀ b, blueLoc b ∈ S \ Q)
    (hRB : ∀ r b, redLoc r ≠ blueLoc b)
    (hG : G ⊆ S \ Q) (hGR : ∀ r, redLoc r ∉ G) (hGB : ∀ b, blueLoc b ∉ G)
    (hdest : ∀ b, blueDest b ∈ F) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hcount : a+c ≤ Q.card+q+Fintype.card B)
    (K : ℝ)
    (hK : (∑ b, assignmentWeight D assignment (blueLoc b) *
      dist (blueLoc b) (blueDest b)) ≤ K)
    (xs : List E) (hX : ∀ j, (xs.toFinset.filter (fun e => part e = j)).card ≤ 1)
    (T : Finset R) (hT : T.card=q) :
    let X := xs.toFinset
    let U := realize F S Q part o loc redLoc blueLoc blueDest xs T
    U ⊆ F ∧ U.card = S.card ∧ ∃ hU : U.Nonempty,
      (∑ p ∈ D, distanceTo U hU p) ≤
        K + (∑ p ∈ D, cappedCost (virtualNearest (S \ Q) w radius M p) (fun e => dist p (loc e)) X) +
        (∑ r∈T,assignmentWeight D assignment (redLoc r) *
          cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) := by
  classical
  let X := xs.toFinset
  change _ ∧ _ ∧ _
  let Red := T.image redLoc
  let Blue := Finset.univ.image blueLoc
  let Dest := Finset.univ.image blueDest
  have hRcard : Red.card = q := by rw [Finset.card_image_of_injective _ hredInj,hT]
  have hBcard : Blue.card = Fintype.card B := by simp [Blue,Finset.card_image_of_injective _ hblueInj]
  have hRsub : Red ⊆ S \ Q := by
    intro s hs
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    exact hred r
  have hBsub : Blue ⊆ S \ Q := by
    intro s hs
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hs
    exact hblue b
  have hRBD : Disjoint Red Blue := by
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,_,he⟩ := Finset.mem_image.mp hs'
    exact hRB r b he.symm
  let Filled := filled part o loc xs
  have hFF := filled_subset F part o loc hloc xs
  have hFc : Filled.card≤a := filled_card part o loc xs
  have hFX := filled_covers part o loc xs hX
  have hFi := filled_ball part o ho loc w radius hball xs
  have hDF : Dest ⊆ F := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    exact hdest b
  have hAddc : (Filled ∪ Dest).card ≤ Q.card + Red.card + Blue.card := by
    have hd : Dest.card ≤ c := hdestCount
    have hh := Finset.card_union_le Filled Dest
    rw [hRcard,hBcard]
    omega
  let U₀ := (S \ (Q ∪ Red ∪ Blue)) ∪ (Filled ∪ Dest)
  have h₀ : U₀ ⊆ F := Finset.union_subset (Finset.sdiff_subset.trans hS) (Finset.union_subset hFF hDF)
  have hc₀ : U₀.card≤S.card := completion_cardinality S Q Red Blue (Filled∪Dest) hQ hRsub hBsub hRBD hAddc
  let U := pad F U₀ S.card
  have hUF := pad_subset F U₀ S.card h₀
  have hUc := pad_card F U₀ S.card h₀ hc₀ (Finset.card_le_card hS)
  have hUn := pad_nonempty F U₀ S.card h₀ hc₀ (Finset.card_le_card hS) (Finset.card_pos.mpr hn)
  have hU₀ := subset_pad F U₀ S.card
  have hFU : Filled ⊆ U := by
    intro f hf
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_left _ hf))
  have hDU : Dest ⊆ U := by
    intro d hd
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_right _ hd))
  have hGU : G ⊆ U := by
    intro s hs
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp (hG hs)).1,?_⟩
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_sdiff.mp (hG hs)).2 hb
      · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
        exact hGR r hs
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
      exact hGB b hs
  have hFillU : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i := by
    intro i
    obtain ⟨u,hu,hb⟩ := hFi i
    exact ⟨u,hFU hu,hb⟩
  have hXU : ∀ e ∈ X, loc e ∈ U := fun e he => hFU (hFX e he)
  have hBlueU : ∀ b ∈ (Finset.univ : Finset B), blueDest b ∈ U := by
    intro b _
    exact hDU (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
  have hcover : ∀ s ∈ S \ Q, s ∈ U ∨ (∃ r ∈ T, redLoc r = s) ∨
      (∃ b ∈ (Finset.univ : Finset B), blueLoc b = s) := by
    intro s hs
    by_cases hR : s ∈ Red
    · exact Or.inr (Or.inl (Finset.mem_image.mp hR))
    by_cases hB : s ∈ Blue
    · exact Or.inr (Or.inr (Finset.mem_image.mp hB))
    apply Or.inl
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hs).1,?_⟩
    simp only [Finset.mem_union,not_or]
    exact ⟨⟨(Finset.mem_sdiff.mp hs).2,hR⟩,hB⟩
  have hh := realization_charging_with_assignment D F (S \ Q) G U hUn w radius M assignment hamem hadist loc X T Finset.univ
    redLoc blueLoc blueDest hr hM0 hUF hGU hFillU hM hXU hBlueU hcover
  refine ⟨hUF,hUc,hUn,?_⟩
  refine hh.trans ?_
  dsimp only [X]
  linarith

end MetricKMedianRecovery.Completion.Canonical

end OAI
