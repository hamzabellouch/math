import OAI.Combinatorics.SecondNeighborhood.ReductionCore
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def deficitPotential (r : V → V → Prop) (S T : Finset V) : ℕ :=
  (image r T \ ((image r S ∩ S) ∪ T)).card

@[simp] theorem deficitPotential_empty (r : V → V → Prop) (S : Finset V) :
    deficitPotential r S ∅ = 0 := by
  classical
  simp [deficitPotential]

omit [Fintype V] in

private theorem card_add_loss_le_card_add_gain
    (old new loss gain : Finset V) (hloss : loss ⊆ old)
    (hdisjoint : Disjoint loss new) (hgain : new \ old ⊆ gain) :
    new.card + loss.card ≤ old.card + gain.card := by
  classical
  have hsubset : new ⊆ (old \ loss) ∪ gain := by
    intro x hx
    by_cases hxo : x ∈ old
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_sdiff.mpr
      refine ⟨hxo, ?_⟩
      intro hxl
      exact Finset.disjoint_left.mp hdisjoint hxl hx
    · exact Finset.mem_union.mpr (Or.inr (hgain (Finset.mem_sdiff.mpr ⟨hx, hxo⟩)))
  have hcard := (Finset.card_le_card hsubset).trans
    (Finset.card_union_le (old \ loss) gain)
  have hpartition := Finset.card_sdiff_add_card_eq_card hloss
  omega

private theorem image_sdiff_union_card_balance (r : V → V → Prop)
    (I T Q : Finset V) (hdisjoint : Disjoint Q (I ∪ T)) :
    (image r (T ∪ Q) \ (I ∪ (T ∪ Q))).card + (Q ∩ image r T).card =
      (image r T \ (I ∪ T)).card +
        (image r Q \ (I ∪ T ∪ Q ∪ image r T)).card := by
  classical
  let A := image r T \ (I ∪ T)
  let C := image r Q \ (I ∪ T ∪ Q ∪ image r T)
  have hsplit : image r (T ∪ Q) \ (I ∪ (T ∪ Q)) = (A \ Q) ∪ C := by
    ext x
    simp only [A, C, image_union, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hpieces : Disjoint (A \ Q) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A, C, Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  have hinter : A ∩ Q = Q ∩ image r T := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxQ⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxQ, (Finset.mem_sdiff.mp hxA).1⟩
    · intro hx
      obtain ⟨hxQ, hximage⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨hximage, ?_⟩, hxQ⟩
      exact Finset.disjoint_left.mp hdisjoint hxQ
  have hpartition := Finset.card_sdiff_add_card_inter A Q
  rw [hinter] at hpartition
  rw [hsplit, Finset.card_union_of_disjoint hpieces]
  change (A \ Q).card + C.card + (Q ∩ image r T).card = A.card + C.card
  omega

theorem deficitPotential_step (r : V → V → Prop) (hr : IsOriented r)
    (hcounter : Counterexample r) (hminimal : ArcMinimal r)
    (S T : Finset V) (hT : T ⊆ image r S \ S)
    (hproper : T ≠ image r S \ S) :
    ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ (image r S \ S) \ T ∧
      deficitPotential r S (T ∪ Q) < deficitPotential r S T + Q.card := by
  classical
  let I := image r S ∩ S
  let E := image r S \ S
  let s : V → V → Prop := fun x y => r x y ∧ ¬ (x ∈ S ∧ y ∈ E \ T)
  have hs : IsOriented s := hr.mono (fun _ _ h => h.1)
  have hremain : (E \ T).Nonempty := by
    by_contra hn
    have hET : E ⊆ T := by
      intro y hy
      by_contra hyT
      exact hn ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyT⟩⟩
    exact hproper (Finset.Subset.antisymm hT hET)
  obtain ⟨b, hb⟩ := hremain
  have hbE := (Finset.mem_sdiff.mp hb).1
  have hbimage := (Finset.mem_sdiff.mp hbE).1
  obtain ⟨a, haS, hab⟩ := mem_image.mp hbimage
  have harcSubset : arcSet s ⊆ arcSet r := by
    apply arcSet_mono
    intro x y hxy
    exact hxy.1
  have harcStrict : (arcSet s).card < (arcSet r).card := by
    apply Finset.card_lt_card
    refine ⟨harcSubset, ?_⟩
    intro hreverse
    have habmem : (a, b) ∈ arcSet r := mem_arcSet.mpr hab
    have hsab : s a b := mem_arcSet.mp (hreverse habmem)
    exact hsab.2 ⟨haS, hb⟩
  have hnotCounter : ¬ Counterexample s := by
    intro hc
    exact (Nat.not_le_of_lt harcStrict) (hminimal s hs hc)
  have hgood : ∃ v, (firstNeighbors s v).card ≤ (secondNeighbors s v).card := by
    by_contra hn
    apply hnotCounter
    intro v
    exact Nat.lt_of_not_ge (fun hv => hn ⟨v, hv⟩)
  obtain ⟨v, hvGood⟩ := hgood
  have hlost : ∃ q, r v q ∧ ¬ s v q := by
    by_contra hn
    have hkeep : ∀ q, r v q → s v q := by
      intro q hvq
      by_contra hsfalse
      exact hn ⟨q, hvq, hsfalse⟩
    have hfirst : firstNeighbors r v ⊆ firstNeighbors s v := by
      intro q hq
      exact mem_firstNeighbors.mpr (hkeep q (mem_firstNeighbors.mp hq))
    have hsecond : secondNeighbors s v ⊆ secondNeighbors r v := by
      intro w hw
      obtain ⟨hwv, hnsvw, u, hsvu, hsuw⟩ := mem_secondNeighbors.mp hw
      apply mem_secondNeighbors.mpr
      exact ⟨hwv, (fun hvw => hnsvw (hkeep w hvw)), u, hsvu.1, hsuw.1⟩
    have hfirstCard := Finset.card_le_card hfirst
    have hsecondCard := Finset.card_le_card hsecond
    have hvBad := hcounter v
    omega
  obtain ⟨q, hvq, hnsvq⟩ := hlost
  have hcut : v ∈ S ∧ q ∈ E \ T := by
    by_contra hn
    exact hnsvq ⟨hvq, hn⟩
  have hvS := hcut.1
  let Q := firstNeighbors r v ∩ (E \ T)
  have hQnonempty : Q.Nonempty :=
    ⟨q, Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr hvq, hcut.2⟩⟩
  have hQsubset : Q ⊆ E \ T := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hQfirst : Q ⊆ firstNeighbors r v := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hQdisjoint : Disjoint Q (I ∪ T) := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxIT
    obtain ⟨hxE, hxnotT⟩ := Finset.mem_sdiff.mp (hQsubset hxQ)
    have hxnotS := (Finset.mem_sdiff.mp hxE).2
    rcases Finset.mem_union.mp hxIT with hxI | hxT
    · exact hxnotS (Finset.mem_inter.mp hxI).2
    · exact hxnotT hxT
  have hfirstEq : firstNeighbors s v = firstNeighbors r v \ Q := by
    ext x
    constructor
    · intro hx
      have hsx := mem_firstNeighbors.mp hx
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_firstNeighbors.mpr hsx.1, ?_⟩
      intro hxQ
      exact hsx.2 ⟨hvS, hQsubset hxQ⟩
    · intro hx
      obtain ⟨hxr, hxnotQ⟩ := Finset.mem_sdiff.mp hx
      apply mem_firstNeighbors.mpr
      refine ⟨mem_firstNeighbors.mp hxr, ?_⟩
      rintro ⟨_, hxET⟩
      exact hxnotQ (Finset.mem_inter.mpr ⟨hxr, hxET⟩)
  have hfirstCard : (firstNeighbors s v).card + Q.card = (firstNeighbors r v).card := by
    rw [hfirstEq]
    exact Finset.card_sdiff_add_card_eq_card hQfirst
  have hfirstCover : firstNeighbors r v ⊆ (I ∪ T) ∪ Q := by
    intro x hx
    have hximage := firstNeighbors_subset_image hvS hx
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hximage, hxS⟩))))
    · by_cases hxT : x ∈ T
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hxT)))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
          ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hximage, hxS⟩, hxT⟩⟩))
  have hfirstNewCover : firstNeighbors s v ⊆ I ∪ T := by
    intro x hx
    rw [hfirstEq] at hx
    obtain ⟨hxr, hxnotQ⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (hfirstCover hxr) with hxIT | hxQ
    · exact hxIT
    · exact False.elim (hxnotQ hxQ)
  have hsourceCover : ∀ u ∈ S, ∀ x, s u x → x ∈ I ∪ T := by
    intro u huS x hsux
    have hximage : x ∈ image r S := mem_image.mpr ⟨u, huS, hsux.1⟩
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hximage, hxS⟩))
    · by_cases hxT : x ∈ T
      · exact Finset.mem_union.mpr (Or.inr hxT)
      · exact False.elim (hsux.2 ⟨huS,
          Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hximage, hxS⟩, hxT⟩⟩)
  have hpathCover : ∀ x, (∃ u, s v u ∧ s u x) → x ∈ (I ∪ T) ∪ image r T := by
    intro x hx
    obtain ⟨u, hsvu, hsux⟩ := hx
    rcases Finset.mem_union.mp (hfirstNewCover (mem_firstNeighbors.mpr hsvu)) with huI | huT
    · exact Finset.mem_union.mpr
        (Or.inl (hsourceCover u (Finset.mem_inter.mp huI).2 x hsux))
    · exact Finset.mem_union.mpr (Or.inr (mem_image.mpr ⟨u, huT, hsux.1⟩))
  let B := Q ∩ image r T
  let C := image r Q \ (I ∪ T ∪ Q ∪ image r T)
  have hgain : secondNeighbors s v \ secondNeighbors r v ⊆ B := by
    intro x hx
    obtain ⟨hxnew, hxnotOld⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxv, hnsvx, u, hsvu, hsux⟩ := mem_secondNeighbors.mp hxnew
    have hrvx : r v x := by
      by_contra hn
      exact hxnotOld (mem_secondNeighbors.mpr ⟨hxv, hn, u, hsvu.1, hsux.1⟩)
    have hxcut : v ∈ S ∧ x ∈ E \ T := by
      by_contra hn
      exact hnsvx ⟨hrvx, hn⟩
    have hxQ : x ∈ Q := Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr hrvx, hxcut.2⟩
    apply Finset.mem_inter.mpr
    refine ⟨hxQ, ?_⟩
    rcases Finset.mem_union.mp (hpathCover x ⟨u, hsvu, hsux⟩) with hxIT | hximage
    · exact False.elim (Finset.disjoint_left.mp hQdisjoint hxQ hxIT)
    · exact hximage
  have hloss : C ⊆ secondNeighbors r v := by
    intro x hx
    obtain ⟨hximage, hxnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨u, huQ, hrux⟩ := mem_image.mp hximage
    have hrvu := mem_firstNeighbors.mp (hQfirst huQ)
    apply mem_secondNeighbors.mpr
    refine ⟨?_, ?_, u, hrvu, hrux⟩
    · intro hxv
      subst x
      exact hr.asymmetric hrvu hrux
    · intro hrvx
      exact hxnot (Finset.mem_union.mpr
        (Or.inl (hfirstCover (mem_firstNeighbors.mpr hrvx))))
  have hlossDisjoint : Disjoint C (secondNeighbors s v) := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxnew
    have hxnot := (Finset.mem_sdiff.mp hxC).2
    have hxcover := hpathCover x (mem_secondNeighbors.mp hxnew).2.2
    apply hxnot
    rcases Finset.mem_union.mp hxcover with hxIT | hximage
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hxIT)))
    · exact Finset.mem_union.mpr (Or.inr hximage)
  have hsecondCard := card_add_loss_le_card_add_gain
    (secondNeighbors r v) (secondNeighbors s v) C B hloss hlossDisjoint hgain
  have hbalance : deficitPotential r S (T ∪ Q) + B.card =
      deficitPotential r S T + C.card := by
    exact image_sdiff_union_card_balance r I T Q hQdisjoint
  have hvBad := hcounter v
  refine ⟨Q, hQnonempty, hQsubset, ?_⟩
  omega

end SeymourSecondNeighborhood

end OAI
