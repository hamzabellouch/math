import OAI.Combinatorics.Ryser.LineCover.HighSamples
import OAI.Combinatorics.Ryser.LineCover.Overlap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem pencil_eq_at_complement
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (c : ComplementPopulation L p) (k l : PencilPopulation L p)
    (hxc : Incidence x c.val) (hxk : Incidence x k.val) (hxl : Incidence x l.val) :
    k = l := by
  apply Subtype.ext
  exact eq_affineLine_of_common_projective_incidence
    (ne_of_projectiveIncidence_of_not_projectiveIncidence
      ((projectiveIncidence_finite_affine x c.val).mpr hxc)
      (complementPopulation_not_incident L p c))
    ((projectiveIncidence_finite_affine x k.val).mpr hxk)
    (pencilPopulation_incident L p k)
    ((projectiveIncidence_finite_affine x l.val).mpr hxl)
    (pencilPopulation_incident L p l)

private theorem pointCrossPairs_card_le
    (x : Point F) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val).card ≤
      multiplicity Incidence L x - 1 := by
  let B := Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
    Incidence x kc.1.val ∧ Incidence x kc.2.val
  change B.card ≤ multiplicity Incidence L x - 1
  by_cases hB : B.Nonempty
  · obtain ⟨kc, hkc⟩ := hB
    have hxkc := (Finset.mem_filter.mp hkc).2
    let C := (L.filter (Incidence x)).erase kc.1.val
    have hk : kc.1.val ∈ L.filter (Incidence x) :=
      Finset.mem_filter.mpr ⟨coverPencil_subset L p kc.1.property, hxkc.1⟩
    let f : ↥B → ↥C := fun q =>
      ⟨q.val.2.val, Finset.mem_erase.mpr
        ⟨(pencil_ne_complement L p kc.1 q.val.2).symm,
          Finset.mem_filter.mpr ⟨complementPopulation_mem L p q.val.2,
            (Finset.mem_filter.mp q.property).2.2⟩⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Prod.ext
      · exact pencil_eq_at_complement x L p a.val.2 a.val.1 b.val.1
          (Finset.mem_filter.mp a.property).2.2
          (Finset.mem_filter.mp a.property).2.1
          (Finset.mem_filter.mp b.property).2.1
      · exact Subtype.ext (congrArg (fun z : ↥C => z.val) hab)
    calc
      B.card ≤ C.card := Finset.card_le_card_of_injective hf
      _ = multiplicity Incidence L x - 1 := by
        have hfilter :
            @Finset.filter _ (Incidence x)
              (fun l => Classical.propDecidable (Incidence x l)) L =
                L.filter (Incidence x) := Finset.filter_congr_decidable _ _ _
        unfold multiplicity
        rw [hfilter]
        exact Finset.card_erase_of_mem hk
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB, Finset.card_empty]
    exact Nat.zero_le _

theorem highCrossPairs_card_le
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (highCrossPairs X L p).card ≤ overlapExcess Incidence X L := by
  let B (x : Point F) :=
    Finset.univ.filter fun kc : PencilPopulation L p × ComplementPopulation L p =>
      Incidence x kc.1.val ∧ Incidence x kc.2.val
  have hcover : highCrossPairs X L p = X.biUnion B := by
    ext kc
    simp only [mem_highCrossPairs, Finset.mem_biUnion, B,
      Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    (highCrossPairs X L p).card = (X.biUnion B).card := congrArg Finset.card hcover
    _ ≤ ∑ x ∈ X, (B x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ X, (multiplicity Incidence L x - 1) :=
      Finset.sum_le_sum fun x _ => pointCrossPairs_card_le x L p
    _ = overlapExcess Incidence X L := rfl

theorem highShapePairs_card_le
    (S : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F) (D : ℕ)
    (hsparse : ∀ l, S ≠ linePoints l → (S ∩ linePoints l).card ≤ D) :
    (highShapePairs S L p).card ≤ D * (L \ coverPencil L p).card := by
  let B := highShapePairs S L p
  have hfiber (c : ComplementPopulation L p) :
      (B.filter fun kc => kc.2 = c).card ≤ D := by
    by_cases heq : S = linePoints c.val
    · have hempty : (B.filter fun kc => kc.2 = c) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨kc, hkc⟩
        have hm := (mem_highShapePairs S L p kc).mp (Finset.mem_filter.mp hkc).1
        have hc : kc.2 = c := (Finset.mem_filter.mp hkc).2
        exact hm.2.2 (heq.trans
          (congrArg (fun a : ComplementPopulation L p => linePoints a.val) hc.symm))
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · let T := B.filter fun kc => kc.2 = c
      let xof (q : ↥T) : Point F :=
        Classical.choose ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxof (q : ↥T) : xof q ∈ S ∧
          Incidence (xof q) q.val.1.val ∧ Incidence (xof q) q.val.2.val :=
        Classical.choose_spec ((mem_highShapePairs S L p q.val).mp
          (Finset.mem_filter.mp q.property).1).1
      have hxc (q : ↥T) : Incidence (xof q) c.val := by
        have hq := (hxof q).2.2
        rw [(Finset.mem_filter.mp q.property).2] at hq
        exact hq
      let f : ↥T → ↥(S ∩ linePoints c.val) := fun q =>
        ⟨xof q, Finset.mem_inter.mpr
          ⟨(hxof q).1, (mem_linePoints (xof q) c.val).mpr (hxc q)⟩⟩
      have hf : Function.Injective f := by
        intro a b hab
        have hxy : xof a = xof b :=
          congrArg (fun z : ↥(S ∩ linePoints c.val) => z.val) hab
        apply Subtype.ext
        apply Prod.ext
        · apply pencil_eq_at_complement (xof a) L p c a.val.1 b.val.1
          · exact hxc a
          · exact (hxof a).2.1
          · rw [hxy]
            exact (hxof b).2.1
        · exact (Finset.mem_filter.mp a.property).2.trans
            (Finset.mem_filter.mp b.property).2.symm
      exact (Finset.card_le_card_of_injective hf).trans (hsparse c.val heq)
  have hsplit : B.card = ∑ c : ComplementPopulation L p,
      (B.filter fun kc => kc.2 = c).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc
    (highShapePairs S L p).card = ∑ c : ComplementPopulation L p,
        (B.filter fun kc => kc.2 = c).card := hsplit
    _ ≤ ∑ _c : ComplementPopulation L p, D := Finset.sum_le_sum fun c _ => hfiber c
    _ = D * (L \ coverPencil L p).card := by simp [ComplementPopulation, Nat.mul_comm]

end RyserCoveringCounterexample.LineCover

end

end OAI
