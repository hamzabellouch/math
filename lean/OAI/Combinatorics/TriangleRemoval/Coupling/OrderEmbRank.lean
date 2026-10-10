import Mathlib

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

lemma orderEmb_rank {N : ℕ} (s : Finset (Fin N)) (i : Fin s.card) :
    (s.filter (fun x => x < s.orderEmbOfFin rfl i)).card = i.val := by
  have he : s.filter (fun x => x < s.orderEmbOfFin rfl i) =
      (Finset.Iio i).image (s.orderEmbOfFin rfl) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_Iio]
    constructor
    · rintro ⟨hx,hxi⟩
      obtain ⟨j,hj⟩ := (s.orderIsoOfFin rfl).surjective ⟨x,hx⟩
      have he : s.orderEmbOfFin rfl j = x := congrArg Subtype.val hj
      exact ⟨j,(s.orderEmbOfFin rfl).lt_iff_lt.mp (he ▸ hxi),he⟩
    · rintro ⟨j,hji,rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl j,(s.orderEmbOfFin rfl).strictMono hji⟩
  rw [he,Finset.card_image_of_injective _ (s.orderEmbOfFin rfl).injective,Fin.card_Iio]

lemma initial_rank {N R : ℕ} (s : Finset (Fin N))
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s) (x : Fin N) (hx : x.val < R) :
    ((s.orderIsoOfFin rfl).symm ⟨x,hroot x hx⟩).val = x.val := by
  let i := (s.orderIsoOfFin rfl).symm ⟨x,hroot x hx⟩
  have he : s.orderEmbOfFin rfl i = x :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hroot x hx⟩)
  have hr := orderEmb_rank s i
  rw [he] at hr
  have hf : s.filter (fun z => z < x) = Finset.univ.filter (fun z : Fin N => z.val < x.val) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨hroot z (h.trans hx),h⟩⟩
  rw [hf,Fin.card_filter_val_lt,Nat.min_eq_right x.isLt.le] at hr
  exact hr.symm

lemma roots_le_card {N R : ℕ} (s : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s) : R ≤ s.card := by
  have hsub : Finset.univ.filter (fun z : Fin N => z.val < R) ⊆ s := by
    intro z hz
    exact hroot z (Finset.mem_filter.mp hz).2
  have h := Finset.card_le_card hsub
  rwa [Fin.card_filter_val_lt,Nat.min_eq_right hR] at h

lemma orderEmb_initial {N R : ℕ} (s : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s)
    (i : Fin s.card) (hi : i.val < R) : (s.orderEmbOfFin rfl i).val = i.val := by
  let x : Fin N := ⟨i.val,hi.trans_le hR⟩
  let j := (s.orderIsoOfFin rfl).symm ⟨x,hroot x hi⟩
  have hj : j = i := Fin.ext (initial_rank s hroot x hi)
  have he := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hroot x hi⟩)
  change s.orderEmbOfFin rfl j = x at he
  rw [hj] at he
  exact congrArg Fin.val he

lemma orderEmb_nonroot {N R : ℕ} (s : Finset (Fin N))
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s)
    (i : Fin s.card) (hi : R ≤ i.val) : R ≤ (s.orderEmbOfFin rfl i).val := by
  by_contra hn
  have hx : (s.orderEmbOfFin rfl i).val < R := Nat.lt_of_not_ge hn
  have hr := initial_rank s hroot (s.orderEmbOfFin rfl i) hx
  have he : (s.orderIsoOfFin rfl).symm
      ⟨s.orderEmbOfFin rfl i,hroot (s.orderEmbOfFin rfl i) hx⟩ = i := by
    apply (s.orderIsoOfFin rfl).injective
    simpa only [OrderIso.apply_symm_apply] using (show
      (⟨s.orderEmbOfFin rfl i,hroot (s.orderEmbOfFin rfl i) hx⟩ : s) = s.orderIsoOfFin rfl i from rfl)
  rw [he] at hr
  omega

end SharpTerminalLeave

end

end OAI
