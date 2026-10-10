import OAI.Combinatorics.Sensitivity.Composition

namespace OAI

/-! The Cartesian block construction works for arbitrary sensitive families. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K L : Type}

theorem compose_block_family (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) (C : K → Finset I) (D : L → Finset J)
    (hC : ∀ k, (C k).Nonempty) (hD : ∀ l, (D l).Nonempty)
    (hdC : Pairwise fun k k' => Disjoint (C k) (C k'))
    (hdD : Pairwise fun l l' => Disjoint (D l) (D l'))
    (hfC : ∀ k, f (flip (fun _ => false) (C k)) ≠ f (fun _ => false))
    (hgD : ∀ l, g (flip (fun _ => false) (D l)) ≠ g (fun _ => false)) :
    (∀ p : K × L, (C p.1 ×ˢ D p.2).Nonempty) ∧
      (Pairwise fun p q : K × L => Disjoint (C p.1 ×ˢ D p.2) (C q.1 ×ˢ D q.2)) ∧
      (∀ p : K × L,
        compose f g (flip (fun _ => false) (C p.1 ×ˢ D p.2)) ≠
          compose f g (fun _ => false)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    obtain ⟨i, hi⟩ := hC p.1
    obtain ⟨j, hj⟩ := hD p.2
    exact ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩⟩
  · intro p q hpq
    apply Finset.disjoint_product.mpr
    by_cases h : p.1 = q.1
    · exact Or.inr (hdD (fun h' => hpq (Prod.ext h h')))
    · exact Or.inl (hdC h)
  · intro p
    rw [compose_flip_product_zero f g _ _ hg (hgD p.2), compose_zero f g hg]
    exact hfC p.1

theorem compose_block_family_card [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) (C : K → Finset I) (D : L → Finset J)
    (hC : ∀ k, (C k).Nonempty) (hD : ∀ l, (D l).Nonempty)
    (hdC : Pairwise fun k k' => Disjoint (C k) (C k'))
    (hdD : Pairwise fun l l' => Disjoint (D l) (D l'))
    (hfC : ∀ k, f (flip (fun _ => false) (C k)) ≠ f (fun _ => false))
    (hgD : ∀ l, g (flip (fun _ => false) (D l)) ≠ g (fun _ => false)) :
    Fintype.card K * Fintype.card L ≤ blockSensitivityAt (compose f g) (fun _ => false) := by
  obtain ⟨hne, hd, hb⟩ := compose_block_family f g hg C D hC hD hdC hdD hfC hgD
  simpa only [Fintype.card_prod] using
    le_blockSensitivityAt_of_family (compose f g) (fun _ => false)
      (fun p : K × L => C p.1 ×ˢ D p.2) hne hd hb

end Paper320

end

end OAI
