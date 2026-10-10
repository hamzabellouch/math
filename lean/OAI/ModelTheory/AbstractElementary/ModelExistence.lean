import Mathlib

namespace OAI

/-! Models of prescribed cardinality in abstract elementary classes. -/

universe u

namespace EventualCategoricity

open FirstOrder
open scoped Cardinal

structure SetModel (L : FirstOrder.Language.{u, u}) where
  carrier : ZFSet.{u}
  str : L.Structure carrier

instance {L : FirstOrder.Language.{u, u}} (M : SetModel L) : L.Structure M.carrier := M.str

namespace SetModel

variable {L : FirstOrder.Language.{u, u}}

def Submodel (M N : SetModel L) : Prop :=
  ∃ e : M.carrier ↪[L] N.carrier, ∀ x, (e x).val = x.val

def ImageOf (M : SetModel L) {N N' : SetModel L}
    (f : N.carrier ≃[L] N'.carrier) (M' : SetModel L) : Prop :=
  M'.Submodel N' ∧ ∀ y : ZFSet.{u},
    y ∈ M'.carrier ↔ ∃ x : N.carrier, x.val ∈ M.carrier ∧ (f x).val = y

def card (M : SetModel L) : Cardinal.{u} := M.carrier.card

end SetModel

structure AEC (L : FirstOrder.Language.{u, u}) where
  mem : SetModel L → Prop
  strong : SetModel L → SetModel L → Prop
  strong_mem : ∀ {M N}, strong M N → mem M ∧ mem N
  refl : ∀ M, mem M → strong M M
  trans : ∀ {M N P}, strong M N → strong N P → strong M P
  antisymm : ∀ {M N}, strong M N → strong N M → M = N
  submodel : ∀ {M N}, strong M N → M.Submodel N
  isoClosed : ∀ {M N}, mem M → (M.carrier ≃[L] N.carrier) → mem N
  isoStrong : ∀ {M N N'}, strong M N →
    ∀ f : N.carrier ≃[L] N'.carrier,
      ∃ M', M.ImageOf f M' ∧ strong M' N'
  coherence : ∀ {M₀ M₁ M₂}, M₀.Submodel M₁ →
    strong M₀ M₂ → strong M₁ M₂ → strong M₀ M₁
  chainUnion : ∀ δ : Ordinal.{u}, δ ≠ 0 →
    ∀ c : δ.ToType → SetModel L,
      (∀ i, mem (c i)) → (∀ i j, i ≤ j → strong (c i) (c j)) →
      ∃ U, mem U ∧
        (∀ x : ZFSet.{u}, x ∈ U.carrier ↔ ∃ i, x ∈ (c i).carrier) ∧
        (∀ i, strong (c i) U) ∧
        ∀ N, mem N → (∀ i, strong (c i) N) → strong U N
  LS : Cardinal.{u}
  LS_infinite : ℵ₀ ≤ LS
  LS_language : L.card + ℵ₀ ≤ LS
  LS_bound : ∀ M, mem M → ∀ A : ZFSet.{u}, A ⊆ M.carrier →
    ∃ N, strong N M ∧ A ⊆ N.carrier ∧ N.card ≤ A.card + LS
  LS_least : ∀ ℓ : Cardinal.{u}, ℵ₀ ≤ ℓ → L.card + ℵ₀ ≤ ℓ →
    (∀ M, mem M → ∀ A : ZFSet.{u}, A ⊆ M.carrier →
      ∃ N, strong N M ∧ A ⊆ N.carrier ∧ N.card ≤ A.card + ℓ) → LS ≤ ℓ

namespace AEC

variable {L : FirstOrder.Language.{u, u}}

def Categorical (K : AEC L) (κ : Cardinal.{u}) : Prop :=
  (∃ M, K.mem M ∧ M.card = κ) ∧
  ∀ M N, K.mem M → K.mem N → M.card = κ → N.card = κ →
    Nonempty (M.carrier ≃[L] N.carrier)

def UnboundedCategoricity (K : AEC L) : Prop :=
  ∀ κ : Cardinal.{u}, ∃ ρ, κ ≤ ρ ∧ K.Categorical ρ

def CategoricityTail (K : AEC L) : Prop :=
  ∃ θ : Cardinal.{u}, ∀ κ, θ ≤ κ → K.Categorical κ

end AEC

def UniformEventualCategoricity : Prop :=
  ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → ∃ μ : Cardinal.{u}, lam ≤ μ ∧
    ∀ (L : FirstOrder.Language.{u, u}) (K : AEC L), K.LS ≤ lam →
      (∃ κ, μ ≤ κ ∧ K.Categorical κ) → ∀ κ', μ ≤ κ' → K.Categorical κ'

def QualitativeEventualCategoricity : Prop :=
  ∀ (L : FirstOrder.Language.{u, u}) (K : AEC L),
    K.UnboundedCategoricity → K.CategoricityTail

theorem exists_subset_card (x : ZFSet.{u}) {κ : Cardinal.{u}}
    (hκ : κ ≤ x.card) :
    ∃ A : ZFSet.{u}, A ⊆ x ∧ A.card = κ := by
  have h : Cardinal.lift.{u + 1} κ ≤ Cardinal.mk x := by
    rw [ZFSet.cardinalMk_coe_sort]
    exact Cardinal.lift_le.mpr hκ
  obtain ⟨s, hs, hc⟩ := Cardinal.le_mk_iff_exists_subset.mp h
  let A := x.sep (fun y => y ∈ s)
  have hA : (A : Set ZFSet.{u}) = s := by
    ext y
    change y ∈ x.sep (fun z => z ∈ s) ↔ y ∈ s
    rw [ZFSet.mem_sep]
    exact ⟨And.right, fun hy => ⟨hs hy, hy⟩⟩
  refine ⟨A, ZFSet.sep_subset, ?_⟩
  apply Cardinal.lift_inj.{u, u + 1}.mp
  rw [← ZFSet.cardinalMk_coe_sort]
  change Cardinal.mk (A : Set ZFSet.{u}) = Cardinal.lift κ
  rw [hA, hc]

namespace SetModel

variable {L : FirstOrder.Language.{u, u}} {M N : SetModel L}

theorem Submodel.carrier_subset (h : M.Submodel N) : M.carrier ⊆ N.carrier := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hmem := (e ⟨x, hx⟩).property
  simpa only [he ⟨x, hx⟩] using hmem

theorem Submodel.card_le (h : M.Submodel N) : M.card ≤ N.card :=
  ZFSet.card_mono h.carrier_subset

theorem Submodel.of_carrier_subset {P : SetModel L}
    (hMP : M.Submodel P) (hNP : N.Submodel P) (hMN : M.carrier ⊆ N.carrier) :
    M.Submodel N := by
  obtain ⟨e, he⟩ := hMP
  obtain ⟨f, hf⟩ := hNP
  let i : M.carrier → N.carrier := fun x => ⟨x.val, hMN x.property⟩
  have hfi : (f : N.carrier → P.carrier) ∘ i = e := by
    funext x
    apply Subtype.ext
    exact (hf (i x)).trans (he x).symm
  refine ⟨{ toFun := i, inj' := ?_, map_fun' := ?_, map_rel' := ?_ }, fun _ => rfl⟩
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : N.carrier => z.val) h
  · intro n g x
    apply f.injective
    change (f ∘ i) (Language.Structure.funMap g x) =
      f (Language.Structure.funMap g (i ∘ x))
    rw [hfi, f.map_fun, e.map_fun, ← Function.comp_assoc, hfi]
  · intro n r x
    rw [← f.map_rel r (i ∘ x), ← Function.comp_assoc, hfi, e.map_rel]

end SetModel

namespace AEC

variable {L : FirstOrder.Language.{u, u}} (K : AEC L)

theorem strong_of_carrier_subset {A B M : SetModel L}
    (hAM : K.strong A M) (hBM : K.strong B M) (hAB : A.carrier ⊆ B.carrier) :
    K.strong A B :=
  K.coherence ((K.submodel hAM).of_carrier_subset (K.submodel hBM) hAB) hAM hBM

theorem exists_small_strong_submodel (M : SetModel L) (hM : K.mem M)
    (A : ZFSet.{u}) (hA : A ⊆ M.carrier) {κ : Cardinal.{u}}
    (hLS : K.LS ≤ κ) (hAκ : A.card ≤ κ) :
    ∃ N, K.strong N M ∧ A ⊆ N.carrier ∧ N.card ≤ κ := by
  obtain ⟨N, hNM, hAN, hN⟩ := K.LS_bound M hM A hA
  exact ⟨N, hNM, hAN,
    hN.trans (Cardinal.add_le_of_le (K.LS_infinite.trans hLS) hAκ hLS)⟩

theorem small_strong_submodels_directed {A B M : SetModel L}
    (hAM : K.strong A M) (hBM : K.strong B M) {κ : Cardinal.{u}}
    (hLS : K.LS ≤ κ) (hAκ : A.card ≤ κ) (hBκ : B.card ≤ κ) :
    ∃ N, K.strong N M ∧ K.strong A N ∧ K.strong B N ∧ N.card ≤ κ := by
  have hAB : A.carrier ∪ B.carrier ⊆ M.carrier := by
    intro x hx
    rcases ZFSet.mem_union.mp hx with hx | hx
    · exact (K.submodel hAM).carrier_subset hx
    · exact (K.submodel hBM).carrier_subset hx
  have hABκ : (A.carrier ∪ B.carrier).card ≤ κ :=
    ZFSet.card_union_le.trans
      (Cardinal.add_le_of_le (K.LS_infinite.trans hLS) hAκ hBκ)
  obtain ⟨N, hNM, hABN, hN⟩ := K.exists_small_strong_submodel M
    (K.strong_mem hAM).2 (A.carrier ∪ B.carrier) hAB hLS hABκ
  exact ⟨N, hNM,
    K.strong_of_carrier_subset hAM hNM (fun _ hx => hABN (ZFSet.mem_union.mpr (.inl hx))),
    K.strong_of_carrier_subset hBM hNM (fun _ hx => hABN (ZFSet.mem_union.mpr (.inr hx))),
    hN⟩

theorem small_strong_submodels_cover (M : SetModel L) (hM : K.mem M)
    {x : ZFSet.{u}} (hx : x ∈ M.carrier) :
    ∃ N, K.strong N M ∧ x ∈ N.carrier ∧ N.card ≤ K.LS := by
  obtain ⟨N, hNM, hxN, hN⟩ := K.exists_small_strong_submodel M hM {x}
    (by
      intro y hy
      have hyx : y = x := ZFSet.mem_singleton.mp hy
      simpa only [hyx] using hx) le_rfl
    (by simpa using Cardinal.one_le_aleph0.trans K.LS_infinite)
  exact ⟨N, hNM, hxN (by simp), hN⟩

theorem exists_strong_submodel_card_containing (M : SetModel L) (hM : K.mem M)
    (A : ZFSet.{u}) (hA : A ⊆ M.carrier) {κ : Cardinal.{u}}
    (hLS : K.LS ≤ κ) (hAκ : A.card ≤ κ) (hκM : κ ≤ M.card) :
    ∃ N, K.strong N M ∧ A ⊆ N.carrier ∧ N.card = κ := by
  obtain ⟨B, hB, hBc⟩ := exists_subset_card M.carrier hκM
  have hAB : A ∪ B ⊆ M.carrier := by
    intro x hx
    rcases ZFSet.mem_union.mp hx with hx | hx
    · exact hA hx
    · exact hB hx
  obtain ⟨N, hNM, hABN, hNc⟩ := K.LS_bound M hM (A ∪ B) hAB
  have hinf : ℵ₀ ≤ κ := K.LS_infinite.trans hLS
  have hABc : (A ∪ B).card ≤ κ :=
    (ZFSet.card_union_le).trans (Cardinal.add_le_of_le hinf hAκ hBc.le)
  have hNle : N.card ≤ κ :=
    hNc.trans (Cardinal.add_le_of_le hinf hABc hLS)
  have hBN : B ⊆ N.carrier := by
    intro x hx
    exact hABN (ZFSet.mem_union.mpr (Or.inr hx))
  have hNge : κ ≤ N.card := by
    rw [← hBc]
    exact ZFSet.card_mono hBN
  refine ⟨N, hNM, ?_, hNle.antisymm hNge⟩
  intro x hx
  exact hABN (ZFSet.mem_union.mpr (Or.inl hx))

theorem exists_strong_submodel_card (M : SetModel L) (hM : K.mem M)
    {κ : Cardinal.{u}} (hLS : K.LS ≤ κ) (hκM : κ ≤ M.card) :
    ∃ N, K.strong N M ∧ N.card = κ := by
  obtain ⟨N, hNM, _, hN⟩ := K.exists_strong_submodel_card_containing M hM
    ∅ (ZFSet.empty_subset _) hLS (by simp) hκM
  exact ⟨N, hNM, hN⟩

theorem arbitrarily_large_models (hK : K.UnboundedCategoricity) (κ : Cardinal.{u}) :
    ∃ M, K.mem M ∧ κ ≤ M.card := by
  obtain ⟨ρ, hκρ, ⟨M, hM, hc⟩, _⟩ := hK κ
  exact ⟨M, hM, hc ▸ hκρ⟩

theorem models_at_every_cardinal_above_LS (hK : K.UnboundedCategoricity)
    {κ : Cardinal.{u}} (hLS : K.LS ≤ κ) :
    ∃ M, K.mem M ∧ M.card = κ := by
  obtain ⟨M, hM, hκM⟩ := K.arbitrarily_large_models hK κ
  obtain ⟨N, hNM, hN⟩ := K.exists_strong_submodel_card M hM hLS hκM
  exact ⟨N, (K.strong_mem hNM).1, hN⟩

theorem contains_copy_at_categorical_cardinal {ρ : Cardinal.{u}}
    (hρ : K.Categorical ρ) (hLS : K.LS ≤ ρ)
    (C M : SetModel L) (hC : K.mem C) (hCc : C.card = ρ) (hM : K.mem M)
    (hρM : ρ ≤ M.card) :
    ∃ N, K.strong N M ∧ N.card = ρ ∧ Nonempty (C.carrier ≃[L] N.carrier) := by
  obtain ⟨N, hNM, hN⟩ := K.exists_strong_submodel_card M hM hLS hρM
  exact ⟨N, hNM, hN, hρ.2 C N hC (K.strong_mem hNM).1 hCc hN⟩

end AEC
end EventualCategoricity

end OAI
