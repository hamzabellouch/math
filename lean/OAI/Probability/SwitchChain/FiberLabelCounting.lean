import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.FiberLabelCounting

variable {V C : Type*} [sectionFintypeV : Fintype V] [sectionFintypeC : Fintype C]

abbrev PrescribedFiberColorings (k : C → ℕ) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c}

abbrev EqualFiberColorings (f₀ : V → C) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c}}

abbrev LabeledFibers (f₀ : V → C) :=
  Σ g : EqualFiberColorings f₀, ∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}

include sectionFintypeV sectionFintypeC in
private theorem ofFiberEquiv_apply_subtype {f g : V → C}
    (e : ∀ c, {v // f v = c} ≃ {v // g v = c}) (c : C) (v : {v // f v = c}) :
    Equiv.ofFiberEquiv e v.val = (e c v).val := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeC := sectionFintypeC
  rcases v with ⟨v, hv⟩
  subst c
  rfl

def labeledFibersEquivPerm (f₀ : V → C) : LabeledFibers f₀ ≃ Equiv.Perm V := by
  let F : LabeledFibers f₀ → Equiv.Perm V := fun a => Equiv.ofFiberEquiv a.2
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨⟨g, hg⟩, e⟩ ⟨⟨h, hh⟩, f⟩ hp
    change Equiv.ofFiberEquiv e = Equiv.ofFiberEquiv f at hp
    have hgh : g = h := by
      funext y
      obtain ⟨x, rfl⟩ := (Equiv.ofFiberEquiv e).surjective y
      have hx := Equiv.ofFiberEquiv_map e x
      have hy := Equiv.ofFiberEquiv_map f x
      rw [← hp] at hy
      exact hx.trans hy.symm
    subst h
    have hef : e = f := by
      funext c
      apply Equiv.ext
      intro v
      apply Subtype.ext
      rw [← ofFiberEquiv_apply_subtype e c v, ← ofFiberEquiv_apply_subtype f c v]
      exact congrArg (fun p : Equiv.Perm V => p v.val) hp
    subst f
    rfl
  · intro p
    let g : V → C := fun v => f₀ (p.symm v)
    let e (c : C) : {v // f₀ v = c} ≃ {v // g v = c} :=
      { toFun := fun v => ⟨p v.val, by simpa [g] using v.property⟩
        invFun := fun v => ⟨p.symm v.val, v.property⟩
        left_inv := by intro v; apply Subtype.ext; simp
        right_inv := by intro v; apply Subtype.ext; simp }
    have hg : ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c} :=
      fun c => (Fintype.card_congr (e c)).symm
    refine ⟨⟨⟨g, hg⟩, e⟩, ?_⟩
    apply Equiv.ext
    intro v
    rfl

theorem equalFiberColorings_card_mul_factorials (f₀ : V → C) :
    Fintype.card (EqualFiberColorings f₀) *
      (∏ c, (Fintype.card {v // f₀ v = c}).factorial) = (Fintype.card V).factorial := by
  have he (g : EqualFiberColorings f₀) :
      Fintype.card (∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}) =
        ∏ c, (Fintype.card {v // f₀ v = c}).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro c _
    exact Fintype.card_equiv (Fintype.equivOfCardEq (g.property c).symm)
  have hd : Fintype.card (LabeledFibers f₀) =
      Fintype.card (EqualFiberColorings f₀) *
        (∏ c, (Fintype.card {v // f₀ v = c}).factorial) := by
    rw [Fintype.card_sigma]
    simp_rw [he]
    simp
  rw [← hd, Fintype.card_congr (labeledFibersEquivPerm f₀), Fintype.card_perm]

theorem prescribedFiberColorings_nonempty (k : C → ℕ)
    (hk : ∑ c, k c = Fintype.card V) :
    Nonempty (PrescribedFiberColorings (V := V) k) := by
  have hc : Fintype.card V = Fintype.card (Σ c, Fin (k c)) := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hk.symm
  let e : V ≃ (Σ c, Fin (k c)) := Fintype.equivOfCardEq hc
  let g : V → C := fun v => (e v).1
  refine ⟨⟨g, fun c => ?_⟩⟩
  let ef : {v // g v = c} ≃ Fin (k c) :=
    (e.subtypeEquiv (fun v => Iff.rfl)).trans (Equiv.sigmaSubtype c)
  exact (Fintype.card_congr ef).trans (Fintype.card_fin (k c))

theorem prescribedFiberColorings_card_mul_factorials (k : C → ℕ)
    (hne : Nonempty (PrescribedFiberColorings (V := V) k)) :
    Fintype.card (PrescribedFiberColorings (V := V) k) *
      (∏ c, (k c).factorial) = (Fintype.card V).factorial := by
  obtain ⟨⟨f₀, hf₀⟩⟩ := hne
  let e : {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c} ≃
      EqualFiberColorings f₀ :=
    Equiv.subtypeEquivRight (fun g => by simp only [hf₀])
  have h := equalFiberColorings_card_mul_factorials f₀
  rw [Fintype.card_congr e]
  simpa only [hf₀] using h

end Problem315.FiberLabelCounting

end

end OAI
