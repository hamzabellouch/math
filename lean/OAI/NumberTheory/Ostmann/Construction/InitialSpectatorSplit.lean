import OAI.NumberTheory.Ostmann.Construction.SelectedInitialPriorBounds
import OAI.NumberTheory.Ostmann.Construction.FiniteFormulaRenaming

namespace OAI

/-! # Separating the original spectator coordinates without changing their law -/
namespace Ostmann
open scoped Classical BigOperators

/-- In one original half-list, separate the spectator block from the giant,
bulk and fixed cell blocks. -/
def initialSpectatorSlotEquiv (b d r : ℕ) :
    Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r)) ≃ Fin (b + (d + r) + 1) where
  toFun
    | .inl i => ((i.castAdd r).natAdd b).succ
    | .inr (.inl _) => 0
    | .inr (.inr (.inl i)) => (i.castAdd (d + r)).succ
    | .inr (.inr (.inr i)) => ((i.natAdd d).natAdd b).succ
  invFun := Fin.cases (.inr (.inl ())) (fun j =>
    Fin.addCases (fun i => .inr (.inr (.inl i)))
      (fun j => Fin.addCases (fun i => .inl i) (fun i => .inr (.inr (.inr i))) j) j)
  left_inv := by
    intro i
    rcases i with i | (i | (i | i)) <;> simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

noncomputable def initialHalfAssemble {P : Type*} (b d r : ℕ)
    (spectator : Fin d → P) (retained : Unit ⊕ (Fin b ⊕ Fin r) → P) :
    Fin (b + (d + r) + 1) → P :=
  Sum.elim spectator retained ∘ (initialSpectatorSlotEquiv b d r).symm

theorem initialHalfAssemble_spectator {P : Type*} (b d r : ℕ)
    (spectator : Fin d → P) (retained : Unit ⊕ (Fin b ⊕ Fin r) → P) (i : Fin d) :
    initialHalfAssemble b d r spectator retained ((i.castAdd r).natAdd b).succ = spectator i := by
  change (Sum.elim spectator retained)
    ((initialSpectatorSlotEquiv b d r).symm (initialSpectatorSlotEquiv b d r (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem initial_doubled_spectators_injective {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (yl yr : Unit ⊕ (Fin b ⊕ Fin r) → P)
    (h : Function.Injective (Fin.append (initialHalfAssemble b d r sl yl)
      (initialHalfAssemble b d r sr yr))) : Function.Injective (Fin.append sl sr) := by
  obtain ⟨hl, hr, hcross⟩ := Fin.append_injective_iff.mp h
  apply Fin.append_injective_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have he := hl (show initialHalfAssemble b d r sl yl ((i.castAdd r).natAdd b).succ =
        initialHalfAssemble b d r sl yl ((j.castAdd r).natAdd b).succ by
      simpa only [initialHalfAssemble_spectator] using hij)
    have hh : (Sum.inl i : Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r))) = Sum.inl j :=
      (initialSpectatorSlotEquiv b d r).injective he
    exact Sum.inl.inj hh
  · intro i j hij
    have he := hr (show initialHalfAssemble b d r sr yr ((i.castAdd r).natAdd b).succ =
        initialHalfAssemble b d r sr yr ((j.castAdd r).natAdd b).succ by
      simpa only [initialHalfAssemble_spectator] using hij)
    have hh : (Sum.inl i : Fin d ⊕ (Unit ⊕ (Fin b ⊕ Fin r))) = Sum.inl j :=
      (initialSpectatorSlotEquiv b d r).injective he
    exact Sum.inl.inj hh
  · intro i j hij
    apply hcross ((i.castAdd r).natAdd b).succ ((j.castAdd r).natAdd b).succ
    simpa only [initialHalfAssemble_spectator] using hij

theorem initial_half_prior_split {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : (Fin (b + (d + r) + 1) → P) → ℂ) :
    (∑ x, (productPrior (Fin.cons μg (Fin.append μb (Fin.append μd μc))) x : ℂ) * F x) =
      ∑ s : Fin d → P, (productPrior μd s : ℂ) *
        ∑ y : Unit ⊕ (Fin b ⊕ Fin r) → P,
          ((∏ i, (Sum.elim (fun _ => μg) (Sum.elim μb μc)) i (y i) : ℝ) : ℂ) *
            F (initialHalfAssemble b d r s y) := by
  let ν : Fin (b + (d + r) + 1) → P → ℝ :=
    Fin.cons μg (Fin.append μb (Fin.append μd μc))
  have he := finite_prior_reindex (initialSpectatorSlotEquiv b d r) ν F
  change (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) = _
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  let e := Equiv.sumArrowEquivProdArrow (Fin d) (Unit ⊕ (Fin b ⊕ Fin r)) P
  have hsplit := e.symm.sum_comp (fun x =>
    ((∏ i, ν (initialSpectatorSlotEquiv b d r i) (x i) : ℝ) : ℂ) *
      F (x ∘ (initialSpectatorSlotEquiv b d r).symm))
  rw [Fintype.sum_prod_type] at hsplit
  simp only [finite_univ_canonical] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have heval : e.symm (s, y) = Sum.elim s y := rfl
  rw [heval]
  rw [← mul_assoc]
  congr 1
  have hprod := Fintype.prod_sum_type (fun i =>
    ν (initialSpectatorSlotEquiv b d r i) ((Sum.elim s y) i))
  simp only [finite_univ_canonical] at hprod
  rw [hprod]
  have hleft : (∏ i : Fin d, ν (initialSpectatorSlotEquiv b d r (.inl i)) (s i)) =
      productPrior μd s := by
    apply Finset.prod_congr rfl
    intro i _
    simp [ν, initialSpectatorSlotEquiv]
  have hright : (∏ i : Unit ⊕ (Fin b ⊕ Fin r),
      ν (initialSpectatorSlotEquiv b d r (.inr i)) (y i)) =
      ∏ i, (Sum.elim (fun _ => μg) (Sum.elim μb μc)) i (y i) := by
    apply Finset.prod_congr rfl
    intro i _
    rcases i with i | (i | i) <;> simp [ν, initialSpectatorSlotEquiv]
  simp only [finite_univ_canonical] at hleft hright
  simp only [Sum.elim_inl, Sum.elim_inr, hleft, hright, Complex.ofReal_mul]

def initialTwoHalfTupleEquiv (P : Type*) (n : ℕ) :
    (Fin n → P) × (Fin n → P) ≃ (Fin (n + n) → P) where
  toFun x := Fin.append x.1 x.2
  invFun x := (fun i => x (i.castAdd n), fun i => x (Fin.natAdd n i))
  left_inv := by
    intro x
    apply Prod.ext <;> funext i
    · exact Fin.append_left x.1 x.2 i
    · exact Fin.append_right x.1 x.2 i
  right_inv := by intro x; exact Fin.append_castAdd_natAdd

theorem initial_two_half_average {P : Type*} [Fintype P] (n : ℕ)
    (μ : Fin n → P → ℝ) (F : (Fin (n + n) → P) → ℂ) :
    (∑ x, (productPrior (Fin.append μ μ) x : ℂ) * F x) =
      ∑ l : Fin n → P, (productPrior μ l : ℂ) *
        ∑ r : Fin n → P, (productPrior μ r : ℂ) * F (Fin.append l r) := by
  rw [← (initialTwoHalfTupleEquiv P n).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [initialTwoHalfTupleEquiv, Equiv.coe_fn_mk, productPrior, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Complex.ofReal_mul, mul_assoc]

private theorem initial_complex_average_swap {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℂ) (b : J → ℂ) (F : I → J → ℂ) :
    (∑ i, a i * ∑ j, b j * F i j) = ∑ j, b j * ∑ i, a i * F i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem initial_doubled_prior_split {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) :
    let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    let νr := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
    (∑ x, (productPrior (Fin.append ν ν) x : ℂ) * F x) =
      ∑ sl : Fin d → P, (productPrior μd sl : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
            ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
              F (Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)) := by
  intro ν νr
  rw [initial_two_half_average]
  rw [initial_half_prior_split]
  apply Finset.sum_congr rfl
  intro sl _
  congr 1
  calc
    _ = ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
            F (Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)) := by
      apply Finset.sum_congr rfl
      intro yl _
      congr 1
      exact initial_half_prior_split b d r μg μb μd μc _
    _ = _ := initial_complex_average_swap _ _ _

end Ostmann

end OAI
