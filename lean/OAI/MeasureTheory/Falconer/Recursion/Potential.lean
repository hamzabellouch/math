import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

namespace PlanarFalconer
open Finset

noncomputable def finiteMin {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

theorem le_finiteMin {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {c : ℝ} (h : ∀ i ∈ s, c ≤ f i) : c ≤ finiteMin s f := by
  rw [finiteMin, dite_eq_left hs]
  exact Finset.le_inf' hs f h

def depthPairs (a t Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc a t) ×ˢ (Finset.Icc a t)).filter fun z => z.1 < z.2 ∧ Q ≤ z.2 - z.1

@[simp] theorem mem_depthPairs {a t Q i j : ℕ} :
    (i,j) ∈ depthPairs a t Q ↔ a ≤ i ∧ i < j ∧ j ≤ t ∧ i + Q ≤ j := by
  simp only [depthPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

theorem depthPairs_nonempty {a t Q : ℕ} (hQ : 0 < Q) (hw : a + Q ≤ t) :
    (depthPairs a t Q).Nonempty := by
  refine ⟨(a,a+Q), mem_depthPairs.mpr ?_⟩
  omega

noncomputable def potential (A : ℕ → ℝ) (a t Q : ℕ) : ℝ :=
  finiteMin (depthPairs a t Q) fun z => A z.1 + A z.2

theorem potential_le (A : ℕ → ℝ) {a t Q i j : ℕ}
    (hi : a ≤ i) (hij : i < j) (hjt : j ≤ t) (hgap : i + Q ≤ j) :
    potential A a t Q ≤ A i + A j :=
  finiteMin_le _ (mem_depthPairs.mpr ⟨hi,hij,hjt,hgap⟩)

theorem le_potential (A : ℕ → ℝ) {a t Q : ℕ} (hQ : 0 < Q)
    (hw : a+Q ≤ t) {c : ℝ}
    (h : ∀ i j, a ≤ i → i < j → j ≤ t → i+Q ≤ j → c ≤ A i + A j) :
    c ≤ potential A a t Q := by
  apply le_finiteMin (depthPairs_nonempty hQ hw)
  rintro ⟨i,j⟩ hij
  obtain ⟨hi, hij, hjt, hgap⟩ := mem_depthPairs.mp hij
  exact h i j hi hij hjt hgap

theorem potential_mono (A : ℕ → ℝ) {a b u t Q : ℕ}
    (hQ : 0 < Q) (hw : b+Q ≤ u) (hab : a ≤ b) (hut : u ≤ t) :
    potential A a t Q ≤ potential A b u Q := by
  apply le_potential A hQ hw
  intro i j hbi hij hju hgap
  exact potential_le A (hab.trans hbi) hij (hju.trans hut) hgap

theorem prefix_payment (A : ℕ → ℝ) {a p v t Q i₀ : ℕ}
    (hQ : 0 < Q) (hw : p+Q ≤ v) (hai : a ≤ i₀) (hip : i₀ ≤ p)
    (hvt : v ≤ t) (hcontrolled : ∀ i, p ≤ i → i+Q ≤ v → A p ≤ A i) :
    potential A a t Q + (A p - A i₀) ≤ potential A p v Q := by
  apply le_potential A hQ hw
  intro i j hpi hij hjv hgap
  have hparent := potential_le A hai (by omega : i₀ < j) (by omega : j ≤ t)
    (by omega : i₀+Q ≤ j)
  have hAi := hcontrolled i hpi (by omega)
  linarith

theorem suffix_payment (A : ℕ → ℝ) {a p t Q j₀ : ℕ}
    (hQ : 0 < Q) (hw : a+Q ≤ p) (hpj : p ≤ j₀) (hjt : j₀ ≤ t)
    (hcontrolled : ∀ j, a+Q ≤ j → j ≤ p → A p ≤ A j) :
    potential A a t Q + (A p - A j₀) ≤ potential A a p Q := by
  apply le_potential A hQ hw
  intro i j hai hij hjp hgap
  have hparent := potential_le A hai (by omega : i < j₀) hjt
    (by omega : i+Q ≤ j₀)
  have hAj := hcontrolled j (by omega) hjp
  linarith

theorem direct_origin_payment (A : ℕ → ℝ) {a p v b u l r L q Q i₀ : ℕ}
    (hq : 0 < q) (hQ : Q = 10*q) (hw : p+Q ≤ v)
    (hai : a ≤ i₀) (hip : i₀ ≤ p) (hlp : l ≤ p) (hpr : p ≤ r)
    (hl : l ≤ b+2*q) (hr : u ≤ r+2*q) (hLu : b+2*L ≤ u)
    (hv : v ≤ a+2*L) (hmin : A i₀ < A p)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v Q + (A p - A i₀) ≤ potential A p v Q := by
  have hi₀l : i₀ < l := by
    by_contra h
    have := hinner i₀ (by omega) (by omega)
    linarith
  apply prefix_payment A (by omega) hw hai hip (le_refl v)
  intro i hpi hiQ
  apply hinner i (by omega) (by omega)

theorem potential_lower (A : ℕ → ℝ) {a t Q : ℕ} (hQ : 0 < Q)
    (hw : a+Q ≤ t) {b : ℝ} (h : ∀ i, a ≤ i → i ≤ t → b ≤ A i) :
    2*b ≤ potential A a t Q := by
  apply le_potential A hQ hw
  intro i j hai hij hjt hgap
  have hi := h i hai (by omega)
  have hj := h j (by omega) hjt
  linarith

end PlanarFalconer

end OAI
