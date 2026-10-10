import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeMatrix
import OAI.NumberTheory.SiegelZeros.Structure.RealCutoff

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W28

open WeightedTorusJets.W18 WeightedTorusJets.W19
open scoped BigOperators

variable {K : Type*} [Field K]

theorem coefficientPolynomial_inBox (N : ℕ) (c : MonomialBox N → K) :
    InBox N (coefficientPolynomial boxExponent c) := by
  classical
  intro e he i
  by_contra hi
  have hne : ∀ n : MonomialBox N, boxExponent n ≠ e := by
    intro n hn
    apply hi
    have hh := congrArg (fun f : Fin 4 →₀ ℕ => f i) hn
    change (n i).val = e i at hh
    rw [← hh]
    exact (n i).isLt
  apply (MvPolynomial.mem_support_iff.mp he)
  simp [coefficientPolynomial, MvPolynomial.coeff_monomial, hne]

def RectangularAssertion (v : Fin 3 → Fin 4 → K) (H N : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin 4) K, InBox N p →
    (∀ a : Fin 3 → ℕ,
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) →
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
      MvPolynomial.eval (fun _ => (1 : K)) (mixedInvariant v a p) = 0) → p = 0

noncomputable def sourceCutoff (H N : ℕ) : ℕ :=
  ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊

noncomputable def sourceRow (v : Fin 3 → Fin 4 → K) (H N : ℕ)
    (a : W62.Index H) (n : MonomialBox N) : K :=
  eigenvalue (v 0) (boxExponent n) ^ a.coords 0 *
    eigenvalue (v 1) (boxExponent n) ^ a.coords 1 *
    eigenvalue (v 2) (boxExponent n) ^ a.coords 2

theorem cutoff_span_of_rectangularAssertion (v : Fin 3 → Fin 4 → K)
    {H N : ℕ} (hH : 0 < H) (hrect : RectangularAssertion v H N) :
    W29.rowSpan (K := K) (sourceRow v H N) (W62.cutoff H (sourceCutoff H N)) = ⊤ := by
  classical
  let S := W62.cutoff H (sourceCutoff H N)
  let a : S → Fin 3 → ℕ := fun r => r.val.coords
  have hm : Submodule.span K
      (Set.range (derivativeMatrix v (boxExponent (N := N)) a).row) = ⊤ := by
    apply (actual_jet_annihilation_iff_rowSpan v _ (boxExponent_injective N) a).mp
    intro c hc
    apply hrect _ (coefficientPolynomial_inBox N c)
    intro b h0 h1 h2
    have hb : (W62.Index.mk b : W62.Index H) ∈ S :=
      W62.rectangle_mem_cutoff hH (by positivity) (W62.Index.mk b) h0 h1 h2
    exact hc ⟨W62.Index.mk b, hb⟩
  have hr : Set.range (derivativeMatrix v (boxExponent (N := N)) a).row =
      sourceRow v H N '' (S : Set (W62.Index H)) := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.val, r.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [hr] at hm
  exact hm

theorem selected_card_of_rectangularAssertion (v : Fin 3 → Fin 4 → K)
    {H N : ℕ} (hH : 0 < H) (hrect : RectangularAssertion v H N) :
    Fintype.card (W62.selected (K := K) H (sourceCutoff H N) (sourceRow v H N)) = N ^ 4 := by
  have h := W62.selected_card_of_spanning H (sourceCutoff H N) (sourceRow v H N)
    (cutoff_span_of_rectangularAssertion v hH hrect)
  simpa [MonomialBox, Fintype.card_fun] using h

theorem source_selected_weight_le (v : Fin 3 → Fin 4 → K)
    {H N : ℕ} (hH : 0 < H) {a : W62.Index H}
    (ha : a ∈ W62.selected (K := K) H (sourceCutoff H N) (sourceRow v H N)) :
    SiegelZerosAwei.W31.weight (H : ℝ) a.coords ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  rw [W62.real_weight_eq]
  have hw := W62.selected_weight_le hH (sourceRow v H N) ha
  have hc : (W62.weight a : ℝ) ≤ (sourceCutoff H N : ℝ) := by exact_mod_cast hw
  exact hc.trans (Nat.floor_le (by positivity))

theorem selected_det_of_rectangularAssertion (v : Fin 3 → Fin 4 → K)
    {H N : ℕ} (hH : 0 < H) (hrect : RectangularAssertion v H N) :
    ∃ e : MonomialBox N ≃
      W62.selected (K := K) H (sourceCutoff H N) (sourceRow v H N),
      Matrix.det (fun i j => sourceRow v H N (e i) j) ≠ 0 := by
  exact W62.selected_det_ne_zero_of_spanning H (sourceCutoff H N) (sourceRow v H N)
    (cutoff_span_of_rectangularAssertion v hH hrect)

end WeightedTorusJets.W28


end SiegelZeros

end OAI
