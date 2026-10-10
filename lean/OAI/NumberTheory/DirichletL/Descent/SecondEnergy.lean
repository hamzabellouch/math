import OAI.NumberTheory.DirichletL.Inversion.SecondFibers
import OAI.NumberTheory.DirichletL.Descent.InitializationEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev SecondChild := OuterTriple × Ideal Eis × Eis

def secondChild {Jo Jn : ℕ} (x : SecondTuple Jo Jn) : SecondChild :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency)

def secondDivisorWeight (K : ℕ) (c : SecondChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4*K) *
    ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2*K) *
    ((idealDivisors c.1.quotient).card : ℝ) ^ (2*K) *
    ((idealDivisors c.1.residual).card : ℝ) ^ (2*K)

theorem secondChild_eq_iff_valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (hx : Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) : secondChild x = c ↔ Valid x c.1 c.2.1 c.2.2 := by
  constructor
  · intro he
    simpa only [he] using hx
  · intro hv
    apply Prod.ext hv.outer_eq
    exact Prod.ext hv.label hv.row_eq

theorem secondChild_fiber_weight {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) (hf : c.2.1 ≠ 0) (hq : c.1.q0 ≠ 0)
    (ht : c.1.quotient ≠ 0) (hr : c.1.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1) :
    (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
      secondDivisorWeight K c := by
  have hfilter : (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c) =
      secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2 := by
    apply Finset.filter_congr
    intro x hx
    exact secondChild_eq_iff_valid x (hvalid x hx) c
  calc
    _ ≤ ∑ _x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2).card : ℝ) := by rw [hfilter]; simp
    _ ≤ secondDivisorWeight K c := by
      have hh := secondFiber_card_le source oldLists newLists keep c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
      dsimp only [secondDivisorWeight]
      exact_mod_cast hh

theorem second_energy_projection {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1)
    (F : SecondChild → ℂ) :
    (∑ x ∈ originalSource source oldLists newLists keep, w x * ‖F (secondChild x)‖ ^ 2) ≤
      ∑ γ ∈ sourceTriples source oldLists newLists keep,
        ((idealDivisors γ.q0).card : ℝ) ^ (5 + 2*K) *
        ((idealDivisors γ.quotient).card : ℝ) ^ (2*K) *
        ((idealDivisors γ.residual).card : ℝ) ^ (2*K) *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (9 + 4*K) *
          ∑ k ∈ rows, ‖F (γ, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ originalSource source oldLists newLists keep,
      secondChild x ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows),
      (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
        secondDivisorWeight K c := by
    intro c hc
    obtain ⟨hγ, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨hq, ht, hr⟩ := houter c.1 hγ
    exact secondChild_fiber_weight source oldLists newLists keep hvalid c
      (hf c.2.1 (Finset.mem_product.mp hfk).1) hq ht hr K ho hn w hw
  have he := fiber_energy_bound (originalSource source oldLists newLists keep)
    (sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows)) secondChild w
    (secondDivisorWeight K) (fun c => ‖F c‖ ^ 2) hmaps (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, secondDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hfm
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
