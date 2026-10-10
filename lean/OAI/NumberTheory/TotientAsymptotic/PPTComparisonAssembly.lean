import OAI.NumberTheory.TotientAsymptotic.PPTCancelCoordinates
import OAI.NumberTheory.TotientAsymptotic.PPTLargePart
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonSum

namespace OAI

/-!
Assemble the pointwise conditions in Ford's comparison estimate after
the actual matched coordinates have been removed.  The right residual
is an integer multiplier in the shifted-product equation; no additional
representation of that multiplier as a totient is required.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptCanceledPair {k : ℕ} (p q : Fin k → ℕ) (E : ℕ) :
    ShiftedPair (pptUnequalCoordinates p q).card :=
  ⟨p ∘ pptCoordinateEmbedding p q, q ∘ pptCoordinateEmbedding p q, E⟩

/-- The comparison conditions follow from the actual shifted-product
identity, target squarefreeness, and the enclosing grid intervals.  The
large leading part is proved from normality and the head size. -/
theorem ppt_canceled_comparison_conditions : ∀ᶠ z : ℝ in atTop,
    ∀ (k D E : ℕ) (p q : Fin k → ℕ) (S : ℝ) (Y U : ℕ → ℝ),
      ∀ hk : 0 < k,
      1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, IsNormalPrime S (q i)) →
      Function.Injective p → p ⟨0,hk⟩ ≠ q ⟨0,hk⟩ →
      0 < E → D*shiftedProduct p = E*shiftedProduct q →
      ((D*shiftedProduct p : ℕ) : ℝ) ≤ z →
      SquarefreeAbove (D*shiftedProduct p) (Y (pptUnequalCoordinates p q).card) →
      (largestPrimeFactor E : ℝ) ≤ Y (pptUnequalCoordinates p q).card →
      (∀ i : Fin (pptUnequalCoordinates p q).card,
        U i ≤ largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1) ∧
        (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1) : ℝ) ≤ Y i ∧
        U i ≤ largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1) ∧
        (largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1) : ℝ) ≤ Y i) →
      z^(9/10 : ℝ) ≤ p ⟨0,hk⟩ → (p ⟨0,hk⟩-1 : ℕ) ≤ z →
      1 ≤ Y 1 → Y 1 ≤ z^(1/(10*B z)) →
      FordComparisonConditions (pptUnequalCoordinates p q).card z S D
        (pptCanceledPrimeProduct p q).totient Y U (pptCanceledPair p q E) := by
  filter_upwards [ppt_normal_comparison_large_part] with z hlarge
  intro k D E p q S Y U hk hS hBS hSz hp hq hpinj hfirst hE heq hsize hsq hEs
    hinterval hhead hpz hY hYpower
  have hprime : ∀ i, (p i).Prime := fun i => (hp i).1
  have hcancel := ppt_cancel_matching_coordinates p q hprime heq
  have hshiftdiv : shiftedProduct (p ∘ pptCoordinateEmbedding p q) ∣ shiftedProduct p := by
    rw [← ppt_canceled_totient_split p q hprime hpinj]
    exact dvd_mul_left _ _
  have hsqd : SquarefreeAbove (D*shiftedProduct (p ∘ pptCoordinateEmbedding p q))
      (Y (pptUnequalCoordinates p q).card) :=
    squarefreeAbove_of_dvd (Nat.mul_dvd_mul_left D hshiftdiv) hsq
  refine ⟨hE, ?_, hcancel, ppt_canceled_comparison_size p q hprime hpinj hsize,
    hEs, ?_, ?_⟩
  · intro i
    have hsides := squarefree_shifts_of_common_product (pptCanceledPair p q E)
      (Y (pptUnequalCoordinates p q).card) hcancel hsqd i
    have hi := hinterval i
    exact ⟨hp _, hq _, ppt_surviving_coordinates_unequal p q i,
      hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, hsides.1, hsides.2⟩
  · intro hb
    obtain ⟨hb', hzero⟩ := ppt_coordinate_first_survives hk p q hfirst
    have hzero' : pptCoordinateEmbedding p q ⟨0,hb⟩ = ⟨0,hk⟩ := by
      simpa only using hzero
    change Real.sqrt z < (partAbove (p (pptCoordinateEmbedding p q ⟨0,hb⟩)-1) (Y 1) : ℝ)
    rw [hzero']
    exact hlarge (p ⟨0,hk⟩) S (Y 1) hS hBS hSz (hp ⟨0,hk⟩) hhead hpz hY hYpower
  · exact squarefreeAbove_of_dvd (dvd_mul_left _ _) hsqd

/-- Left-list recovery alone proves injectivity of a fixed comparison
block, even when its right residual is supplied directly as an integer. -/
lemma ppt_plain_comparison_injective {b c a : ℕ} (T : Finset ℕ)
    (t : ℕ → ShiftedPair b)
    (hreal : ∀ n ∈ T, n = c*a*∏ i, (t n).left i) :
    Set.InjOn t (T : Set ℕ) := by
  intro n hn m hm he
  have hleft := congrArg ShiftedPair.left he
  rw [hreal n hn, hreal m hm, hleft]

/-- The unconditional published estimate on a fixed common-factor and
left-tail block, with its actual integer right residual. -/
theorem ppt_plain_comparison_block_count :
    ∃ C z₀ : ℝ, 0 < C ∧ 1 < z₀ ∧
    ∀ (b d c a : ℕ) (z S : ℝ) (Y U : ℕ → ℝ),
      z₀ ≤ z → FordComparisonParameters b z S (d*a.totient) c.totient Y U →
      ∀ (T : Finset ℕ) (t : ℕ → ShiftedPair b),
        (∀ n ∈ T, n = c*a*∏ i, (t n).left i) →
        (∀ n ∈ T, FordComparisonConditions b z S (d*a.totient) c.totient Y U (t n)) →
        (T.card : ℝ) ≤ fordComparisonBound C b z S (d*a.totient) c.totient Y U := by
  classical
  obtain ⟨C, z₀, hC, hz₀, hford⟩ := fordLemma51Input
  refine ⟨C, z₀, hC, hz₀, ?_⟩
  intro b d c a z S Y U hz hparams T t hreal hconditions
  have hh := hford b z S (d*a.totient) c.totient Y U hz hparams (T.image t) (by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    exact hconditions n hn)
  rwa [Finset.card_image_of_injOn (ppt_plain_comparison_injective T t hreal)] at hh

/-- Sum the concrete plain-residual comparison blocks with the proved
normal-tail cost, retaining both reciprocal totient masses. -/
theorem ppt_plain_normal_tail_comparison_sum :
    ∃ C z₀ : ℝ, 0 < C ∧ 1 < z₀ ∧
    ∀ (b d h : ℕ) (z W V : ℝ) (Y U : ℕ → ℝ)
      (R A : Finset ℕ) (T : ℕ → ℕ → Finset ℕ)
      (tail : ℕ → Fin h → ℕ) (t : ℕ → ℕ → ℕ → ShiftedPair b),
      0 < d → z₀ ≤ z → 0 ≤ B z → 1 < W → 0 ≤ B W → W ≤ V → 1 ≤ Y b →
      (∀ a ∈ A, a = ∏ i, tail a i) →
      (∀ a ∈ A, Function.Injective (tail a)) →
      (∀ a ∈ A, ∀ i, IsNormalPrime W (tail a i)) →
      (∀ a ∈ A, ∀ i, (largestPrimeFactor (tail a i-1) : ℝ) ≤ V) →
      (∀ c ∈ R, ∀ a ∈ A,
        FordComparisonParameters b z W (d*a.totient) c.totient Y U) →
      (∀ c ∈ R, ∀ a ∈ A, ∀ n ∈ T c a, n = c*a*∏ i, (t c a n).left i) →
      (∀ c ∈ R, ∀ a ∈ A, ∀ n ∈ T c a,
        FordComparisonConditions b z W (d*a.totient) c.totient Y U (t c a n)) →
      (∑ c ∈ R, ∑ a ∈ A, ((T c a).card : ℝ)) ≤
        z/(d : ℝ)*pptComparisonScale C b z W Y U*
          ((b+1 : ℝ)^d.primeFactorsList.length*
            Real.exp (4*(h : ℝ)*B V*Real.log (b+1)))*
          (∑ c ∈ R, 1/(c.totient : ℝ))*(∑ a ∈ A, 1/(a.totient : ℝ)) := by
  obtain ⟨C, z₀, hC, hz₀, hcount⟩ := ppt_plain_comparison_block_count
  refine ⟨C, z₀, hC, hz₀, ?_⟩
  intro b d h z W V Y U R A T tail t hd hz hB hW hBW hWV hY
    htail hinj hnormal hsmall hparams hreal hconditions
  apply ppt_comparison_block_sum (zero_lt_one.trans (hz₀.trans_le hz)).le
    (ppt_comparison_scale_nonneg hC.le hB (hz₀.trans_le hz).le hY) R A T
  · intro c hc a ha
    exact hcount b d c a z W Y U hz (hparams c hc a ha) (T c a)
      (t c a) (hreal c hc a ha) (hconditions c hc a ha)
  · intro a ha
    rw [htail a ha]
    exact ppt_small_tail_comparison_cost b (tail a) hd (hnormal a ha)
      (hinj a ha) hW hBW hWV (hsmall a ha)

end TotientAsymptotic

end

end OAI
