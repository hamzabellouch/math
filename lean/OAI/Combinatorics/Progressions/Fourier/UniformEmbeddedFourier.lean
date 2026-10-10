import OAI.Combinatorics.Progressions.Probability.RawWeightCellMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {R J : Type*} [Fintype R] [Fintype J] [DecidableEq J]
  {X : R → Type*} [∀ r, Fintype (X r)]

noncomputable def integerGridMixture (w : R → ℝ)
    (p : ∀ r, FiniteProbabilityWeights (X r)) (Y : ∀ r, X r → J → ℤ)
    (K : ℕ) (M : R → ℕ) [∀ r, NeZero (M r)]
    (S : ∀ r, Finset (J → Fin (M r))) (z : J → ℤ) : ℂ :=
  weightedMixtureExpansion (A := fun r => S r) w
    (fun r k => integerRetainedCoefficient (p r) (Y r) K (M r) k)
    (fun r k z => star (rectangularGridCharacter (M r) k z)) z

theorem integerGridMixture_eq_sum (w : R → ℝ)
    (p : ∀ r, FiniteProbabilityWeights (X r)) (Y : ∀ r, X r → J → ℤ)
    (K : ℕ) (M : R → ℕ) [∀ r, NeZero (M r)]
    (S : ∀ r, Finset (J → Fin (M r))) (z : J → ℤ) :
    integerGridMixture w p Y K M S z =
      ∑ r, (w r : ℂ) * integerGridApproximation (p r) (Y r) K (M r) (S r) z := by
  rw [integerGridMixture, weightedMixtureExpansion_eq_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [integerGridApproximation_eq_sum]
  congr 1
  exact Finset.sum_coe_sort (S r)
    (fun k => integerRetainedCoefficient (p r) (Y r) K (M r) k * star (rectangularGridCharacter (M r) k z))

theorem integerGridMixture_coefficient_mass (w : R → ℝ)
    (p : ∀ r, FiniteProbabilityWeights (X r)) (Y : ∀ r, X r → J → ℤ)
    (K : ℕ) (M : R → ℕ) [∀ r, NeZero (M r)]
    (S : ∀ r, Finset (J → Fin (M r))) {C : ℝ}
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (hC : 0 ≤ C)
    (hKM : ∀ r, K ≤ M r)
    (hcap : ∀ r, (∑ k, ‖integerGridCoefficient (p r) (Y r) (M r) k‖) ≤ C) :
    (∑ t : Σ r, S r,
      ‖(w t.1 : ℂ) * integerRetainedCoefficient (p t.1) (Y t.1) K (M t.1) t.2‖) ≤ C := by
  apply weightedMixtureExpansion_mass_le (A := fun r => S r) w
    (fun r k => integerRetainedCoefficient (p r) (Y r) K (M r) k) hw hmass hC
  intro r
  calc
    _ = ∑ k ∈ S r, ‖integerRetainedCoefficient (p r) (Y r) K (M r) k‖ :=
      Finset.sum_coe_sort (S r) (fun k => ‖integerRetainedCoefficient (p r) (Y r) K (M r) k‖)
    _ ≤ C := integerRetainedCoefficient_mass_le (p r) (Y r) K (M r) (S r) (hKM r) (hcap r)

theorem integerGridMixture_approximation (w : R → ℝ)
    (p : ∀ r, FiniteProbabilityWeights (X r)) (Y : ∀ r, X r → J → ℤ)
    (K : ℕ) (M : R → ℕ) [∀ r, NeZero (M r)]
    (S : ∀ r, Finset (J → Fin (M r))) (z : J → ℤ) {ε : ℝ}
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (hε : 0 ≤ ε)
    (he : ∀ r, ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass (p r) (Y r) z : ℝ) : ℂ) -
      integerGridApproximation (p r) (Y r) K (M r) (S r) z‖ ≤ ε) :
    ‖(((K : ℝ) ^ Fintype.card J * (∑ r, w r * finiteImageMass (p r) (Y r) z) : ℝ) : ℂ) -
      integerGridMixture w p Y K M S z‖ ≤ ε := by
  rw [integerGridMixture_eq_sum]
  have hsum : (((K : ℝ) ^ Fintype.card J * (∑ r, w r * finiteImageMass (p r) (Y r) z) : ℝ) : ℂ) =
      ∑ r, (w r : ℂ) * (((K : ℝ) ^ Fintype.card J * finiteImageMass (p r) (Y r) z : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  exact norm_weighted_mixture_sub_le_uniform w _ _ hw hmass hε he

end Erdos3

end

section

namespace Erdos3.IntegerFourierBudget

open scoped BigOperators Classical

theorem mixture_approximation {R J : Type*} [Fintype R] [Fintype J]
    {X : R → Type*} [∀ r, Fintype (X r)] (B : IntegerFourierBudget)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1)
    (p : ∀ r, FiniteProbabilityWeights (X r)) (Y : ∀ r, (J → ℤ) → X r → J → ℤ)
    (K : ℕ) (M : R → ℕ) [∀ r, NeZero (M r)] (hKM : ∀ r, K ≤ M r)
    (hcap : 0 ≤ B.coefficientCap) (hmodel : ∀ r, B.Controls (p r) (Y r) K (M r))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ S : ∀ r, Finset (J → Fin (M r)),
      (Fintype.card (Σ r, S r) : ℝ) ≤ (Fintype.card R : ℝ) * B.countConstant / ε ^ B.countExponent ∧
      (∀ center, (∑ t : Σ r, S r,
        ‖(w t.1 : ℂ) * integerRetainedCoefficient (p t.1) (Y t.1 center) K (M t.1) t.2‖) ≤
          B.coefficientCap) ∧
      (∀ t : Σ r, S r, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ B.denominatorBound ε ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ B.residualBound ε) ∧
          ∀ j, ((t.2.val j).val : ℝ) / M t.1 = (a j : ℝ) / d + ξ j / K) ∧
      ∀ center z, centeredFundamentalBox B.radius K center z →
        ‖(((K : ℝ) ^ Fintype.card J *
          (∑ r, w r * finiteImageMass (p r) (Y r center) z) : ℝ) : ℂ) -
          integerGridMixture w p (fun r => Y r center) K M S z‖ ≤ ε := by
  have hm (r : R) := hmodel r ε hε hε1
  choose S hcount hfull hchar happ using hm
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ r : R, B.countConstant / ε ^ B.countExponent :=
        weightedMixtureExpansion_card_le (fun r => S r) (fun _ => B.countConstant / ε ^ B.countExponent)
          (fun r => by simpa only [Fintype.card_coe] using hcount r)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
  · intro center
    exact integerGridMixture_coefficient_mass w p (fun r => Y r center) K M S hw hmass hcap hKM
      (fun r => hfull r center)
  · intro t
    exact hchar t.1 t.2.val t.2.property
  · intro center z hz
    exact integerGridMixture_approximation w p (fun r => Y r center) K M S z hw hmass hε.le
      (fun r => happ r center z hz)

end Erdos3.IntegerFourierBudget

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def retainedImageMass {X R Z : Type*} [Fintype X] [DecidableEq R] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R) (O : X → Z) (z : Z) : ℝ :=
  p.mean (fun x => if F x ∈ S then if O x = z then 1 else 0 else 0)

namespace FiniteProbabilityWeights

theorem embedded_cell_image_mass {X R Z : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq R] [DecidableEq Z]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (S : Finset R) (Y : S → Type*) [∀ r, Fintype (Y r)]
    (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (O : X → Z) (z : Z) :
    (∑ r : S, (ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)) *
      finiteImageMass (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
        (fun y => O (e r y)) z) = retainedImageMass (ofPositiveWeights w hw htotal) F S O z := by
  have h := congrArg Complex.re (embedded_cell_mixture w hw htotal F S Y e hcell hchild
    (fun x => if O x = z then (1 : ℂ) else 0))
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, complexMean_re, apply_ite, Complex.one_re, Complex.zero_re,
    retainedImageMass, finiteImageMass] using h

theorem embedded_cell_fourier_approximation {X R J : Type*}
    [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R] [Fintype J] [DecidableEq J]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (S : Finset R) (Y : S → Type*) [∀ r, Fintype (Y r)]
    (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (O : X → J → ℤ)
    (K : ℕ) (M : S → ℕ) [∀ r, NeZero (M r)]
    (T : ∀ r, Finset (J → Fin (M r))) (z : J → ℤ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ r : S,
      ‖(((K : ℝ) ^ Fintype.card J *
        finiteImageMass (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
          (fun y => O (e r y)) z : ℝ) : ℂ) -
        integerGridApproximation
          (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
          (fun y => O (e r y)) K (M r) (T r) z‖ ≤ ε) :
    ‖(((K : ℝ) ^ Fintype.card J * retainedImageMass (ofPositiveWeights w hw htotal) F S O z : ℝ) : ℂ) -
      integerGridMixture
        (fun r : S => (ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)))
        (fun r => ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
        (fun r y => O (e r y)) K M T z‖ ≤ ε := by
  have h := integerGridMixture_approximation
    (fun r : S => (ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)))
    (fun r => ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
    (fun r y => O (e r y)) K M T z
    (fun r => (ofPositiveWeights w hw htotal).mass_nonneg _)
    ((ofPositiveWeights w hw htotal).sum_fiber_masses_le_one F S) hε he
  rw [embedded_cell_image_mass w hw htotal F S Y e hcell hchild O z] at h
  exact h

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.IntegerFourierBudget

open scoped BigOperators Classical

theorem embedded_mixture_approximation {X R J : Type*}
    [Fintype X] [Fintype R] [Fintype J] (B : IntegerFourierBudget)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (C : Finset R) (Y : C → Type*) [∀ r, Fintype (Y r)]
    (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (O : (J → ℤ) → X → J → ℤ)
    (K : ℕ) (M : C → ℕ) [∀ r, NeZero (M r)] (hKM : ∀ r, K ≤ M r)
    (hcap : 0 ≤ B.coefficientCap)
    (hmodel : ∀ r, B.Controls
      (FiniteProbabilityWeights.ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r))
      (fun center y => O center (e r y)) K (M r))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let p := FiniteProbabilityWeights.ofPositiveWeights w hw htotal
    let weights := fun r : C => p.mass (Finset.univ.filter (fun x => F x = r.val))
    let q := fun r : C => FiniteProbabilityWeights.ofPositiveWeights
      (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r)
    ∃ S : ∀ r, Finset (J → Fin (M r)),
      (Fintype.card (Σ r, S r) : ℝ) ≤ (C.card : ℝ) * B.countConstant / ε ^ B.countExponent ∧
      (∀ center, (∑ t : Σ r, S r,
        ‖(weights t.1 : ℂ) * integerRetainedCoefficient (q t.1) (fun y => O center (e t.1 y)) K (M t.1) t.2‖) ≤
          B.coefficientCap) ∧
      (∀ t : Σ r, S r, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ B.denominatorBound ε ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ B.residualBound ε) ∧
          ∀ j, ((t.2.val j).val : ℝ) / M t.1 = (a j : ℝ) / d + ξ j / K) ∧
      ∀ center z, centeredFundamentalBox B.radius K center z →
        ‖(((K : ℝ) ^ Fintype.card J * retainedImageMass p F C (O center) z : ℝ) : ℂ) -
          integerGridMixture weights q (fun r y => O center (e r y)) K M S z‖ ≤ ε := by
  dsimp only
  let p := FiniteProbabilityWeights.ofPositiveWeights w hw htotal
  let weights := fun r : C => p.mass (Finset.univ.filter (fun x => F x = r.val))
  let q := fun r : C => FiniteProbabilityWeights.ofPositiveWeights
    (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r)
  obtain ⟨S, hcount, hcoef, hchar, happ⟩ := B.mixture_approximation weights
    (fun r => p.mass_nonneg _) (p.sum_fiber_masses_le_one F C)
    q (fun r center y => O center (e r y)) K M hKM hcap hmodel hε hε1
  refine ⟨S, ?_, hcoef, hchar, ?_⟩
  · simpa only [Fintype.card_coe] using hcount
  · intro center z hz
    have h := happ center z hz
    dsimp only [weights, p, q] at h
    rw [FiniteProbabilityWeights.embedded_cell_image_mass w hw htotal F C Y e hcell hchild (O center) z] at h
    exact h

end Erdos3.IntegerFourierBudget

end

end OAI
