import OAI.Analysis.KadisonKastler.BilateralCoordinateSigma

namespace OAI

/-! Three separated increment blocks in the double-ergodicity proof. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralLeftWord (m : ℕ) := bilateralIncrementProduct G (m + 1)
def bilateralMiddleWord (m : ℕ) (ω : BilateralWalkPath G) := (ω ((m + 1 : ℕ) : ℤ))⁻¹
def bilateralRightWord (m : ℕ) (ω : BilateralWalkPath G) :=
  bilateralIncrementProduct G m (bilateralTranslate G (m + 2) ω)

theorem bilateralLeftWord_measurable (m : ℕ) : Measurable (bilateralLeftWord G m) :=
  bilateralIncrementProduct_measurable G _

theorem bilateralMiddleWord_measurable (m : ℕ) : Measurable (bilateralMiddleWord G m) :=
  (measurable_of_countable (Inv.inv : G → G)).comp (measurable_pi_apply _)

theorem bilateralRightWord_measurable (m : ℕ) : Measurable (bilateralRightWord G m) :=
  (bilateralIncrementProduct_measurable G _).comp (bilateralTranslate_measurePreserving G _).measurable

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem bilateral_block_word_factorization (m : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (2 * m + 2) ω =
      bilateralRightWord G m ω * (bilateralMiddleWord G m ω * bilateralLeftWord G m ω) := by
  have hn : 2 * m + 2 = (m + 2) + m := by omega
  rw [hn, bilateralIncrementProduct_add]
  rfl

variable {G}

theorem bilateralIncrementProduct_shift_coordinate_measurable {I : Set ℤ} (k : ℤ) (n : ℕ)
    (hI : ∀ j : ℕ, j < n → (j : ℤ) + k ∈ I) :
    Measurable[cylinderEvents (X := fun _ : ℤ => G) I]
      (fun ω => bilateralIncrementProduct G n (bilateralTranslate G k ω)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_cylinderEvent_apply (hI n (Nat.lt_succ_self n))).prodMk
        (ih (fun j hj => hI j (hj.trans (Nat.lt_succ_self n)))))

def bilateralSymmetricWindow (m : ℕ) : Set ℤ := {j | -(m : ℤ) ≤ j ∧ j ≤ m}

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_symmetricWindow_L2_approximation
    (f : Lp K 2 (bilateralWalkLaw G)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Lp K 2 (bilateralWalkLaw G)),
      AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
        g (bilateralWalkLaw G) ∧ ‖f - g‖ < ε := by
  obtain ⟨I, g, hg, hfg⟩ := exists_finiteCoordinate_L2_approximation f hε
  refine ⟨I.sup Int.natAbs, g, hg.mono (cylinderEvents_mono ?_), ?_⟩
  · intro j hj
    have hjm : j.natAbs ≤ I.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hj
    have hp : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    have hn : -(j.natAbs : ℤ) ≤ j := by
      have hh : -j ≤ ((-j).natAbs : ℤ) := Int.le_natAbs
      simpa only [Int.natAbs_neg, neg_neg] using (neg_le_neg hh)
    change -((I.sup Int.natAbs : ℕ) : ℤ) ≤ j ∧ j ≤ ((I.sup Int.natAbs : ℕ) : ℤ)
    omega
  · simpa only [dist_eq_norm] using hfg

end

end KadisonKastler

end OAI
