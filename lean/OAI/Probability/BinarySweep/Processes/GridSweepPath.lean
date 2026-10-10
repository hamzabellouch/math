import Mathlib
import OAI.Probability.BinarySweep.Processes.CoordinateLayerEdgeSwap

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma gridSweep_path {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) (k : Fin h) :
    gridSweep bits g (H.position 0 k) = H.position (Fin.last b) k :=
  chronological_trajectory b (gridLayer bits g) (fun t => H.position t k) (fun j => hg j k)

abbrev FreeSlot {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) := {x : GridSlot bits // x ∉ Set.range (H.position t)}

instance freeSlotFintype {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) : Fintype (FreeSlot H t) := Fintype.ofFinite _

lemma card_freeSlot {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (t : Fin (b + 1)) : Fintype.card (FreeSlot H t) = gridSize bits - h := by
  classical
  rw [show Fintype.card (FreeSlot H t) =
    Fintype.card (GridSlot bits) - Fintype.card (Set.range (H.position t)) from
      Fintype.card_subtype_compl (fun x => x ∈ Set.range (H.position t))]
  rw [card_gridSlot]
  have hr : Fintype.card (Set.range (H.position t)) = h := by
    let e : Fin h ↪ GridSlot bits := ⟨H.position t, H.disjoint t⟩
    simpa [e] using Fintype.card_range e
  rw [hr]

def freeIdentification {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    FreeSlot H 0 ≃ FreeSlot H (Fin.last b) :=
  Fintype.equivOfCardEq (by rw [card_freeSlot, card_freeSlot])

def remainingBijection {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) :
    FreeSlot H 0 ≃ FreeSlot H (Fin.last b) where
  toFun x := ⟨gridSweep bits g x, by
    rintro ⟨k, hk⟩
    exact x.property ⟨k, (gridSweep bits g).injective ((gridSweep_path H g hg k).trans hk)⟩⟩
  invFun y := ⟨(gridSweep bits g).symm y, by
    rintro ⟨k, hk⟩
    apply y.property
    refine ⟨k, ?_⟩
    rw [← gridSweep_path H g hg k, hk]
    exact (gridSweep bits g).apply_symm_apply y⟩
  left_inv x := by apply Subtype.ext; exact (gridSweep bits g).symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact (gridSweep bits g).apply_symm_apply y

def remainingPerm {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) (hg : pathEvent H g) : Equiv.Perm (FreeSlot H 0) :=
  (remainingBijection H g hg).trans (freeIdentification H).symm

def conditionalNormalizer {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : ℝ := by
  classical
  exact ∑ g : GridChoices bits, if pathEvent H g then gridWeight bits z g else 0

def conditionalOperator {b h D : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) :
    RepSpace D →L[ℂ] RepSpace D := by
  classical
  exact LinearMap.toContinuousLinearMap
    ((conditionalNormalizer H z : ℂ)⁻¹ • ∑ g : GridChoices bits,
      if hg : pathEvent H g then (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg)
      else 0)

def lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : ℕ := by
  classical
  exact Fintype.card {k : Fin h // (fun i : {i : Fin b // i ≠ j} =>
    H.position j.castSucc k i) = y}

def pathCost {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) : ℝ :=
  ∑ j, ∑ y : GridOutside bits j,
    Real.log (((2 ^ bits j : ℕ) : ℝ) ^ lineHoles H j y /
      (Nat.descFactorial (2 ^ bits j) (lineHoles H j y) : ℝ))

def ConditionalMomentTarget : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ q : ℕ, 0 < q ∧ ∃ zStar : ℝ, 0 < zStar ∧
    ∀ b : ℕ, 1 ≤ b → ∀ bits : Fin b → ℕ, (∀ j, r ≤ bits j ∧ bits j ≤ 2 * r) →
    ∀ h : ℕ, ∀ H : PathFamily bits h, ∀ z : ℝ, 0 ≤ z → z ≤ zStar →
    ∀ D : ℕ, ∀ ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D),
      ρ.IsIrreducible → IsUnitaryRep ρ →
      logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
        ((-cExponent (gridSize bits) * Real.log D +
          eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal)

theorem pathEvent_nonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    ∃ g : GridChoices bits, pathEvent H g := by
  classical
  let A (j : Fin b) (y : GridOutside bits j) :=
    {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}
  have hp (j : Fin b) (y : GridOutside bits j) :
      ∃ σ : Equiv.Perm (Slot (bits j)), ∀ k : A j y,
        σ (H.position j.castSucc k.val j) = H.position j.succ k.val j := by
    apply Equiv.Perm.exists_extending_pair
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.castSucc
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.succ
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
        exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
  choose g hg using hp
  refine ⟨g, ?_⟩
  intro j k
  apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
  simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
  apply Prod.ext
  · exact hg j _ ⟨k, rfl⟩
  · funext i
    exact (H.changes_only_stage j k i.val i.property).symm

lemma lineLaw_pos (d : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : Equiv.Perm (Slot d)) : 0 < lineLaw d z g := by
  have hu : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    exact inv_pos.mpr hc
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz1) hu)
    (mul_nonneg hz (finiteLaw_nonneg (binarySweep d) g))

lemma lineLaw_sum (d : ℕ) (z : ℝ) : ∑ g, lineLaw d z g = 1 := by
  simp only [lineLaw, Finset.sum_add_distrib, ← Finset.mul_sum,
    uniformLaw_sum, binaryLaw, finiteLaw_sum]
  ring

lemma gridWeight_pos {b : ℕ} (bits : Fin b → ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : GridChoices bits) : 0 < gridWeight bits z g := by
  apply Finset.prod_pos
  intro j _
  exact Finset.prod_pos (fun y _ => lineLaw_pos (bits j) hz hz1 (g j y))

lemma gridWeight_sum {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) :
    ∑ g : GridChoices bits, gridWeight bits z g = 1 := by
  classical
  unfold gridWeight
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, lineLaw (bits j) z (g y))]
  have hj (j : Fin b) : ∑ g : GridOutside bits j → Equiv.Perm (Slot (bits j)),
      ∏ y, lineLaw (bits j) z (g y) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : GridOutside bits j)
      (g : Equiv.Perm (Slot (bits j))) => lineLaw (bits j) z g)]
    simp [lineLaw_sum]
  simp [hj]

theorem conditionalNormalizer_pos {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) : 0 < conditionalNormalizer H z := by
  classical
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  apply Finset.sum_pos'
  · intro g' _
    split_ifs
    · exact (gridWeight_pos bits hz hz1 g').le
    · exact le_rfl
  · exact ⟨g, Finset.mem_univ _, by simpa [hg] using gridWeight_pos bits hz hz1 g⟩

variable {G : Type*} [Fintype G] [Group G]

lemma uniformLaw_probability : IsProbability (uniformLaw G) :=
  ⟨fun _ => by unfold uniformLaw; positivity, uniformLaw_sum⟩

lemma convolution_sub_left (p q r : G → ℝ) :
    convolution (fun g => p g - q g) r = fun g => convolution p r g - convolution q r g := by
  funext g
  simp [convolution, sub_mul, Finset.sum_sub_distrib]

lemma convolution_smul_left (a : ℝ) (p q : G → ℝ) :
    convolution (fun g => a * p g) q = fun g => a * convolution p q g := by
  funext g
  simp [convolution, mul_assoc, Finset.mul_sum]

lemma convolution_uniform_right_mass (p : G → ℝ) :
    convolution p (uniformLaw G) = fun g => (∑ x, p x) * uniformLaw G g := by
  funext g
  simp [convolution, uniformLaw, Finset.sum_mul]

lemma convolution_minorization {p q : G → ℝ} (hp : IsProbability p) (hq : IsProbability q)
    (δ : ℝ) (hδ : ∀ g, δ * uniformLaw G g ≤ p g) :
    totalVariation (convolution p q) (uniformLaw G) ≤
      (1 - δ) * totalVariation q (uniformLaw G) := by
  let r : G → ℝ := fun g => p g - δ * uniformLaw G g
  have hr : ∀ g, 0 ≤ r g := fun g => sub_nonneg.mpr (hδ g)
  have hmass : ∑ g, r g = 1 - δ := by
    simp [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, uniformLaw_sum]
  have he : totalVariation (convolution p q) (uniformLaw G) =
      totalVariation (convolution r q) (convolution r (uniformLaw G)) := by
    have hdiff (g : G) : convolution r q g - convolution r (uniformLaw G) g =
        convolution p q g - uniformLaw G g := by
      rw [show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_sub_left, convolution_smul_left, convolution_uniform_left hq.2]
      rw [← show r = (fun g => p g - δ * uniformLaw G g) from rfl,
        convolution_uniform_right_mass, hmass]
      ring
    simp only [totalVariation, hdiff]
  rw [he]
  simpa only [hmass] using convolution_tv_contract hr q (uniformLaw G)

end BinaryCoordinateSweeps
end

end OAI
