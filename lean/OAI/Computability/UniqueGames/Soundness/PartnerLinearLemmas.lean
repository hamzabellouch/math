import Mathlib.Algebra.Module.TransferInstance
import Std
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Soundness.LinearMapDensityLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.PartnerLinear

open PartnerProjection
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev SourceCoordinates (P : Type) := F2 × (P → F2 × F2)
abbrev Active := {j : P // active j = true}
abbrev Inactive := {j : P // active j = false}
abbrev PartnerCoordinates := F2 × ((Inactive active → F2 × F2) × (Active active → F2))

def sourceCoordinates (x : SourcePoint rhs) : SourceCoordinates P :=
  (ofBit x.homogeneous, fun j => (ofBit (x.coordinates j).first, ofBit (x.coordinates j).second))

def sourceFromCoordinates (v : SourceCoordinates P) : SourcePoint rhs where
  homogeneous := toBit v.1
  coordinates := fun j => complete .first (rhs j && toBit v.1)
    (toBit (v.2 j).1) (toBit (v.2 j).2)
  valid := by intro j; exact parity_complete _ _ _ _

def sourceEquiv : SourcePoint rhs ≃ SourceCoordinates P where
  toFun := sourceCoordinates rhs
  invFun := sourceFromCoordinates rhs
  left_inv x := by
    apply source_ext rhs
    · exact toBit_ofBit _
    · funext j
      change complete .first (rhs j && toBit (ofBit x.homogeneous))
        (toBit (ofBit (x.coordinates j).first))
        (toBit (ofBit (x.coordinates j).second)) = x.coordinates j
      simp only [toBit_ofBit, ← x.valid j]
      exact complete_coordinates .first (x.coordinates j)
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · funext j
      apply Prod.ext <;> exact ofBit_toBit _

def partnerCoordinates (y : PartnerPoint rhs active) : PartnerCoordinates active :=
  (ofBit y.homogeneous,
    (fun j => (ofBit (y.full j.val).first, ofBit (y.full j.val).second),
      fun j => ofBit (y.single j.val)))

def partnerFromCoordinates (v : PartnerCoordinates active) : PartnerPoint rhs active where
  homogeneous := toBit v.1
  full := fun j => if hj : active j = false then
    complete .first (rhs j && toBit v.1)
      (toBit (v.2.1 ⟨j, hj⟩).1) (toBit (v.2.1 ⟨j, hj⟩).2)
    else zeroTriple
  single := fun j => if hj : active j = true then toBit (v.2.2 ⟨j, hj⟩) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simp only [dite_eq_left hj]; exact parity_complete _ _ _ _
  single_zero := by intro j hj; simp [hj]

def partnerEquiv : PartnerPoint rhs active ≃ PartnerCoordinates active where
  toFun := partnerCoordinates rhs active
  invFun := partnerFromCoordinates rhs active
  left_inv y := by
    apply partner_ext rhs active
    · exact toBit_ofBit _
    · funext j
      cases hj : active j with
      | false =>
        change (if hj' : active j = false then
          complete .first (rhs j && toBit (ofBit y.homogeneous))
            (toBit (ofBit (y.full j).first)) (toBit (ofBit (y.full j).second))
          else zeroTriple) = y.full j
        simp only [dite_eq_left hj, toBit_ofBit, ← y.full_valid j hj]
        exact complete_coordinates .first (y.full j)
      | true => simpa [partnerFromCoordinates, hj] using (y.full_zero j hj).symm
    · funext j
      cases hj : active j with
      | false => simpa [partnerFromCoordinates, hj] using (y.single_zero j hj).symm
      | true => simp [partnerFromCoordinates, partnerCoordinates, hj, toBit_ofBit]
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · apply Prod.ext
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, complete, ofBit_toBit]
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, ofBit_toBit]

noncomputable instance sourceAddCommGroup : AddCommGroup (SourcePoint rhs) :=
  (sourceEquiv rhs).addCommGroup

noncomputable instance sourceModule : Module F2 (SourcePoint rhs) :=
  (sourceEquiv rhs).addEquiv.module F2

noncomputable instance partnerAddCommGroup : AddCommGroup (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addCommGroup

noncomputable instance partnerModule : Module F2 (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addEquiv.module F2

noncomputable def sourceLinearEquiv : SourcePoint rhs ≃ₗ[F2] SourceCoordinates P :=
  (sourceEquiv rhs).addEquiv.linearEquiv F2

noncomputable def partnerLinearEquiv : PartnerPoint rhs active ≃ₗ[F2] PartnerCoordinates active :=
  (partnerEquiv rhs active).addEquiv.linearEquiv F2

noncomputable instance sourceFintype [Fintype P] : Fintype (SourcePoint rhs) := by
  classical
  exact Fintype.ofEquiv (SourceCoordinates P) (sourceEquiv rhs).symm

noncomputable instance partnerFintype [Fintype P] : Fintype (PartnerPoint rhs active) := by
  classical
  exact Fintype.ofEquiv (PartnerCoordinates active) (partnerEquiv rhs active).symm

theorem source_add (x y : SourcePoint rhs) : x + y = addSource rhs x y := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm (sourceEquiv rhs x + sourceEquiv rhs y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · funext j
    apply Prod.ext <;> exact (ofBit_xor _ _).symm

theorem source_zero : (0 : SourcePoint rhs) = zeroSource rhs := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem partner_add (x y : PartnerPoint rhs active) : x + y = addPartner rhs active x y := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm
    (partnerEquiv rhs active x + partnerEquiv rhs active y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · apply Prod.ext
    · funext j
      apply Prod.ext <;> exact (ofBit_xor _ _).symm
    · funext j
      exact (ofBit_xor _ _).symm

theorem partner_zero : (0 : PartnerPoint rhs active) = zeroPartner rhs active := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

noncomputable def projection : SourcePoint rhs →ₗ[F2] PartnerPoint rhs active where
  toFun := project rhs active slot
  map_add' x y := by rw [source_add, partner_add]; exact project_add rhs active slot x y
  map_smul' c x := by
    rcases scalar_cases c with rfl | rfl
    · change project rhs active slot ((0 : F2) • x) = (0 : F2) • project rhs active slot x
      rw [zero_smul, zero_smul, source_zero, partner_zero, project_zero]
    · simp

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl

theorem projection_surjective : Function.Surjective (projection rhs active slot) :=
  project_surjective rhs active slot

theorem mem_projection_ker (x : SourcePoint rhs) :
    x ∈ (projection rhs active slot).ker ↔ InKernel rhs active slot x := by
  change project rhs active slot x = 0 ↔ _
  rw [partner_zero]
  rfl

noncomputable instance sourceFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (SourcePoint rhs) :=
  (sourceLinearEquiv rhs).symm.finiteDimensional

noncomputable instance partnerFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (PartnerPoint rhs active) :=
  (partnerLinearEquiv rhs active).symm.finiteDimensional

/-- Identifies the actual linear kernel with the previously counted concrete kernel. -/
noncomputable def kernelEquiv :
    (projection rhs active slot).ker ≃ KernelCardinality.Kernel rhs active slot where
  toFun x := ⟨x.val, (mem_projection_ker rhs active slot x.val).1 x.property⟩
  invFun x := ⟨x.val, (mem_projection_ker rhs active slot x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem projection_ker_card [Fintype P] :
    Nat.card (projection rhs active slot).ker = 2 ^ Fintype.card (Active active) := by
  rw [Nat.card_congr (kernelEquiv rhs active slot), Nat.card_eq_fintype_card]
  exact KernelCardinality.kernel_card rhs active slot

theorem projection_ker_finrank [Fintype P] :
    Module.finrank F2 (projection rhs active slot).ker = Fintype.card (Active active) := by
  have h := UniqueGamesTheorem.Gadget.LinearKernelCount.card_binary_space
    (V := (projection rhs active slot).ker)
  rw [projection_ker_card] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat)) h.symm

theorem projection_ker_finrank_of_card [Fintype P] (t : Nat)
    (ht : Fintype.card (Active active) = t) :
    Module.finrank F2 (projection rhs active slot).ker = t := by
  rw [projection_ker_finrank, ht]

theorem source_finrank [Fintype P] :
    Module.finrank F2 (SourcePoint rhs) = 1 + 2 * Fintype.card P := by
  rw [(sourceLinearEquiv rhs).finrank_eq]
  simp [SourceCoordinates, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

/-- Distinct coordinate blocks make disjoint active-set kernels have trivial intersection. -/
theorem disjoint_projection_kernels
    (active' : P → Bool) (slot' : P → Slot)
    (hdisjoint : ∀ j, active j = true → active' j = false) :
    (projection rhs active slot).ker ⊓ (projection rhs active' slot').ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    rw [source_zero]
    exact disjoint_kernels_intersection_zero rhs active slot active' slot' hdisjoint x
      ((mem_projection_ker rhs active slot x).1 hx.1)
      ((mem_projection_ker rhs active' slot' x).1 hx.2)
  · exact bot_le

noncomputable def sourceTau : SourcePoint rhs →ₗ[F2] F2 :=
  (LinearMap.fst F2 F2 (P → F2 × F2)).comp (sourceLinearEquiv rhs).toLinearMap

noncomputable def partnerTau : PartnerPoint rhs active →ₗ[F2] F2 :=
  (LinearMap.fst F2 F2 ((Inactive active → F2 × F2) × (Active active → F2))).comp
    (partnerLinearEquiv rhs active).toLinearMap

theorem sourceTau_apply (x : SourcePoint rhs) : sourceTau rhs x = ofBit x.homogeneous := rfl
theorem partnerTau_apply (x : PartnerPoint rhs active) :
    partnerTau rhs active x = ofBit x.homogeneous := rfl

theorem tau_comp_projection :
    (partnerTau rhs active).comp (projection rhs active slot) = sourceTau rhs := by
  ext x
  rfl

end UniqueGamesTheorem.Soundness.PartnerLinear

end

section

namespace UniqueGamesTheorem.Soundness.RepetitionUpper

/-- Expectation of `f` evaluated at the number of successes in `n` independent
Bernoulli trials.  The recursion itself specifies the product distribution. -/
def bernoulliAverage (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f =>
      (1 - p) * bernoulliAverage p n f +
        p * bernoulliAverage p n (fun k => f (k + 1))

theorem bernoulliAverage_scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    bernoulliAverage p n (fun k => c * f k) = c * bernoulliAverage p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [bernoulliAverage, ih]
      grind

/-- The exact binomial generating-function identity used in (6.25). -/
theorem bernoulliAverage_geometric (p a : Rat) (n : Nat) :
    bernoulliAverage p n (fun k => a ^ k) = (1 - p * (1 - a)) ^ n := by
  induction n with
  | zero => simp [bernoulliAverage]
  | succ n ih =>
      simp only [bernoulliAverage]
      have hs : (fun k : Nat => a ^ (k + 1)) = fun k => a * a ^ k := by
        funext k
        rw [Rat.pow_succ, Rat.mul_comm]
      rw [hs, bernoulliAverage_scale, ih, Rat.pow_succ]
      grind

theorem bernoulliAverage_mono (p : Rat) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : Nat) (f g : Nat → Rat) (h : ∀ k, f k ≤ g k) :
    bernoulliAverage p n f ≤ bernoulliAverage p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
      have hleft := ih f g h
      have hright := ih (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => h (k + 1))
      have hnp : 0 ≤ 1 - p := by grind
      have hl := Rat.mul_le_mul_of_nonneg_left hleft hnp
      have hr := Rat.mul_le_mul_of_nonneg_left hright hp
      simp only [bernoulliAverage]
      grind

/-- The repeated-game bound is the explicitly supplied premise `conditional`.
The premise `averaged` is the separate law-of-total-probability obligation. -/
theorem success_le_geometric
    (p a success : Rat) (n : Nat) (conditionalSuccess : Nat → Rat)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage p n conditionalSuccess) :
    success ≤ (1 - p * (1 - a)) ^ n := by
  have h := bernoulliAverage_mono p hp hp' n conditionalSuccess
    (fun k => a ^ k) conditional
  rw [bernoulliAverage_geometric] at h
  exact Rat.le_trans averaged h

theorem pow_mono_nonneg (x y : Rat) (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hy : 0 ≤ y := Rat.le_trans hx hxy
      have hp : 0 ≤ x ^ n := Rat.pow_nonneg hx
      have h₁ := Rat.mul_le_mul_of_nonneg_left hxy hp
      have h₂ := Rat.mul_le_mul_of_nonneg_right ih hy
      simp only [Rat.pow_succ]
      exact Rat.le_trans h₁ h₂

/-- A uniformly sampled vector in a `d`-dimensional binary space is zero with
probability `2^(-d)`.  The counting justification is a separate obligation. -/
def zeroProbability (d : Nat) : Rat := (1 / 2 : Rat) ^ d

theorem zeroProbability_nonneg (d : Nat) : 0 ≤ zeroProbability d := by
  exact Rat.pow_nonneg (by grind)

theorem zeroProbability_le_one (d : Nat) : zeroProbability d ≤ 1 := by
  induction d with
  | zero => simp [zeroProbability]
  | succ d ih =>
      have hp := zeroProbability_nonneg d
      simp only [zeroProbability, Rat.pow_succ] at *
      grind

theorem zeroProbability_antitone (d L : Nat) (hd : d ≤ L) :
    zeroProbability L ≤ zeroProbability d := by
  induction L with
  | zero =>
      have : d = 0 := by omega
      subst d
      exact Rat.le_refl
  | succ L ih =>
      by_cases heq : d = L + 1
      · subst d
        exact Rat.le_refl
      · have hdL : d ≤ L := by omega
        have h := ih hdL
        have hp := zeroProbability_nonneg L
        have hs : zeroProbability (L + 1) ≤ zeroProbability L := by
          simp only [zeroProbability, Rat.pow_succ] at *
          grind
        exact Rat.le_trans hs h

/-- The last inequality in (6.25), including the sign obligations. -/
theorem geometric_le_dimension_bound (d L n : Nat) (hd : d ≤ L)
    (a : Rat) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (1 - zeroProbability d * (1 - a)) ^ n ≤
      (1 - zeroProbability L * (1 - a)) ^ n := by
  have hp := zeroProbability_nonneg d
  have hp' := zeroProbability_le_one d
  have hdL := zeroProbability_antitone d L hd
  have hna : 0 ≤ 1 - a := by grind
  have hprod := Rat.mul_le_mul_of_nonneg_right hdL hna
  have hnprod := Rat.mul_le_mul_of_nonneg_right hp' hna
  apply pow_mono_nonneg
  · grind
  · grind

/-- Lemma 6.8's numerical conclusion, conditional on the repeated-game and
averaging premises.  In particular these hypotheses must be proved for the
same augmented strategy, including its fixed advice. -/
theorem projection_upper_bound
    (d L n : Nat) (hd : d ≤ L) (a success : Rat)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (conditionalSuccess : Nat → Rat)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage (zeroProbability d) n conditionalSuccess) :
    success ≤ (1 - zeroProbability L * (1 - a)) ^ n := by
  have hs := success_le_geometric (zeroProbability d) a success n
    conditionalSuccess (zeroProbability_nonneg d) (zeroProbability_le_one d)
    conditional averaged
  exact Rat.le_trans hs (geometric_le_dimension_bound d L n hd a ha ha')

def decoderThreshold (theta : Rat) (q : Nat) : Rat := theta ^ 3 / (64 * (q : Rat))

theorem decoderThreshold_pos (theta : Rat) (q : Nat)
    (htheta : 0 < theta) (hq : 0 < q) : 0 < decoderThreshold theta q := by
  have hq' : (0 : Rat) < (q : Rat) := Rat.natCast_pos.mpr hq
  have ht := Rat.pow_pos (n := 3) htheta
  have hd : (0 : Rat) < 64 * (q : Rat) := by grind
  unfold decoderThreshold
  apply (Rat.lt_div_iff hd).mpr
  simpa using ht

/-- An elementary Archimedean bound for rational parameters. -/
theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

/-- The estimate `b^n ≤ 1 / (1+n(1-b))` without division. -/
theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

/-- Positive powers of a rational base below one eventually fall below every
positive rational threshold; this supplies the search target in (4.4). -/
theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

theorem zeroProbability_pos (d : Nat) : 0 < zeroProbability d := by
  exact Rat.pow_pos (by grind)

theorem exists_repetition_length (L q : Nat) (a theta : Rat)
    (ha : 0 ≤ a) (ha' : a < 1) (htheta : 0 < theta) (hq : 0 < q) :
    ∃ t : Nat, 0 < t ∧
      (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q := by
  have hp := zeroProbability_pos L
  have hp' := zeroProbability_le_one L
  have hc : 0 < 1 - a := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hp' (Rat.le_of_lt hc)
  have hpos := Rat.mul_pos hp hc
  apply exists_power_lt
  · grind
  · grind
  · exact decoderThreshold_pos theta q htheta hq

/-- Proposition 6.9's contradiction, with its dependency boundary visible.
`extraction` is the entire lower-bound implication; `upper` must bound every
strategy of the same type, with all allowed advice; `gap` is (4.4). -/
theorem soundness_of_bounds
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (delta lower upperBound : Rat)
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, lower ≤ success strategy)
    (upper : ∀ strategy, success strategy ≤ upperBound)
    (gap : upperBound < lower) :
    ∀ labeling, acceptance labeling ≤ delta := by
  intro labeling
  apply Rat.not_lt.mp
  intro hbad
  obtain ⟨strategy, hlow⟩ := extraction labeling hbad
  have h : lower ≤ upperBound := Rat.le_trans hlow (upper strategy)
  exact (Rat.not_lt.mpr h) gap

/-- Proposition 6.9 specialized to (6.25) and (4.4). Every occurrence of
`strategy` is the same object, so fixed advice cannot silently change between
the lower and upper bounds. -/
theorem soundness_from_repetition
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (dimension : Strategy → Nat)
    (conditionalSuccess : Strategy → Nat → Rat)
    (delta a theta : Rat) (q L t : Nat) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (dimension_le : ∀ strategy, dimension strategy ≤ L)
    (conditional : ∀ strategy k, conditionalSuccess strategy k ≤ a ^ k)
    (averaged : ∀ strategy, success strategy ≤
      bernoulliAverage (zeroProbability (dimension strategy)) t
        (conditionalSuccess strategy))
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, decoderThreshold theta q ≤ success strategy)
    (gap : (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q) :
    ∀ labeling, acceptance labeling ≤ delta := by
  apply soundness_of_bounds acceptance success delta (decoderThreshold theta q)
    ((1 - zeroProbability L * (1 - a)) ^ t) extraction
  · intro strategy
    exact projection_upper_bound (dimension strategy) L t (dimension_le strategy)
      a (success strategy) ha ha' (conditionalSuccess strategy)
      (conditional strategy) (averaged strategy)
  · exact gap

end UniqueGamesTheorem.Soundness.RepetitionUpper

end

end OAI
