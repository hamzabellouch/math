import Mathlib
import OAI.Computability.MaxCut.Games.Deletion
import OAI.Computability.MaxCut.Games.HarmonicLoss

namespace OAI

namespace MaxCutGames.Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

/-- Turn the fixed generic vector subspace into its actual logical characters. -/
def logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    Submodule (ZMod 2) (BinaryDual (F := F)) :=
  S.map traceDualEquiv.toLinearMap

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem traceSpace_logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    traceSpace (logicalCharacters S) = S := by
  exact (Submodule.map_symm_eq_iff traceDualEquiv).mpr rfl

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem logicalCharacters_finrank (S : Submodule (ZMod 2) (Vec F)) :
    Module.finrank (ZMod 2) (logicalCharacters S) = Module.finrank (ZMod 2) S :=
  traceDualEquiv.finrank_map_eq S

omit [CharP F 2] [Algebra (ZMod 2) F] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem theta_pos : 0 < fieldLineTheta F := by
  have hc : (0 : ℚ) < Nat.card (FieldLine F) := by
    exact_mod_cast (card_FieldLine_pos (F := F))
  exact inv_pos.mpr hc

/-- All probabilities concern the actual recursive noise choices. The field
and generic top space satisfy separately proved finite-field properties; no
probability estimate for the whole recursive gadget is an input. -/
theorem full_lift_detection :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (r₀ : ℕ) (ε : ℚ) (_hr₀ : 0 < r₀)
      (_hbudget : badRankCoefficient r₀ * ε ≤ 1)
      (_hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
      (S₀ : Submodule (ZMod 2) (Vec F))
      (_hrank : Module.finrank (ZMod 2) S₀ = r₀) (_hS₀ : IsGeneric S₀)
      (L : Lift (Stage.iterate J hJ Q (depth r₀ (fieldLineTheta F)))
        (⊤ : Submodule (ZMod 2) (BinaryDual (F := F)))),
      (1 / 4 : ℚ) ≤ detectionProbability J hJ Q
        (depth r₀ (fieldLineTheta F)) ⊤ L := by
  intro J hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  classical
  let S := logicalCharacters S₀
  have hSrank : Module.finrank (ZMod 2) S = r₀ :=
    (logicalCharacters_finrank S₀).trans hrank
  have hSgeneric : IsGeneric (traceSpace S) := by
    simpa only [S, traceSpace_logicalCharacters] using hS₀
  let L₀ := L.restrict (show S ≤ ⊤ from le_top)
  have hdrop := DescentProbability.expected_terminal_loss J hJ Q
    (fun T => ¬ IsGeneric (traceSpace T)) r₀ (badRankCoefficient r₀)
    (fieldLineTheta F) ε (badRankCoefficient_nonneg r₀) (le_of_lt theta_pos) hbudget
    (by
      intro s T L' hT
      exact OutgoingHarmonic.descendant_harmonic_loss_le hJ Q s T L' r₀ hT)
    (by
      intro s T L' hT
      have hf := FreshGenericity.descendant_bad_le hJ Q s T L' r₀ ε hT hgeneric
      refine (le_of_eq ?_).trans hf
      apply Finset.expect_congr rfl
      intro i _
      by_cases hi : IsGeneric (traceSpace (childDomain J hJ Q s T L' i))
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_true_eq_false, ite_false]
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_false_eq_true, ite_true])
    (depth r₀ (fieldLineTheta F)) S L₀ hSrank.le
  have hdepth := depth_budget r₀ (fieldLineTheta F) theta_pos
  have hpotential : MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q (depth r₀ (fieldLineTheta F)) S L₀ := by
    simp only [hSgeneric, not_true_eq_false, ite_false, mul_zero, add_zero, hSrank] at hdrop ⊢
    linarith
  exact quarter_detection_of_restricted_terminal_potential J hJ Q
    (depth r₀ (fieldLineTheta F)) S ⊤ le_top L (hSrank.symm ▸ hr₀) hpotential

end

end MaxCutGames.Gadget.BaseDetection

namespace MaxCutGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- The logical kernel viewed as a submodule of the ambient input space. -/
def shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) : Submodule 𝕜 P :=
  (LinearMap.ker lam).map R.subtype

abbrev Space (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) := P ⧸ shiftKernel R lam

def projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    P →ₗ[𝕜] Space R lam := (shiftKernel R lam).mkQ

theorem projection_surjective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    Function.Surjective (projection R lam) := (shiftKernel R lam).mkQ_surjective

theorem mem_shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : P) :
    x ∈ shiftKernel R lam ↔ ∃ h : R, lam h = 0 ∧ (h : P) = x := Iff.rfl

theorem projection_eq_zero (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    projection R lam (h : P) = 0 ↔ lam h = 0 := by
  change (Submodule.Quotient.mk (h : P) : Space R lam) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_shiftKernel]
  constructor
  · rintro ⟨k, hk, hkh⟩
    have : k = h := Subtype.ext hkh
    simpa [this] using hk
  · intro hh
    exact ⟨h, hh, rfl⟩

/-- Inclusion of the quotient shift space into the ambient quotient. -/
def quotientShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    (R ⧸ LinearMap.ker lam) →ₗ[𝕜] Space R lam :=
  (LinearMap.ker lam).liftQ ((projection R lam).comp R.subtype) (by
    intro h hh
    exact (projection_eq_zero R lam h).mpr hh)

@[simp] theorem quotientShift_mk (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    quotientShift R lam (Submodule.Quotient.mk h) = projection R lam (h : P) := rfl

/-- The logical alphabet is realized as actual linear shifts of the quotient. -/
noncomputable def logicalShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : B →ₗ[𝕜] Space R lam :=
  (quotientShift R lam).comp (lam.quotKerEquivOfSurjective hlam).symm.toLinearMap

@[simp] theorem logicalShift_lambda (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (h : R) :
    logicalShift R lam hlam (lam h) = projection R lam (h : P) := by
  simp [logicalShift, LinearMap.quotKerEquivOfSurjective_symm_apply]

theorem logicalShift_injective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : Function.Injective (logicalShift R lam hlam) := by
  intro a b hab
  obtain ⟨h, rfl⟩ := hlam a
  obtain ⟨k, rfl⟩ := hlam b
  rw [logicalShift_lambda, logicalShift_lambda] at hab
  have hz : projection R lam ((h - k : R) : P) = 0 := by
    change projection R lam ((h : P) - (k : P)) = 0
    rw [map_sub, hab, sub_self]
  have := (projection_eq_zero R lam (h - k)).mp hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using this)

/-- Equivariance under every allowed shift; no linearity of `C` is assumed. -/
def Equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (C : P → B) : Prop :=
  ∀ (u : P) (h : R), C (u + (h : P)) = C u + lam h

/-- An output difference is unchanged by every logical shift. -/
theorem difference_shift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) (h : R) :
    C (u + (h : P) + a) - C (u + (h : P)) = C (u + a) - C u := by
  have he : u + (h : P) + a = (u + a) + (h : P) := by
    simp only [add_assoc, add_comm (h : P) a]
  rw [he, hC, hC, add_sub_add_right_eq_sub]

/-- Translating by a logical shift bijects output fibers even after conditioning
on an arbitrary shift-invariant event. -/
def conditionedShiftEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (D : P → Prop)
    (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) (h : R) :
    {u : P // C u = b ∧ D u} ≃ {u : P // C u = b + lam h ∧ D u} where
  toFun u := ⟨u.val + (h : P), by
    exact ⟨(hC u.val h).trans (congrArg (fun x => x + lam h) u.property.1),
      (hD u.val h).mpr u.property.2⟩⟩
  invFun u := ⟨u.val + ((-h : R) : P), by
    constructor
    · rw [hC u.val (-h), u.property.1, map_neg, add_neg_cancel_right]
    · exact (hD u.val (-h)).mpr u.property.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

/-- Surjectivity makes all output fibers equally large inside an invariant
event, without assuming that this event has positive probability. -/
noncomputable def conditionedFiberEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u)
    (b c : B) : {u : P // C u = b ∧ D u} ≃ {u : P // C u = c ∧ D u} := by
  classical
  let h : R := Classical.choose (hlam (c - b))
  have hh : lam h = c - b := Classical.choose_spec (hlam (c - b))
  have he : b + lam h = c := by rw [hh, add_comm, sub_add_cancel]
  simpa only [he] using conditionedShiftEquiv R lam C hC D hD b h

theorem conditioned_fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u)
    (b c : B) :
    Nat.card {u : P // C u = b ∧ D u} = Nat.card {u : P // C u = c ∧ D u} :=
  Nat.card_congr (conditionedFiberEquiv R lam hlam C hC D hD b c)

theorem output_fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (b c : B) : Nat.card {u : P // C u = b} = Nat.card {u : P // C u = c} := by
  simpa only [and_true] using conditioned_fiber_card R lam hlam C hC
    (fun _ => True) (fun _ _ => Iff.rfl) b c

/-- Fixing the additive perturbation and the observed difference leaves the
initial output uniform: the joint fibers have equal cardinality for all outputs. -/
theorem difference_fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (a : P) (d b c : B) :
    Nat.card {u : P // C u = b ∧ C (u + a) - C u = d} =
      Nat.card {u : P // C u = c ∧ C (u + a) - C u = d} := by
  apply conditioned_fiber_card R lam hlam C hC
  intro u h
  rw [difference_shift R lam C hC]

/-- Splitting an invariant event into its output fibers. -/
def conditionedSigmaEquiv (C : P → B) (D : P → Prop) :
    {u : P // D u} ≃ Σ b : B, {u : P // C u = b ∧ D u} where
  toFun u := ⟨C u.val, ⟨u.val, rfl, u.property⟩⟩
  invFun u := ⟨u.2.val, u.2.property.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨b, u, hu, hD⟩; cases hu; rfl

/-- An invariant event factors as an independent logical output and one fiber. -/
noncomputable def conditionedProductEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) :
    {u : P // D u} ≃ B × {u : P // C u = b ∧ D u} :=
  ((conditionedSigmaEquiv C D).trans
    (Equiv.sigmaCongrRight (fun c => conditionedFiberEquiv R lam hlam C hC D hD c b))).trans
    (Equiv.sigmaEquivProd _ _)

@[simp] theorem conditionedProductEquiv_fst (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B)
    (u : {u : P // D u}) :
    (conditionedProductEquiv R lam hlam C hC D hD b u).1 = C u.val := rfl

/-- Exact counting factorization underlying the conditional uniform law. -/
theorem conditioned_card_factorization [Finite P] [Finite B]
    (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) :
    Nat.card {u : P // D u} = Nat.card B * Nat.card {u : P // C u = b ∧ D u} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (conditionedProductEquiv R lam hlam C hC D hD b)

theorem difference_card_factorization [Finite P] [Finite B]
    (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (a : P) (d b : B) :
    Nat.card {u : P // C (u + a) - C u = d} =
      Nat.card B * Nat.card {u : P // C u = b ∧ C (u + a) - C u = d} := by
  apply conditioned_card_factorization R lam hlam C hC
  intro u h
  rw [difference_shift R lam C hC]

theorem output_constant_on_fibers (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (x y : P)
    (hxy : projection R lam x = projection R lam y) : C x = C y := by
  have hm : x - y ∈ shiftKernel R lam := (Submodule.Quotient.eq _).mp hxy
  obtain ⟨h, hh, hval⟩ := (mem_shiftKernel R lam _).mp hm
  have he : y + (h : P) = x := by rw [hval, add_comm, sub_add_cancel]
  simpa only [he, hh, add_zero] using hC y h

def output (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) : Space R lam → B :=
  _root_.Quotient.lift C (fun _ _ h =>
    output_constant_on_fibers R lam C hC _ _ (_root_.Quotient.sound h))

@[simp] theorem output_projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u : P) :
    output R lam C hC (projection R lam u) = C u := rfl

theorem output_equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (x : Space R lam) (b : B) :
    output R lam C hC (x + logicalShift R lam hlam b) = output R lam C hC x + b := by
  obtain ⟨u, rfl⟩ := projection_surjective R lam x
  obtain ⟨h, rfl⟩ := hlam b
  rw [logicalShift_lambda, ← map_add, output_projection, output_projection]
  exact hC u h

/-- Noise pushforward preserves the change event pointwise, before averaging. -/
theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]

/-- Pulling a quotient character back recovers its prescribed logical value. -/
theorem character_pullback_shift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (g : Space R lam →ₗ[𝕜] 𝕜) (h : R) :
    (g.comp (projection R lam)) (h : P) =
      (g.comp (logicalShift R lam hlam)) (lam h) := by
  simp only [LinearMap.comp_apply, logicalShift_lambda]

/-- Pullback preserves the detection event of an already selected family of
quotient characters, including a section of the logical restriction map. -/
theorem detection_iff {I : Type*} (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (family : I → Space R lam →ₗ[𝕜] 𝕜) (a : P) :
    (∃ i, family i (projection R lam a) ≠ 0) ↔
      ∃ i, (family i).comp (projection R lam) a ≠ 0 := Iff.rfl

/-- Translation by the logical kernel parametrizes a quotient fiber. -/
def fiberMap (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    shiftKernel R lam → {u : P // projection R lam u = projection R lam a} :=
  fun h => ⟨a + (h : P), by
    have hh : projection R lam (h : P) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h.property
    rw [map_add, hh, add_zero]⟩

theorem fiberMap_bijective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    Function.Bijective (fiberMap R lam a) := by
  constructor
  · intro h k he
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val he)
  · intro u
    have hm : u.val - a ∈ shiftKernel R lam :=
      (Submodule.Quotient.eq _).mp u.property
    refine ⟨⟨u.val - a, hm⟩, Subtype.ext ?_⟩
    change a + (u.val - a) = u.val
    rw [add_comm, sub_add_cancel]

/-- Every fiber has the same cardinality, justifying uniform-input pushforward. -/
theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  obtain ⟨a, rfl⟩ := projection_surjective R lam x
  exact (Nat.card_congr (Equiv.ofBijective _ (fiberMap_bijective R lam a))).symm

end MaxCutGames.Gadget.Quotient

namespace MaxCutGames.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

def shifts (s : Stage k B) : Submodule k s.Input := LinearMap.range s.embed

noncomputable def shiftEquiv (s : Stage k B) : s.Shift ≃ₗ[k] shifts s :=
  LinearEquiv.ofInjective s.embed s.embed_injective

@[simp] theorem shiftEquiv_coe (s : Stage k B) (h : s.Shift) :
    ((shiftEquiv s h : shifts s) : s.Input) = s.embed h := rfl

@[simp] theorem embed_shiftEquiv_symm (s : Stage k B) (h : shifts s) :
    s.embed ((shiftEquiv s).symm h) = (h : s.Input) :=
  LinearEquiv.ofInjective_symm_apply s.embed h

noncomputable def logical (s : Stage k B) : shifts s →ₗ[k] B :=
  s.logical.comp (shiftEquiv s).symm.toLinearMap

@[simp] theorem logical_shiftEquiv (s : Stage k B) (h : s.Shift) :
    logical s (shiftEquiv s h) = s.logical h := by
  simp [logical]

theorem logical_surjective (s : Stage k B) : Function.Surjective (logical s) := by
  intro b
  obtain ⟨h, hh⟩ := s.logical_surjective b
  exact ⟨shiftEquiv s h, (logical_shiftEquiv s h).trans hh⟩

theorem equivariant (s : Stage k B) :
    Quotient.Equivariant (shifts s) (logical s) s.output := by
  intro u h
  have he := s.equivariant u ((shiftEquiv s).symm h)
  simpa only [embed_shiftEquiv_symm, logical, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using he

abbrev Space (s : Stage k B) := Quotient.Space (shifts s) (logical s)

noncomputable def projection (s : Stage k B) : s.Input →ₗ[k] Space s :=
  Quotient.projection (shifts s) (logical s)

theorem projection_surjective (s : Stage k B) : Function.Surjective (projection s) :=
  Quotient.projection_surjective (shifts s) (logical s)

instance spaceFinite (s : Stage k B) : Finite (Space s) :=
  Finite.of_surjective (projection s) (projection_surjective s)

noncomputable def shift (s : Stage k B) : B →ₗ[k] Space s :=
  Quotient.logicalShift (shifts s) (logical s) (logical_surjective s)

theorem shift_injective (s : Stage k B) : Function.Injective (shift s) :=
  Quotient.logicalShift_injective (shifts s) (logical s) (logical_surjective s)

@[simp] theorem shift_logical (s : Stage k B) (h : s.Shift) :
    shift s (s.logical h) = projection s (s.embed h) := by
  rw [← logical_shiftEquiv s h]
  exact Quotient.logicalShift_lambda (shifts s) (logical s) (logical_surjective s)
    (shiftEquiv s h)

noncomputable def output (s : Stage k B) : Space s → B :=
  Quotient.output (shifts s) (logical s) s.output (equivariant s)

@[simp] theorem output_projection (s : Stage k B) (u : s.Input) :
    output s (projection s u) = s.output u := rfl

theorem output_equivariant (s : Stage k B) (x : Space s) (b : B) :
    output s (x + shift s b) = output s x + b :=
  Quotient.output_equivariant (shifts s) (logical s) (logical_surjective s)
    s.output (equivariant s) x b

/-- Original finite noise choices, pushed through the actual quotient map. -/
noncomputable def noise (s : Stage k B) : s.Noise → Space s :=
  fun t => projection s (s.noise t)

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

theorem character_logical (s : Stage k B) (g : Space s →ₗ[k] k) (h : s.Shift) :
    (g.comp (projection s)) (s.embed h) = (g.comp (shift s)) (s.logical h) := by
  simp only [LinearMap.comp_apply, shift_logical]

theorem noise_detection_iff {I : Type*} (s : Stage k B)
    (family : I → Space s →ₗ[k] k) (t : s.Noise) :
    (∃ i, family i (noise s t) ≠ 0) ↔
      ∃ i, (family i).comp (projection s) (s.noise t) ≠ 0 := Iff.rfl

/-- The quotient is again a finite stage; its logical map is now the identity. -/
noncomputable def toStage [Finite B] (s : Stage k B) : Stage k B where
  Input := Space s
  Shift := B
  Noise := s.Noise
  embed := shift s
  embed_injective := shift_injective s
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := output s
  equivariant := output_equivariant s
  noise := noise s

end MaxCutGames.Gadget.StageQuotient

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

namespace MaxCutGames.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

/-- Every logical character is extended to the ambient input space. -/
def IsFullLift (ι : B →ₗ[K] V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : Prop :=
  ∀ (z : Module.Dual K B) (b : B), ψ z (ι b) = z b

/-- Detection by any member of a character family. Classical decidability
only selects an event indicator on the finite noise sample space. -/
noncomputable def characterDetection (noise : Ω → V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : ℚ := by
  classical
  exact probability (fun ω => ∃ z : Module.Dual K B, ψ z (noise ω) ≠ 0)

theorem exists_leftInverse_of_logical_injective (ι : B →ₗ[K] V)
    (T : V →ₗ[K] E) (hinjective : Function.Injective (T.comp ι)) :
    ∃ l : E →ₗ[K] B, l.comp (T.comp ι) = LinearMap.id :=
  (T.comp ι).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

/-- The left inverse supplies an actual full character lift through `T`. -/
theorem fullLift_of_leftInverse (ι : B →ₗ[K] V) (T : V →ₗ[K] E)
    (l : E →ₗ[K] B) (hleft : l.comp (T.comp ι) = LinearMap.id) :
    IsFullLift ι (l.comp T).dualMap := by
  intro z b
  change z (l (T (ι b))) = z b
  have hb : l (T (ι b)) = b := LinearMap.congr_fun hleft b
  rw [hb]

/-- A full-lift detection guarantee transfers to every target map injective
on the logical alphabet. -/
theorem target_detection_of_full_lift_bound [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hfull : ∀ ψ : Module.Dual K B →ₗ[K] Module.Dual K V,
      IsFullLift ι ψ → q ≤ characterDetection noise ψ)
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  classical
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  calc
    q ≤ characterDetection noise (l.comp T).dualMap :=
      hfull _ (fullLift_of_leftInverse ι T l hl)
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      unfold characterDetection
      apply probability_mono
      rintro ω ⟨z, hz⟩ hzero
      apply hz
      change z (l (T (noise ω))) = 0
      simp [hzero]

/-- Equivalent useful interface when the recursive calculation already gives
detection of every vector-valued linear retraction of the logical inclusion. -/
theorem target_detection_of_retraction_bound [DecidableEq B] [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hretract : ∀ L : V →ₗ[K] B, L.comp ι = LinearMap.id →
      q ≤ probability (fun ω => L (noise ω) ≠ 0))
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  have hcomp : (l.comp T).comp ι = LinearMap.id := by
    simpa only [LinearMap.comp_assoc] using hl
  calc
    q ≤ probability (fun ω => (l.comp T) (noise ω) ≠ 0) := hretract _ hcomp
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      apply probability_mono
      intro ω h hzero
      apply h
      simp [hzero]

end MaxCutGames.Gadget.DetectionBridge

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace MaxCutGames.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

noncomputable def pullbackFullLift (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    Lift s (⊤ : Submodule k (Module.Dual k B)) where
  family :=
    { toFun z := (ψ z.val).comp (StageQuotient.projection s)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  agrees := by
    intro z h
    change ψ z.val (StageQuotient.projection s (s.embed h)) = z.val (s.logical h)
    rw [← StageQuotient.shift_logical]
    exact hψ z.val (s.logical h)

omit [Finite B] in
theorem pullback_detection_iff (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) (n : s.Noise) :
    (∃ z, (pullbackFullLift s ψ hψ).family z (s.noise n) ≠ 0) ↔
      ∃ z, ψ z (StageQuotient.noise s n) ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, Submodule.mem_top⟩, hz⟩

omit [Finite B] in
/-- Any checked full-lift probability bound before quotienting applies to
every full family on the actual quotient, on the same noise sampler. -/
theorem full_detection_after_quotient (s : Stage k B) [Fintype s.Noise] (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    q ≤ characterDetection (StageQuotient.noise s) ψ := by
  classical
  have h := hfull (pullbackFullLift s ψ hψ)
  simpa only [characterDetection, pullback_detection_iff] using h

omit [Finite B] in
/-- The form consumed by the injection enlargement: injectivity on the base
logical alphabet suffices for the same detection probability. -/
theorem target_detection_after_quotient (s : Stage k B) [Fintype s.Noise]
    {E : Type*} [AddCommGroup E] [Module k E] [DecidableEq E]
    (T : StageQuotient.Space s →ₗ[k] E) (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (hinj : Function.Injective (T.comp (StageQuotient.shift s))) :
    q ≤ probability (fun n => T (StageQuotient.noise s n) ≠ 0) := by
  exact target_detection_of_full_lift_bound (StageQuotient.noise s)
    (StageQuotient.shift s) T q (full_detection_after_quotient s q hfull) hinj

end MaxCutGames.Gadget.QuotientDetection

namespace MaxCutGames.Gadget.EmbeddedConditional

open scoped BigOperators

variable {k P R B Z M : Type*} [Ring k]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup B] [Module k B] [Fintype B]
variable [AddCommMonoid M] [Module ℚ≥0 M]

/-- Exact conditional uniformity for an embedded carrier of logical shifts.
No injectivity of the embedding is needed for this averaging statement. -/
theorem expect_uniform_output_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (D : P → Z) (hD : ∀ u h, D (u + e h) = D u)
    (f : B → Z → M) :
    (𝔼 u, f (C u) (D u)) = 𝔼 u, 𝔼 b : B, f b (D u) := by
  classical
  have hs (b : B) :
      (𝔼 u, f (C u + b) (D u)) = 𝔼 u, f (C u) (D u) := by
    obtain ⟨h, rfl⟩ := hlam b
    apply Fintype.expect_equiv (Equiv.addRight (e h))
    intro u
    simp only [Equiv.coe_addRight, hC, hD]
  calc
    (𝔼 u, f (C u) (D u)) = 𝔼 b : B, 𝔼 u, f (C u + b) (D u) := by
      simp only [hs, Fintype.expect_const]
    _ = 𝔼 u, 𝔼 b : B, f (C u + b) (D u) := Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 b : B, f b (D u) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Fintype.expect_equiv (Equiv.addLeft (C u))
      intro b
      rfl

/-- Unconditional uniformity is the constant-observable instance. -/
theorem expect_equivariant_output (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (f : B → M) :
    (𝔼 u, f (C u)) = 𝔼 b : B, f b := by
  have he := expect_uniform_output_embedded e lam hlam C hC
    (fun _ => ()) (fun _ _ => rfl) (fun b _ => f b)
  simpa only [Fintype.expect_const] using he

/-- Surjective linear maps send uniform finite input to uniform output. -/
theorem expect_linear_surjective (f : P →ₗ[k] B) (hf : Function.Surjective f)
    (test : B → M) : (𝔼 u, test (f u)) = 𝔼 b : B, test b := by
  apply expect_equivariant_output (LinearMap.id : P →ₗ[k] P) f hf f
  intro u h
  exact f.map_add u h

/-- Fixed-perturbation conditional uniformity without a range conversion. -/
theorem expect_uniform_difference_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (a : P) (f : B → B → M) :
    (𝔼 u, f (C u) (C (u + a) - C u)) =
      𝔼 u, 𝔼 b : B, f b (C (u + a) - C u) := by
  apply expect_uniform_output_embedded e lam hlam C hC
  intro u h
  have he : u + e h + a = (u + a) + e h := by
    simp only [add_assoc, add_comm (e h) a]
  rw [he, hC, hC, add_sub_add_right_eq_sub]

end MaxCutGames.Gadget.EmbeddedConditional

namespace MaxCutGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem compLeft_surjective (lam : R →ₗ[k] B) (hlam : Function.Surjective lam) :
    Function.Surjective (lam.compLeft I) := by
  intro b
  choose h hh using fun i => hlam (b i)
  exact ⟨h, funext hh⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem aggregate_single (J : I → B →ₗ[k] X × B) (i : I) (b : B) :
    aggregate J (Pi.single i b) = J i b := by
  classical
  change (∑ j, J j ((Pi.single i b : I → B) j)) = J i b
  simp only [LinearMap.apply_single]
  simp

omit [Fintype I] [Fintype P] [Fintype B] [DecidableEq B] in
theorem child_outputs_perturb (C : P → B) (u : I → P) (i : I) (a : P) :
    (fun j => C ((u + (Pi.single i a : I → P)) j)) =
      (fun j => C (u j)) + (Pi.single i (C (u i + a) - C (u i)) : I → B) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [add_comm (C (u i)), sub_add_cancel]
  · simp [Pi.single_eq_of_ne hj]

omit [Module k P] in
omit [Fintype P] [Fintype X] [Fintype B] [DecidableEq B] in
theorem parent_output_perturb (J : I → B →ₗ[k] X × B) (C : P → B)
    (F : X × B → B) (u : I → P) (i : I) (a : P) :
    F (aggregate J (fun j => C ((u + (Pi.single i a : I → P)) j))) =
      F (aggregate J (fun j => C (u j)) + J i (C (u i + a) - C (u i))) := by
  rw [child_outputs_perturb, map_add, aggregate_single]

/-- The exact conditional-uniform and coordinate-marginal law for a fixed
selected index and fixed child perturbation. -/
theorem expect_change_at_index (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (i : I) (a : P) :
    (𝔼 u : I → P,
      change F (aggregate J (fun j => C (u j))) (J i (C (u i + a) - C (u i)))) =
      𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
  have hCt : ∀ (u : I → P) (h : I → R),
      (fun j => C ((u + (e.compLeft I) h) j)) =
        (fun j => C (u j)) + (lam.compLeft I) h := by
    intro u h
    funext j
    exact hC (u j) (h j)
  have hDt : ∀ (u : I → P) (h : I → R),
      C ((u + (e.compLeft I) h) i + a) - C ((u + (e.compLeft I) h) i) =
        C (u i + a) - C (u i) := by
    intro u h
    change C (u i + e (h i) + a) - C (u i + e (h i)) = _
    have he : u i + e (h i) + a = (u i + a) + e (h i) := by
      simp only [add_assoc, add_comm (e (h i)) a]
    rw [he, hC, hC, add_sub_add_right_eq_sub]
  calc
    _ = 𝔼 u : I → P, 𝔼 b : I → B,
        change F (aggregate J b) (J i (C (u i + a) - C (u i))) :=
      EmbeddedConditional.expect_uniform_output_embedded
        (e.compLeft I) (lam.compLeft I) (compLeft_surjective lam hlam)
        (fun u j => C (u j)) hCt (fun u => C (u i + a) - C (u i)) hDt
        (fun b d => change F (aggregate J b) (J i d))
    _ = 𝔼 u : I → P, 𝔼 z : X × B,
        change F z (J i (C (u i + a) - C (u i))) := by
      apply Finset.expect_congr rfl
      intro u _
      exact EmbeddedConditional.expect_linear_surjective (aggregate J) hJ
        (fun z => change F z (J i (C (u i + a) - C (u i))))
    _ = 𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
      exact EmbeddedConditional.expect_linear_surjective
        (LinearMap.proj i : (I → P) →ₗ[k] P)
        (fun x => ⟨fun _ => x, rfl⟩)
        (fun x : P => 𝔼 z : X × B, change F z (J i (C (x + a) - C x)))

omit [DecidableEq I] in
/-- The averaged block kernel includes zero differences by multiplication with
their nonzero indicator. -/
theorem kernel_all (J : I → B →ₗ[k] X × B) (F : X × B → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ)
    (d : B) :
    (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ * (if d ≠ 0 then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · simp only [ite_eq_left hd, mul_one]
    exact hk d hd

/-- One exact nonlinear recurrence on the actual product input and the actual
single-coordinate noise. The only remaining block obligation is `hk`. -/
theorem parent_change_recurrence {N : Type*} [Fintype N]
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (C : P → B) (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (noise : N → P) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ) :
    (𝔼 i, 𝔼 n : N, 𝔼 u : I → P,
      if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
        F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
      ρ * (𝔼 n : N, 𝔼 x : P, if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
  classical
  have hpoint (i : I) (n : N) :
      (𝔼 u : I → P,
        if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
          F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
        𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
    simp_rw [parent_output_perturb]
    exact expect_change_at_index J hJ e lam hlam C hC F i (noise n)
  simp_rw [hpoint]
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 n : N, 𝔼 x : P, 𝔼 i,
        𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
      apply Finset.expect_congr rfl
      intro n _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 n : N, 𝔼 x : P,
        ρ * (if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      apply Finset.expect_congr rfl
      intro x _
      simpa only [ne_eq, sub_eq_zero] using kernel_all J F ρ hk (C (x + noise n) - C x)
    _ = _ := by simp only [← Finset.mul_expect]

end MaxCutGames.Gadget.NonlinearRecurrence

end OAI
