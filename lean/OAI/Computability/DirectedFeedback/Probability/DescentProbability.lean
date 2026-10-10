import Mathlib
import OAI.Computability.DirectedFeedback.Games.Harmonic

namespace OAI

namespace DFVSGames.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable instance noiseFintype (n : ℕ) : Fintype (Stage.iterate J hJ Q n).Noise := by
  induction n with
  | zero => exact Fintype.ofFinite B
  | succ n ih =>
    exact inferInstanceAs (Fintype (I × (Stage.iterate J hJ Q n).Noise))

noncomputable def terminalPotential (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  average (fun t => DFVSGames.Gadget.Harmonic.harmonic (leafRank J hJ Q n S L t))

omit [FiniteDimensional k B] in
@[simp] theorem terminalPotential_zero (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    terminalPotential J hJ Q 0 S L = DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S)) = _
  exact average_const _

omit [FiniteDimensional k B] in
theorem terminalPotential_succ (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    terminalPotential J hJ Q (n + 1) S L =
      average (fun i => terminalPotential J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold terminalPotential average
  change Finset.univ.expect (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    DFVSGames.Gadget.Harmonic.harmonic (leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expected_terminal_loss
    (bad : Submodule k (B →ₗ[k] k) → Prop) [DecidablePred bad]
    (r₀ : ℕ) (C θ ε : ℚ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hsmall : C * ε ≤ 1)
    (hstep : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      average (fun i => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k (childDomain J hJ Q s S L i))) ≤
          3 * θ + C * θ * if bad S then 1 else 0)
    (hfresh : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      probability (fun i => bad (childDomain J hJ Q s S L i)) ≤ ε)
    (n : ℕ) (S : Submodule k (B →ₗ[k] k)) (L : Lift (Stage.iterate J hJ Q n) S)
    (hcap : Module.finrank k S ≤ r₀) :
    DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) - terminalPotential J hJ Q n S L ≤
      4 * n * θ + C * θ * if bad S then 1 else 0 := by
  induction n generalizing S with
  | zero =>
    simp only [terminalPotential_zero, sub_self, Nat.cast_zero, mul_zero, zero_mul,
      zero_add]
    split <;> simp_all [mul_nonneg]
  | succ n ih =>
    let s := Stage.iterate J hJ Q n
    let Sc := childDomain J hJ Q s S L
    let Lc := childLift J hJ Q s S L
    have hchild : average (fun i => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k (Sc i)) -
        terminalPotential J hJ Q n (Sc i) (Lc i)) ≤
        4 * n * θ + C * θ * probability (fun i => bad (Sc i)) := by
      calc
        _ ≤ average (fun i => 4 * n * θ + C * θ * if bad (Sc i) then 1 else 0) := by
          apply average_mono
          intro i
          exact ih (Sc i) (Lc i) ((child_rank_le J hJ Q s S L i).trans hcap)
        _ = _ := by rw [average_add, average_const, average_mul_left]; rfl
    have hdrop := hstep s S L hcap
    have hbad := hfresh s S L hcap
    have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
    rw [terminalPotential_succ]
    rw [average_sub] at hchild
    rw [average_sub, average_const] at hdrop
    change DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
      average (fun i => terminalPotential J hJ Q n (Sc i) (Lc i)) ≤ _
    push_cast
    nlinarith

end DFVSGames.Gadget.DescentProbability

namespace DFVSGames.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def survivalProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  probability (fun t => 0 < leafRank J hJ Q n S L t)

noncomputable def detectionProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ := by
  classical
  exact probability (fun t => ∃ z : S, L.family z ((Stage.iterate J hJ Q n).noise t) ≠ 0)

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_nonneg (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    0 ≤ detectionProbability J hJ Q n S L := by
  classical
  exact probability_nonneg _

omit [FiniteDimensional (ZMod 2) B] in

theorem detectionProbability_restrict_le (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T) :
    detectionProbability J hJ Q n S (L.restrict hST) ≤
      detectionProbability J hJ Q n T L := by
  classical
  apply probability_mono
  rintro t ⟨z, hz⟩
  exact ⟨Submodule.inclusion hST z, hz⟩

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_zero_of_rank_pos
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) (hrank : 0 < Module.finrank (ZMod 2) S) :
    (1 / 2 : ℚ) ≤ detectionProbability J hJ Q 0 S L := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨z, hz⟩ := exists_ne (0 : S)
  have hzval : z.val ≠ 0 := by
    intro he
    exact hz (Subtype.ext he)
  have hex : ∃ b : B, z.val b ≠ 0 := by
    by_contra h
    apply hzval
    ext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  have hagree : L.family z b = z.val b := L.agrees z b
  have hχ : L.family z b ≠ 0 := by rwa [hagree]
  change (1 / 2 : ℚ) ≤ probability (fun b : B => ∃ z : S, L.family z b ≠ 0)
  exact binary_family_detection_ge_half _ (L.family z).toAddMonoidHom b hχ
    (fun b hb => ⟨z, hb⟩)

omit [FiniteDimensional (ZMod 2) B] in
@[simp] theorem survivalProbability_zero
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    survivalProbability J hJ Q 0 S L =
      if 0 < Module.finrank (ZMod 2) S then 1 else 0 := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    if 0 < Module.finrank (ZMod 2) S then (1 : ℚ) else 0) = _
  exact average_const _

omit [FiniteDimensional (ZMod 2) B] in
theorem survivalProbability_succ (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    survivalProbability J hJ Q (n + 1) S L =
      average (fun i => survivalProbability J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold survivalProbability
  change probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    0 < leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2) = _
  exact probability_product _

omit [FiniteDimensional (ZMod 2) B] in
theorem average_child_detection_le (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    average (fun i => detectionProbability J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) ≤
        detectionProbability J hJ Q (n + 1) S L := by
  classical
  unfold detectionProbability
  change _ ≤ probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    ∃ z : S, L.family z ((Stage.iterate J hJ Q (n + 1)).noise t) ≠ 0)
  rw [probability_product]
  apply average_mono
  intro i
  apply probability_mono
  intro t hdetect
  exact child_detection J hJ Q (Stage.iterate J hJ Q n) S L i t hdetect

omit [FiniteDimensional (ZMod 2) B] in
theorem half_survival_le_detection (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    (1 / 2 : ℚ) * survivalProbability J hJ Q n S L ≤
      detectionProbability J hJ Q n S L := by
  induction n generalizing S with
  | zero =>
    rw [survivalProbability_zero]
    split_ifs with hrank
    · simpa only [mul_one] using detectionProbability_zero_of_rank_pos J hJ Q S L hrank
    · simpa only [mul_zero] using detectionProbability_nonneg J hJ Q 0 S L
  | succ n ih =>
    rw [survivalProbability_succ, ← average_mul_left]
    calc
      _ ≤ average (fun i => detectionProbability J hJ Q n
          (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
          (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
        apply average_mono
        intro i
        exact ih _ _
      _ ≤ detectionProbability J hJ Q (n + 1) S L :=
        average_child_detection_le J hJ Q n S L

theorem quarter_detection_of_terminal_potential (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S L) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n S L := by
  have hsurv : (1 / 2 : ℚ) ≤ survivalProbability J hJ Q n S L :=
    survival_probability_ge_half_of_potential (leafRank J hJ Q n S L)
      (Module.finrank (ZMod 2) S) hrank (leafRank_le J hJ Q n S L) hpotential
  have hdet := half_survival_le_detection J hJ Q n S L
  linarith

theorem quarter_detection_of_restricted_terminal_potential (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S (L.restrict hST)) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n T L :=
  (quarter_detection_of_terminal_potential J hJ Q n S (L.restrict hST)
    hrank hpotential).trans (detectionProbability_restrict_le J hJ Q n S T hST L)

end DFVSGames.Gadget.LeafDetection

namespace DFVSGames.Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

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
  have hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q (depth r₀ (fieldLineTheta F)) S L₀ := by
    simp only [hSgeneric, not_true_eq_false, ite_false, mul_zero, add_zero, hSrank] at hdrop ⊢
    linarith
  exact quarter_detection_of_restricted_terminal_potential J hJ Q
    (depth r₀ (fieldLineTheta F)) S ⊤ le_top L (hSrank.symm ▸ hr₀) hpotential

end

end DFVSGames.Gadget.BaseDetection

namespace DFVSGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

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

def quotientShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    (R ⧸ LinearMap.ker lam) →ₗ[𝕜] Space R lam :=
  (LinearMap.ker lam).liftQ ((projection R lam).comp R.subtype) (by
    intro h hh
    exact (projection_eq_zero R lam h).mpr hh)

@[simp] theorem quotientShift_mk (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    quotientShift R lam (Submodule.Quotient.mk h) = projection R lam (h : P) := rfl

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

def Equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (C : P → B) : Prop :=
  ∀ (u : P) (h : R), C (u + (h : P)) = C u + lam h

theorem difference_shift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) (h : R) :
    C (u + (h : P) + a) - C (u + (h : P)) = C (u + a) - C u := by
  have he : u + (h : P) + a = (u + a) + (h : P) := by
    simp only [add_assoc, add_comm (h : P) a]
  rw [he, hC, hC, add_sub_add_right_eq_sub]

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

theorem difference_fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (a : P) (d b c : B) :
    Nat.card {u : P // C u = b ∧ C (u + a) - C u = d} =
      Nat.card {u : P // C u = c ∧ C (u + a) - C u = d} := by
  apply conditioned_fiber_card R lam hlam C hC
  intro u h
  rw [difference_shift R lam C hC]

def conditionedSigmaEquiv (C : P → B) (D : P → Prop) :
    {u : P // D u} ≃ Σ b : B, {u : P // C u = b ∧ D u} where
  toFun u := ⟨C u.val, ⟨u.val, rfl, u.property⟩⟩
  invFun u := ⟨u.2.val, u.2.property.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨b, u, hu, hD⟩; cases hu; rfl

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

theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]

theorem character_pullback_shift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (g : Space R lam →ₗ[𝕜] 𝕜) (h : R) :
    (g.comp (projection R lam)) (h : P) =
      (g.comp (logicalShift R lam hlam)) (lam h) := by
  simp only [LinearMap.comp_apply, logicalShift_lambda]

theorem detection_iff {I : Type*} (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (family : I → Space R lam →ₗ[𝕜] 𝕜) (a : P) :
    (∃ i, family i (projection R lam a) ≠ 0) ↔
      ∃ i, (family i).comp (projection R lam) a ≠ 0 := Iff.rfl

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

theorem fiber_card (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : Space R lam) :
    Nat.card {u : P // projection R lam u = x} = Nat.card (shiftKernel R lam) := by
  obtain ⟨a, rfl⟩ := projection_surjective R lam x
  exact (Nat.card_congr (Equiv.ofBijective _ (fiberMap_bijective R lam a))).symm

end DFVSGames.Gadget.Quotient

namespace DFVSGames.Gadget.StageQuotient

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

end DFVSGames.Gadget.StageQuotient

namespace DFVSGames.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

def IsFullLift (ι : B →ₗ[K] V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : Prop :=
  ∀ (z : Module.Dual K B) (b : B), ψ z (ι b) = z b

noncomputable def characterDetection (noise : Ω → V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : ℚ := by
  classical
  exact probability (fun ω => ∃ z : Module.Dual K B, ψ z (noise ω) ≠ 0)

theorem exists_leftInverse_of_logical_injective (ι : B →ₗ[K] V)
    (T : V →ₗ[K] E) (hinjective : Function.Injective (T.comp ι)) :
    ∃ l : E →ₗ[K] B, l.comp (T.comp ι) = LinearMap.id :=
  (T.comp ι).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

theorem fullLift_of_leftInverse (ι : B →ₗ[K] V) (T : V →ₗ[K] E)
    (l : E →ₗ[K] B) (hleft : l.comp (T.comp ι) = LinearMap.id) :
    IsFullLift ι (l.comp T).dualMap := by
  intro z b
  change z (l (T (ι b))) = z b
  have hb : l (T (ι b)) = b := LinearMap.congr_fun hleft b
  rw [hb]

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

end DFVSGames.Gadget.DetectionBridge

namespace DFVSGames.Gadget.QuotientDetection

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
theorem target_detection_after_quotient (s : Stage k B) [Fintype s.Noise]
    {E : Type*} [AddCommGroup E] [Module k E] [DecidableEq E]
    (T : StageQuotient.Space s →ₗ[k] E) (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (hinj : Function.Injective (T.comp (StageQuotient.shift s))) :
    q ≤ probability (fun n => T (StageQuotient.noise s n) ≠ 0) := by
  exact target_detection_of_full_lift_bound (StageQuotient.noise s)
    (StageQuotient.shift s) T q (full_detection_after_quotient s q hfull) hinj

end DFVSGames.Gadget.QuotientDetection

end OAI
