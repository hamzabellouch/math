import Mathlib
import OAI.Computability.MaxCut.Games.KMSBasisInvariant
import OAI.Computability.MaxCut.Games.A5ReverseIndex

namespace OAI

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

noncomputable section
namespace MaxCutGames.Appendix.A5Induction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.DerivativeDegree
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

/-- The strong-induction motive quantifies over the actual changing domains.
Quotients and subspaces preserve the fixed universe levels. -/
def BoundAtDegree (d : ℕ) : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    [Finite E] [Finite F]
    [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
    (f : (E →ₗ[F2] F) → ℝ),
    DegreeAtMost d f →
      (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f

theorem damping_le (d k : ℕ) :
    (1 / 2 : ℝ) ^ (31 * d * (k + 1) + 4 * d * k) ≤
      (1 / 2 : ℝ) ^ (31 * d) * (1 / 2 : ℝ) ^ (8 * d * k) := by
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
      nlinarith
  have he : 31 * d * (k + 1) + 4 * d * k =
      (31 * d + 8 * d * k) + 27 * d * k := by ring
  rw [he, pow_add, pow_add]
  have hh := mul_le_mul_of_nonneg_left (hpow (27 * d * k))
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (31 * d))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (8 * d * k)))
  simpa only [mul_one] using hh

theorem coefficient_absorption (d : ℕ) (hd : 1 ≤ d) :
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
      (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) ≤
      (2 : ℝ) ^ (100 * d * d) := by
  have hfirst : (2 : ℝ) ^ (100 * d * d) *
      ((2 : ℝ) ^ (94 * d * d))⁻¹ = (2 : ℝ) ^ (6 * d * d) := by
    have he : 100 * d * d = 6 * d * d + 94 * d * d := by ring
    rw [he, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      mul_one]
  have he : 31 * d = (31 * d - 1) + 1 := by omega
  have hsecond : ((2 : ℝ) ^ (31 * d - 1))⁻¹ =
      2 * (1 / 2 : ℝ) ^ (31 * d) := by
    calc
      ((2 : ℝ) ^ (31 * d - 1))⁻¹ = (1 / 2 : ℝ) ^ (31 * d - 1) := by
        rw [one_div, inv_pow]
      _ = 2 * ((1 / 2 : ℝ) ^ (31 * d - 1) * (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← pow_succ, ← he]
  have hscaled := mul_le_mul_of_nonneg_right (A5Scalar.absorption hd)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  calc
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) =
        162 * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
          ((2 : ℝ) ^ (31 * d - 1))⁻¹) * (2 : ℝ) ^ (100 * d * d) := by
      symm
      calc
        _ = 162 * ((2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (94 * d * d))⁻¹ +
            (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (31 * d - 1))⁻¹) := by ring
        _ = _ := by rw [hfirst, hsecond]
    _ ≤ _ := by simpa only [one_mul] using hscaled

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual weighted map-derivative sum left by the finite reindexing. -/
def dampedMapMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ X : F →ₗ[F2] E,
    (1 / 2 : ℝ) ^ (31 * d * (frequencyRank X + 1) + 4 * d * frequencyRank X) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2

theorem dampedMapMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedMapMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * (𝔼 M, f M ^ 2) ^ 2 := by
  have hterms : dampedMapMoment d f ≤ (1 / 2 : ℝ) ^ (31 * d) *
      ∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2) ^ 2 := by
    unfold dampedMapMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro X _
    have hh := mul_le_mul_of_nonneg_right (damping_le d (frequencyRank X))
      (sq_nonneg (𝔼 N, mapDerivative X f N ^ 2))
    simpa only [mul_assoc] using hh
  have hbase := weighted_fourth_derivative_energy f d (fun Y hY => hf Y hY)
  have hbase' :
      (∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2)^2) ≤ 2 * (𝔼 M, f M ^ 2)^2 := by
    simpa only [one_div, frequencyRank] using hbase
  calc
    dampedMapMoment d f ≤ _ := hterms
    _ ≤ (1 / 2 : ℝ) ^ (31 * d) * (2 * (𝔼 M, f M ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase'
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    _ = _ := by ring

def dampedHybridMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)

theorem dampedHybridMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedHybridMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f := by
  unfold dampedHybridMoment hybridMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)) ≤
        𝔼 T, (2 * (1 / 2 : ℝ) ^ (31 * d)) *
          (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2 := by
      apply Finset.expect_le_expect
      intro T _
      exact dampedMapMoment_le d _
        ((degree_hybridDerivative s.val.1 s.val.2 T f hf).mono (Nat.sub_le _ _))
    _ = _ := by rw [← Finset.mul_expect]

omit [Finite E] [Finite F] in
theorem hybridProjector_zero_pair (f : (E →ₗ[F2] F) → ℝ) :
    hybridProjector (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f = f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp [hybridProjector, linearCoeff_spectralProjector, LinearIdentities.Hybrid]

theorem energy_sq_le_hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, f M ^ 2) ^ 2 ≤ hybridMomentSum d f := by
  have hzero : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    have he : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) + Module.finrank F2 F =
        Module.finrank F2 F := by simpa using hq
    omega
  let s0 : HybridIndex (E := E) (F := F) d := ⟨(⊥, ⊤), by
    change Module.finrank F2 (⊥ : Submodule F2 E) +
      Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) ≤ d
    rw [hzero]
    simp⟩
  have havg := hybridDerivative_energy_average
    (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f
  rw [hybridProjector_zero_pair] at havg
  have hcs : (𝔼 T, 𝔼 N,
      hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 ≤
      𝔼 T, (𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 := by
    simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun T => 𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2)
      (fun _ => (1 : ℝ))
  rw [havg] at hcs
  apply hcs.trans
  change (𝔼 T, (𝔼 N, hybridDerivative s0.val.1 s0.val.2 T f N ^ 2) ^ 2) ≤ _
  unfold hybridMomentSum
  let H : HybridIndex (E := E) (F := F) d → ℝ :=
    fun s => 𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)^2
  change H s0 ≤ ∑ s, H s
  exact Finset.single_le_sum (f := H) (s := Finset.univ)
    (fun s _ => Finset.expect_nonneg (fun T _ =>
      sq_nonneg (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)))
    (Finset.mem_univ s0)

theorem degree_zero_bound (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost 0 f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * 0 * 0) * hybridMomentSum 0 f := by
  rw [DegreeZero.fourth_moment_eq_energy_sq f (fun Y hY => hf Y hY)]
  simpa using energy_sq_le_hybridMomentSum 0 f

/-- Close the actual recurrence once its finite index expansion is supplied.
This lemma states that recurrence explicitly; it is not the public A.5 theorem. -/
theorem recurrence_closure (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (hrec : (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d * d) * (𝔼 M, f M ^ 2)^2 +
        (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f := by
  have hS : 0 ≤ hybridMomentSum d f :=
    Finset.sum_nonneg (fun s _ => Finset.expect_nonneg (fun T _ => sq_nonneg _))
  have herror := mul_le_mul_of_nonneg_left (energy_sq_le_hybridMomentSum d f)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d * d))
  have hdamp := mul_le_mul_of_nonneg_left (dampedHybridMoment_le d f hf)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  have hrec' : (𝔼 M, f M ^ 4) / 162 ≤
      ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f := by
    calc
      _ ≤ _ := hrec
      _ ≤ (2 : ℝ) ^ (6 * d * d) * hybridMomentSum d f +
          (2 : ℝ) ^ (100 * d * d) *
            ((2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f) :=
        add_le_add herror hdamp
      _ = _ := by ring
  calc
    (𝔼 M, f M ^ 4) = 162 * ((𝔼 M, f M ^ 4) / 162) := by ring
    _ ≤ 162 * (((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f) := mul_le_mul_of_nonneg_left hrec' (by norm_num)
    _ = (162 * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d)))) *
          hybridMomentSum d f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_absorption d hd) hS

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Dimension bounds for the outer subspaces used by the actual A.5 operator
identity, obtained from the order of an actual derivative-space index. -/
theorem lifted_outer_dimensions (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d) :
    Module.finrank F2 (C.comap X.range.mkQ) ≤ d ∧
      Module.finrank F2 (F ⧸ D.map X.ker.subtype) ≤ d := by
  have hC := HybridComposition.finrank_comap_mkQ X.range C
  have hD := Submodule.finrank_map_subtype_eq X.ker D
  have hKD := D.finrank_quotient_add_finrank
  have hFD := (D.map X.ker.subtype).finrank_quotient_add_finrank
  have hX := X.finrank_range_add_finrank_ker
  change Module.finrank F2 X.range +
    (Module.finrank F2 C + Module.finrank F2 (X.ker ⧸ D)) ≤ d at hcut
  constructor <;> omega

/-- The native A.5 energy inequality with its actually proved numerical
complement factor. The only cutoff is the rank plus the outer derivative order. -/
theorem a5_energySquare_le_power (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    [Fintype (OperatorPartitions.A5GeometricIndex X
      (C.comap X.range.mkQ) (D.map X.ker.subtype))]
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (S : Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) ^ 2 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
        ∑ p : OperatorPartitions.A5GeometricIndex X
          (C.comap X.range.mkQ) (D.map X.ker.subtype),
          (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
            (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
  have hI : X.range ≤ C.comap X.range.mkQ := by
    intro x hx
    change X.range.mkQ x ∈ C
    have hz : X.range.mkQ x = 0 := by
      change x ∈ LinearMap.ker X.range.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map X.ker.subtype ≤ X.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hCmap : (C.comap X.range.mkQ).map X.range.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := X.range.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hDcomap : (D.map X.ker.subtype).comap X.ker.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hdims := lifted_outer_dimensions X C D d hcut
  have hcount := A5IndexCount.card_geometricIndex_cube_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI d hdims.1 hdims.2
  rw [Nat.card_eq_fintype_card] at hcount
  have hcountR :
      (Fintype.card (OperatorPartitions.A5GeometricIndex X
        (C.comap X.range.mkQ) (D.map X.ker.subtype)) : ℝ)^3 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) := by exact_mod_cast hcount
  have hn := OperatorNorm.a5_energySquare_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI hB f S
  have hfinal := hn.trans
    (mul_le_mul_of_nonneg_right hcountR
      (Finset.sum_nonneg (fun p _ => sq_nonneg _)))
  let energy (C' : Submodule F2 (E ⧸ X.range)) (D' : Submodule F2 X.ker) : ℝ :=
    (𝔼 N, hybridDerivative C' D' S (mapDerivative X f) N ^ 2)^2
  have he : energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) = energy C D :=
    congrArg₂ energy hCmap hDcomap
  change energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) ≤ _ at hfinal
  rw [he] at hfinal
  exact hfinal

/-- Actual A.5 descendants before recombining the first hybrid restriction. -/
def postA5Sum (X : F →ₗ[F2] E) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : A5Passage.Passage X e, 𝔼 S : Parameter X.range X.ker,
    (𝔼 N, mapDerivative (LinearIdentities.compress X q.2.val.1 q.2.val.2)
      (hybridDerivative q.2.val.1 q.2.val.2 (embed X.range X.ker S) f) N ^ 2)^2

theorem mapDerivative_hybridMomentSum_le (d e : ℕ) (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (hcut : Module.finrank F2 X.range + e ≤ d) :
    hybridMomentSum e (mapDerivative X f) ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) * postA5Sum X e f := by
  unfold hybridMomentSum postA5Sum
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  let : Fintype (OperatorPartitions.A5GeometricIndex X
      (s.val.1.comap X.range.mkQ) (s.val.2.map X.ker.subtype)) :=
    A5Passage.pairFintype X s
  have hs : Module.finrank F2 X.range + order s.val.1 s.val.2 ≤ d := by
    have ho := s.property
    omega
  calc
    (𝔼 S, (𝔼 N, hybridDerivative s.val.1 s.val.2 S (mapDerivative X f) N ^ 2)^2) ≤
        𝔼 S, (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
          ∑ p : A5Passage.Pair X s,
            (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
              (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
      apply Finset.expect_le_expect
      intro S _
      exact a5_energySquare_le_power X s.val.1 s.val.2 d hs f S
    _ = _ := by rw [← Finset.mul_expect, Finset.expect_sum_comm]

/-- Recombination uses the natural domain and codomain isomorphisms. The
intermediate shifts need only be the actual embedded derivative parameters. -/
theorem postA5Sum_hybrid_average (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, postA5Sum X e (hybridDerivative A B T f)) =
      A5Passage.descendantSum A B X e f := by
  unfold postA5Sum A5Passage.descendantSum
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [NaturalTransport.nested_mapDerivative_energy
    A B q.2.val.1 q.2.val.2 f]
  exact Restriction.real_translation_average
    (fun S : Parameter X.range X.ker => embed A B (embed X.range X.ker S))
    (fun U => (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2)^2)

/-- The actual A.15 induction step for one positive-order derivative triple.
The induction hypothesis is used only at the strictly smaller degree `d-t`,
on its genuine quotient-domain and kernel-codomain spaces. -/
theorem a15_of_strong_induction (d t : ℕ) (A : Submodule F2 E)
    (B : Submodule F2 F) (X : B →ₗ[F2] (E ⧸ A))
    (ht : t = order A B + Module.finrank F2 X.range)
    (htpos : 0 < t) (htd : t ≤ d)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
      (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
        A5Passage.descendantSum A B X (d - t) f := by
  have hlt : d - t < d := by omega
  have hcut : Module.finrank F2 X.range + (d - t) ≤ d := by omega
  have hpoint (T : E →ₗ[F2] F) :
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) := by
    have hdeg : DegreeAtMost (d - t) (mapDerivative X (hybridDerivative A B T f)) := by
      simpa only [ht, frequencyRank] using degree_map_hybridDerivative A B X T f hf
    have hIH := ih (d - t) hlt (mapDerivative X (hybridDerivative A B T f)) hdeg
    have hnorm := mapDerivative_hybridMomentSum_le d (d - t) X
      (hybridDerivative A B T f) hcut
    calc
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
          (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
            hybridMomentSum (d - t) (mapDerivative X (hybridDerivative A B T f)) := hIH
      _ ≤ (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
          ((2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
            postA5Sum X (d - t) (hybridDerivative A B T f)) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = _ := by rw [pow_add]; ring
  calc
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        𝔼 T, (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) :=
      Finset.expect_le_expect (fun T _ => hpoint T)
    _ = _ := by rw [← Finset.mul_expect, postA5Sum_hybrid_average]

/-- Apply the genuine lower-degree induction step to every term of the
checked A.13 sum, preserving its original positive-order cutoff. -/
theorem boundedTripleSum_le_descendants (d : ℕ)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    A13Reduction.boundedPositiveTripleSum d f ≤
      ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
        (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
          24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
          A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
            (d - A13Index.size p.val) f := by
  unfold A13Reduction.boundedPositiveTripleSum
  apply Finset.sum_le_sum
  intro p _
  have h15 := a15_of_strong_induction d (A13Index.size p.val)
    p.val.1 p.val.2.1 p.val.2.2 rfl p.property.1 p.property.2 ih f hf
  have hw := mul_le_mul_of_nonneg_left h15
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (24 * d * A13Index.size p.val))
  have he : 24 * d * A13Index.size p.val +
      (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
        6 * d * Module.finrank F2 p.val.2.2.range) =
      100 * (d - A13Index.size p.val)^2 + 24 * d * A13Index.size p.val +
        6 * d * Module.finrank F2 p.val.2.2.range := by ring
  calc
    A13Reduction.tripleTerm d p.val f ≤
        (2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          ((2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f) := hw
    _ = ((2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          (2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range)) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f := by ring
    _ = _ := by rw [← pow_add, he]

/-- Proposition A.5 on every finite-dimensional binary linear-map space,
proved by strong induction with all changing domains in the motive. -/
theorem boundAtDegree (d : ℕ) : BoundAtDegree.{u, v} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E F instE instME instF instMF instDE instDF instFiniteE instFiniteF
      instHom instDual f hf
    by_cases hz : d = 0
    · subst d
      exact degree_zero_bound f hf
    · have hd : 1 ≤ d := by omega
      have hreverse :
          (∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
            (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
              24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
              A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
                (d - A13Index.size p.val) f) ≤
            (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f := by
        simpa only [dampedHybridMoment, dampedMapMoment, frequencyRank, one_div] using
          A5ReverseSum.weighted_descendantSum_le d hd f
      have hbounded := (boundedTripleSum_le_descendants d ih f hf).trans hreverse
      have hA13 := A13Reduction.degree_reduction_truncated f d hf
      apply recurrence_closure d hd f hf
      simpa only [pow_two, Nat.mul_assoc] using
        hA13.trans (add_le_add le_rfl hbounded)

theorem derivative_inequality (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d f := by
  simpa only [pow_two, Nat.mul_assoc] using boundAtDegree.{u, v} d f hf

end MaxCutGames.Appendix.A5Induction
end

/-! Frequency-conditioned counts of actual Hybrid pairs and derivative indices. -/
namespace MaxCutGames.Appendix.HybridCounting

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

private theorem comap_subtype_injective_inline_HybridCounting {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (I A B : Submodule K V) (hA : A ≤ I) (hB : B ≤ I)
    (h : A.comap I.subtype = B.comap I.subtype) : A = B := by
  apply le_antisymm
  · intro x hx
    have hv : (⟨x, hA hx⟩ : I) ∈ A.comap I.subtype := hx
    rw [h] at hv
    exact hv
  · intro x hx
    have hv : (⟨x, hB hx⟩ : I) ∈ B.comap I.subtype := hx
    rw [← h] at hv
    exact hv

private theorem map_quotient_injective_inline_HybridCounting {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (N A B : Submodule K V) (hA : N ≤ A) (hB : N ≤ B)
    (h : A.map N.mkQ = B.map N.mkQ) : A = B := by
  have aux (P Q : Submodule K V) (hQ : N ≤ Q)
      (he : P.map N.mkQ = Q.map N.mkQ) : P ≤ Q := by
    intro x hx
    have hm : N.mkQ x ∈ P.map N.mkQ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [he] at hm
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hm
    have hk : x - y ∈ N := by
      have hzero : x - y ∈ LinearMap.ker N.mkQ := by
        change N.mkQ (x - y) = 0
        rw [map_sub, heq, sub_self]
      simpa only [Submodule.ker_mkQ] using hzero
    have hz := Q.add_mem (hQ hk) hy
    simpa only [sub_add_cancel] using hz
  exact le_antisymm (aux A B hB h) (aux B A hA h.symm)

private theorem finite_submodules_inline_HybridCounting (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Finite (Submodule F2 V) := by
  let : Finite V := Finite.of_injective (Module.finBasis F2 V).equivFun
    (Module.finBasis F2 V).equivFun.injective
  exact Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]
  [Module F2 E] [Module F2 F] [FiniteDimensional F2 F]

/-- All actual Hybrid pairs for this frequency, with no ambient-dimension factor. -/
theorem card_hybrid_pairs_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {p : Submodule F2 E × Submodule F2 F //
      LinearIdentities.Hybrid Y p.1 p.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let P := {p : Submodule F2 E × Submodule F2 F //
    LinearIdentities.Hybrid Y p.1 p.2}
  let : Finite (Submodule F2 Y.range) := finite_submodules_inline_HybridCounting _
  let : Finite (Submodule F2 (F ⧸ Y.ker)) := finite_submodules_inline_HybridCounting _
  have hk (p : P) : Y.ker ≤ p.1.2 := by
    intro x hx
    apply p.2.2
    change Y x ∈ p.1.1
    rw [show Y x = 0 from hx]
    exact Submodule.zero_mem _
  let code (p : P) : Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker) :=
    ((p.1.1).comap Y.range.subtype, (p.1.2).map Y.ker.mkQ)
  have hi : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact comap_subtype_injective_inline_HybridCounting Y.range p.1.1 q.1.1 p.2.1 q.2.1
        (congrArg Prod.fst h)
    · exact map_quotient_injective_inline_HybridCounting Y.ker p.1.2 q.1.2 (hk p) (hk q)
        (congrArg Prod.snd h)
  have hq : finrank F2 (F ⧸ Y.ker) = finrank F2 Y.range := by
    have hquot := Y.ker.finrank_quotient_add_finrank
    have hrank := Y.finrank_range_add_finrank_ker
    omega
  have hleft := MaxCutGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := Y.range) d hY
  have hright := MaxCutGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := F ⧸ Y.ker) d (hq.trans_le hY)
  calc
    _ ≤ Nat.card (Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_le_card_of_injective code hi
    _ = Nat.card (Submodule F2 Y.range) * Nat.card (Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_prod _ _
    _ ≤ 2 ^ (d * d) * 2 ^ (d * d) := Nat.mul_le_mul hleft hright
    _ = _ := by rw [← pow_add]; congr 1; ring

variable [FiniteDimensional F2 E]

/-- The actual order-bounded index subtype injects into the conditioned pairs. -/
theorem card_hybridIndex_le_two (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let : Finite (Submodule F2 E) := finite_submodules_inline_HybridCounting _
  let : Finite (Submodule F2 F) := finite_submodules_inline_HybridCounting _
  let code (s : {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2}) :
      {p : Submodule F2 E × Submodule F2 F // LinearIdentities.Hybrid Y p.1 p.2} :=
    ⟨s.1.1, s.2⟩
  have hi : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    change (code s).1 = (code t).1
    exact congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective code hi).trans (card_hybrid_pairs_le Y d hY)

theorem card_hybridIndex_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (3 * d * d) := by
  apply (card_hybridIndex_le_two Y d hY).trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (d * d) (by decide : 2 ≤ 3)

end MaxCutGames.Appendix.HybridCounting

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.DerivativeDegree

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual selector multiplicity on frequencies of rank at most `d`.
This uses only the proved finite subspace count and Parseval. -/
theorem selector_energy_le (d : ℕ) (g : (E →ₗ[F2] F) → ℝ)
    (hg : DegreeAtMost d g) :
    hybridSelectorEnergy d g ≤ (2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2) := by
  unfold hybridSelectorEnergy hybridProjector
  apply selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hg Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : selectorMultiplicity
      (fun s : HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [selectorMultiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

/-- Generic closure of the fourth-moment estimate from a uniform bound on
the actual hybrid derivatives. Its eventual KMS application must prove `hH`
from the basis-invariant function and its local densities. -/
theorem fourth_moment_le_of_uniform_hybrid_energy
    (d : ℕ) (g : (E →ₗ[F2] F) → ℝ) (hg : DegreeAtMost d g)
    (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ d → (𝔼 N, hybridDerivative A B T g N ^ 2) ≤ H) :
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (103 * d * d) * H * (𝔼 X, g X ^ 2) := by
  have hp : (2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (103 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d g :=
      A5Induction.derivative_inequality d g hg
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) * (H * hybridSelectorEnergy d g) :=
      mul_le_mul_of_nonneg_left (hybridMomentSum_le_of_uniform_energy d g H hH)
        (by positivity)
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) *
        (H * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (selector_energy_le d g hg) hH0) (by positivity)
    _ = ((2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d)) *
        H * (𝔼 X, g X ^ 2) := by ring
    _ = _ := by rw [hp]

end
end MaxCutGames.Inverse.KMSFourthMoment

/-! The analytic synthesis and the direct basis-invariant projection are the
same actual function. This identity fixes the interface for both moment and
spectral estimates. -/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankComponent_eq_rankProjection (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    rankComponent i f = rankProjection i f := by
  funext X
  simp only [rankComponent, component, synthesis, rankProjection, frequencyRank,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp_all [MaxCutGames.Fourier.MatrixCharacters.F2]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankComponent_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankComponent i f) := by
  rw [rankComponent_eq_rankProjection]
  exact rankProjection_invariant i f hf

/-- The degree bound follows from the literal coefficient filter. -/
theorem rankComponent_coeff_eq_zero_of_ne (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E)
    (hS : Module.finrank F2 S.range ≠ i) :
    linearCoeff (rankComponent i f) S = 0 := by
  simp only [rankComponent, coeff_component, ite_eq_right hS]

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The exact rank component meets the generic derivative inequality's degree
contract by its literal Fourier coefficient filter. This specializes the
checked aggregation to the same actual component used by the KMS spectral
argument; the separate basis-specific proof supplies its hybrid energy.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Appendix
open MaxCutGames.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual finite Fourier support of the component, with no rank-level
inequality invoked. -/
theorem rankComponent_degree (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DerivativeDegree.DegreeAtMost i (rankComponent i f) := by
  intro S hS
  apply rankComponent_coeff_eq_zero_of_ne i f S
  exact ne_of_gt hS

variable [Finite E] [Finite F]

/-- Generic fourth-moment closure for the literal KMS rank component. -/
theorem rankComponent_fourth_moment_le_of_hybrid (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ i →
      (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
    (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2) :=
  fourth_moment_le_of_uniform_hybrid_energy i (rankComponent i f)
    (rankComponent_degree i f) H hH0 hH

end
end MaxCutGames.Inverse.KMSFourthMoment

end OAI
