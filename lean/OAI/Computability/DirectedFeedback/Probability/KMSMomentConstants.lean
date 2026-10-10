import Mathlib
import OAI.Computability.DirectedFeedback.Games.A5ForwardIndex

namespace OAI

namespace DFVSGames.Appendix.HybridCounting

open Module
open DFVSGames.Integration.BinaryLinear (F2)

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
  have hleft := DFVSGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := Y.range) d hY
  have hright := DFVSGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := F ⧸ Y.ker) d (hq.trans_le hY)
  calc
    _ ≤ Nat.card (Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_le_card_of_injective code hi
    _ = Nat.card (Submodule F2 Y.range) * Nat.card (Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_prod _ _
    _ ≤ 2 ^ (d * d) * 2 ^ (d * d) := Nat.mul_le_mul hleft hright
    _ = _ := by rw [← pow_add]; congr 1; ring

variable [FiniteDimensional F2 E]

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

end DFVSGames.Appendix.HybridCounting

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.DerivativeDegree

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

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
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

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
  split_ifs <;> simp_all [DFVSGames.Fourier.MatrixCharacters.F2]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankComponent_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankComponent i f) := by
  rw [rankComponent_eq_rankProjection]
  exact rankProjection_invariant i f hf

theorem rankComponent_coeff_eq_zero_of_ne (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E)
    (hS : Module.finrank F2 S.range ≠ i) :
    linearCoeff (rankComponent i f) S = 0 := by
  simp only [rankComponent, coeff_component, ite_eq_right hS]

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Appendix
open DFVSGames.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem rankComponent_degree (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DerivativeDegree.DegreeAtMost i (rankComponent i f) := by
  intro S hS
  apply rankComponent_coeff_eq_zero_of_ne i f S
  exact ne_of_gt hS

variable [Finite E] [Finite F]

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
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

theorem fourthMomentConstant_pos (r : ℕ) : 0 < fourthMomentConstant r := by
  unfold fourthMomentConstant
  positivity

theorem fourthMomentConstant_nonneg (r : ℕ) : 0 ≤ fourthMomentConstant r :=
  (fourthMomentConstant_pos r).le

theorem mixedRankConstant_eq (r : ℕ) :
    mixedRankConstant r = (2 : ℝ) ^ (6 * r * r + 2 * r) := by
  unfold mixedRankConstant mixedStepFactor
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem a5_mul_mixedRankConstant (r : ℕ) :
    (2 : ℝ) ^ (103 * r * r) * mixedRankConstant r = fourthMomentConstant r := by
  rw [mixedRankConstant_eq, ← pow_add]
  unfold fourthMomentConstant
  congr 1
  ring

theorem fourthMomentConstant_mono {i r : ℕ} (hi : i ≤ r) :
    fourthMomentConstant i ≤ fourthMomentConstant r := by
  unfold fourthMomentConstant
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 109 hi) hi)
    (Nat.mul_le_mul_left 2 hi)

theorem a5_mixed_bound {i r : ℕ} (hi : i ≤ r) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    (2 : ℝ) ^ (103 * i * i) * (mixedRankConstant i * ε) * η ≤
      fourthMomentConstant r * η * ε := by
  calc
    _ = fourthMomentConstant i * (η * ε) := by
      rw [← a5_mul_mixedRankConstant]
      ring
    _ ≤ fourthMomentConstant r * (η * ε) :=
      mul_le_mul_of_nonneg_right (fourthMomentConstant_mono hi) (mul_nonneg hη hε)
    _ = _ := by ring

end
end DFVSGames.Inverse.KMSMomentConstants

namespace DFVSGames.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

def relativeDensity (S I : Finset Ω) : ℝ :=
  ((S ∩ I).card : ℝ) / I.card

theorem inter_chart_eq (S I C : Finset Ω) (hSC : S ⊆ C) :
    S ∩ (I ∩ C) = S ∩ I := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hS, hI, _⟩
    exact ⟨hS, hI⟩
  · rintro ⟨hS, hI⟩
    exact ⟨hS, hI, hSC hS⟩

theorem chart_inter_nonempty (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) : (I ∩ C).Nonempty := by
  obtain ⟨x, hx⟩ := hSI
  exact ⟨x, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).2, hSC (Finset.mem_inter.mp hx).1⟩⟩

theorem relativeDensity_le_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hIC : (I ∩ C).Nonempty) :
    relativeDensity S I ≤ relativeDensity S (I ∩ C) := by
  unfold relativeDensity
  rw [inter_chart_eq S I C hSC]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hIC)
  · exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

theorem density_bound_passes_to_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) {α : ℝ} (hα : α ≤ relativeDensity S I) :
    (I ∩ C).Nonempty ∧ α ≤ relativeDensity S (I ∩ C) := by
  have hIC := chart_inter_nonempty S I C hSC hSI
  exact ⟨hIC, hα.trans (relativeDensity_le_chart S I C hSC hIC)⟩

end FiniteDensity

abbrev F2 := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → F2

def Vertex (n ell : ℕ) :=
  {L : Submodule F2 (Ambient n) // Module.finrank F2 L = ell}

instance vertexFinite (n ell : ℕ) : Finite (Vertex n ell) := by
  let : Finite (Submodule F2 (Ambient n)) :=
    Finite.of_injective (fun L : Submodule F2 (Ambient n) => (L : Set (Ambient n)))
      SetLike.coe_injective
  exact inferInstanceAs (Finite {L : Submodule F2 (Ambient n) //
    Module.finrank F2 L = ell})

instance vertexFintype (n ell : ℕ) : Fintype (Vertex n ell) := Fintype.ofFinite _

def Adjacent {n ell : ℕ} (L M : Vertex n ell) : Prop :=
  L ≠ M ∧ Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) + 1 = ell

def neighbors {n ell : ℕ} (L : Vertex n ell) : Finset (Vertex n ell) :=
  Finset.univ.filter (Adjacent L)

def retention {n ell : ℕ} (S : Finset (Vertex n ell)) : ℝ :=
  (∑ L ∈ S, relativeDensity S (neighbors L)) / S.card

def interval {n ell : ℕ} (A B : Submodule F2 (Ambient n)) :
    Finset (Vertex n ell) :=
  Finset.univ.filter fun L => A ≤ L.val ∧ L.val ≤ B

def ExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (Vertex n ell), S.Nonempty → ζ ≤ retention S →
            ∃ A B : Submodule F2 (Ambient n),
              A ≤ B ∧ Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r ∧
                (S ∩ interval A B).Nonempty ∧ α ≤ relativeDensity S (interval A B)

end
end DFVSGames.Inverse.KMS

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

theorem liftedIndicator_nonneg {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : 0 ≤ liftedIndicator S X := by
  unfold liftedIndicator
  split <;> norm_num

theorem liftedIndicator_le_one {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : liftedIndicator S X ≤ 1 := by
  unfold liftedIndicator
  split <;> norm_num

theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

theorem inLift_comp_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (g : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) (X : BasisMap n ell) :
    InLift S (X.comp g.toLinearMap) ↔ InLift S X := by
  unfold InLift
  rw [LinearMap.range_comp_of_range_eq_top X g.range]

theorem liftedIndicator_basisInvariant {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    KMSBasisInvariant.IsBasisInvariant (liftedIndicator S) := by
  intro g X
  simp only [liftedIndicator, inLift_comp_iff]

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem nat_card_eq_sum_fibers (f : X → Y) :
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]

theorem nat_card_event_eq_sum_fibers (f : X → Y) (p : Y → Prop) :
    Nat.card {x : X // p (f x)} =
      ∑ y : {y : Y // p y}, Nat.card {x : X // f x = y.val} := by
  let e : (Σ y : {y : Y // p y}, {x : X // f x = y.val}) ≃
      {x : X // p (f x)} :=
    { toFun := fun a => ⟨a.2.val, a.2.property.symm ▸ a.1.property⟩
      invFun := fun a => ⟨⟨f a.val, a.property⟩, ⟨a.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro a; rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]

theorem uniformFiber_card_ratio (f : X → Y) (p : Y → Prop)
    (c : ℕ) (hc : 0 < c)
    (hf : ∀ y, Nat.card {x : X // f x = y} = c) :
    (Nat.card {x : X // p (f x)} : ℝ) / Nat.card X =
      (Nat.card {y : Y // p y} : ℝ) / Nat.card Y := by
  have hX : Nat.card X = Nat.card Y * c := by
    rw [nat_card_eq_sum_fibers f]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  have hE : Nat.card {x : X // p (f x)} = Nat.card {y : Y // p y} * c := by
    rw [nat_card_event_eq_sum_fibers f p]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  rw [hE, hX, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Nat.cast_pos.mpr hc))

theorem subtype_event_ratio_le {Z : Type*} [Fintype Z] (D : Z → Prop)
    (p : {z : Z // D z} → Prop) :
    (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card Z ≤
      (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card {z : Z // D z} := by
  by_cases hD : Nat.card {z : Z // D z} = 0
  · have hE : Nat.card {z : {z : Z // D z} // p z} = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hD]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hE]
    simp
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
    · exact Nat.cast_le.mpr
        (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical
open DFVSGames.Inverse.KMS

theorem exists_restricted_completion {n q t : ℕ}
    (Q : Fin q → Ambient n) (W L : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (hQL : Submodule.span F2 (Set.range Q) ≤ L)
    (hLW : L ≤ Submodule.span F2 (Set.range Q) ⊔ W)
    (hL : Module.finrank F2 L = q + t) :
    ∃ z : Fin t → W,
      LinearIndependent F2 (Sum.elim Q (fun i => (z i : Ambient n))) ∧
        Submodule.span F2
          (Set.range (Sum.elim Q (fun i => (z i : Ambient n)))) = L := by
  classical
  let T : Set (Ambient n) := Set.range Q ∪ (W ⊓ L : Submodule F2 (Ambient n))
  have hQT : Set.range Q ⊆ T := Set.subset_union_left
  have hTspan : Submodule.span F2 T = L := by
    change Submodule.span F2
      (Set.range Q ∪ ((W ⊓ L : Submodule F2 (Ambient n)) : Set (Ambient n))) = L
    rw [Submodule.span_union, Submodule.span_eq,
      ← sup_inf_assoc_of_le W hQL, inf_eq_right.mpr hLW]
  obtain ⟨B, hBT, hQB, hTB, hB⟩ :=
    exists_linearIndepOn_id_extension hQ.linearIndepOn_id hQT
  have hBspan : Submodule.span F2 B = L := by
    rw [← hTspan]
    exact le_antisymm (Submodule.span_mono hBT) (Submodule.span_le.mpr hTB)
  let D : Set (Ambient n) := B \ Set.range Q
  let f : Fin q ⊕ D → Ambient n := Sum.elim Q Subtype.val
  have hf_inj : Function.Injective f := by
    apply Sum.elim_injective.mpr
    refine ⟨hQ.injective, Subtype.val_injective, ?_⟩
    intro i d hid
    exact d.property.2 ⟨i, hid⟩
  have hf_range : Set.range f = B := by
    ext x
    constructor
    · rintro ⟨i | d, rfl⟩
      · exact hQB (Set.mem_range_self i)
      · exact d.property.1
    · intro hx
      by_cases hxQ : x ∈ Set.range Q
      · obtain ⟨i, rfl⟩ := hxQ
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx, hxQ⟩, rfl⟩
  have hf : LinearIndependent F2 f := by
    apply (linearIndepOn_id_range_iff hf_inj).mp
    rw [hf_range]
    exact hB
  have hcard := finrank_span_eq_card hf
  rw [hf_range, hBspan, hL] at hcard
  have hDcard : Fintype.card D = t := by
    apply Nat.add_left_cancel (n := q)
    simpa using hcard.symm
  let e : Fin t ≃ D := (Fintype.equivFinOfCardEq hDcard).symm
  let z : Fin t → W := fun i =>
    ⟨(e i).val, ((hBT (e i).property.1).resolve_left (e i).property.2).1⟩
  let g : (Fin q ⊕ Fin t) ≃ (Fin q ⊕ D) := Equiv.sumCongr (Equiv.refl _) e
  have hz : Sum.elim Q (fun i => (z i : Ambient n)) = f ∘ g := by
    funext i
    cases i <;> rfl
  refine ⟨z, ?_, ?_⟩
  · rw [hz]
    exact hf.comp g g.injective
  · rw [hz, g.surjective.range_comp, hf_range, hBspan]

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

theorem restrictedCompletionCard_eq
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    Nat.card (RestrictedCompletion (t := t) Q W L) =
      Nat.card (RestrictedCompletion (t := t) Q W M) :=
  Nat.card_congr (restrictedCompletionEquiv x y)

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

end OAI
