import OAI.Analysis.KadisonKastler.SignedFunctionalCompression
import OAI.Analysis.KadisonKastler.ExtremeHermitianSplit
import OAI.Analysis.KadisonKastler.SpatialCoefficientClosure

namespace OAI

/-! # An extreme signed separator has no nontrivial commuting source projection -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commuting_operator_zero_of_cyclic (π : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (hcyc : DenseRange (fun b => π b ξ)) (p : H →L[ℂ] H)
    (hp : ∀ b, Commute p (π b)) (hpξ : p ξ = 0) : p = 0 := by
  have he : (fun x : H => p x) = fun _ => 0 := by
    apply hcyc.equalizer p.continuous continuous_const
    funext b
    change p (π b ξ) = 0
    have h := congrArg (fun T : H →L[ℂ] H => T ξ) (hp b).eq
    change p (π b ξ) = π b (p ξ) at h
    simpa only [hpξ, map_zero] using h
  exact ContinuousLinearMap.ext (fun x => congrFun he x)

theorem signedVectorFunctional_projection_left
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ b, Commute p (π b)) (ξ : H) (b : B) :
    signedVectorFunctional π S (p ξ) b = inner ℂ (S (p ξ)) (π b ξ) := by
  rw [signedVectorFunctional_projection π S p hp hSp hpp]
  have hSpξ : S (p ξ) = p (S ξ) :=
    (congrArg (fun T : H →L[ℂ] H => T ξ) hSp.eq).symm
  have hpb : p (π b ξ) = π b (p ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (hpp b).eq
  rw [hSpξ]
  have hi : inner ℂ (p (S ξ)) (π b ξ) = inner ℂ (S ξ) (p (π b ξ)) := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
      p.adjoint_inner_left (π b ξ) (S ξ)
  rw [hi, hpb]

theorem extreme_signed_projection_trivial
    (φ : A →⋆ₐ[ℂ] B) (F : WeakDual ℂ B)
    (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyc : DenseRange (fun b => π b ξ))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1)
    (hSπ : ∀ b, Commute S (π b)) (hrep : F.toStrongDual = signedVectorFunctional π S ξ)
    (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hpπ : ∀ b, Commute p (π b)) (hpS : Commute p S)
    (hpN : p ∈ generatedVonNeumannAlgebra (π.comp φ).range) : p = 0 ∨ p = 1 := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hsource : ∀ a : (π.comp φ).range, inner ℂ (S ξ) (a.val ξ) = 0 := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    have hz := (mem_extremePoints.mp hF).1.2.2 b
    change F.toStrongDual (φ b) = 0 at hz
    rw [hrep] at hz
    change inner ℂ (S ξ) (π (φ b) ξ) = 0 at hz
    change π (φ b) = a.val at hb
    rwa [← hb]
  have hann (q : H →L[ℂ] H) (hq : IsStarProjection q)
      (hqπ : ∀ b, Commute q (π b)) (hqS : Commute q S) (hqN : q ∈ N) :
      ∀ a, signedVectorFunctional π S (q ξ) (φ a) = 0 := by
    intro a
    rw [signedVectorFunctional_projection π S q hq hqS hqπ]
    exact coefficient_zero_generated (π.comp φ).range ξ (S ξ) hsource (π (φ a) * q)
      (N.mul_mem (subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨a, rfl⟩) hqN)
  have hqπ (b : B) : Commute (1 - p) (π b) := by
    change (1 - p) * π b = π b * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, (hpπ b).eq]
  have hqS : Commute (1 - p) S := by
    change (1 - p) * S = S * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, hpS.eq]
  have hqN : 1 - p ∈ N := N.sub_mem N.one_mem hpN
  let t : ℝ := ‖p ξ‖ ^ 2
  let s : ℝ := ‖(1 - p) ξ‖ ^ 2
  have hts : t + s = 1 := by
    simpa only [t, s, hξ, one_pow] using norm_sq_projection_add_complement p hp ξ
  by_cases ht0 : t = 0
  · left
    apply commuting_operator_zero_of_cyclic π ξ hcyc p hpπ
    apply norm_eq_zero.mp
    dsimp [t] at ht0
    nlinarith [norm_nonneg (p ξ)]
  by_cases hs0 : s = 0
  · right
    have he : 1 - p = 0 := by
      apply commuting_operator_zero_of_cyclic π ξ hcyc (1 - p) hqπ
      apply norm_eq_zero.mp
      dsimp [s] at hs0
      nlinarith [norm_nonneg ((1 - p) ξ)]
    exact (sub_eq_zero.mp he).symm
  exfalso
  have ht : 0 < t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm ht0)
  have hs : 0 < s := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hs0)
  let G := signedVectorFunctional π S (p ξ)
  let K := signedVectorFunctional π S ((1 - p) ξ)
  have heq : G + K = F.toStrongDual :=
    (signedVectorFunctional_split_projection π S p hp hpS hpπ ξ).symm.trans hrep.symm
  have hG : G = t • F.toStrongDual :=
    extreme_hermitian_split φ F hF G K t s ht hs hts
      (signedVectorFunctional_norm_le π S hS hSS _)
      (signedVectorFunctional_norm_le π S hS hSS _)
      (signedVectorFunctional_star π S hS hSπ _)
      (signedVectorFunctional_star π S hS hSπ _)
      (hann p hp hpπ hpS hpN) (hann (1 - p) hp.one_sub hqπ hqS hqN) heq
  have hinner (b : B) : inner ℂ (S (p ξ)) (π b ξ) = inner ℂ (t • S ξ) (π b ξ) := by
    rw [← signedVectorFunctional_projection_left π S p hp hpS hpπ ξ b]
    have he := congrArg (fun L : B →L[ℂ] ℂ => L b) hG
    rw [hrep] at he
    simpa only [G, smul_apply, signedVectorFunctional_apply, inner_smul_left_eq_smul] using he
  have hvec : S (p ξ) = t • S ξ := by
    apply ext_inner_right ℂ
    have he := hcyc.equalizer (continuous_const.inner continuous_id)
      (continuous_const.inner continuous_id) (funext hinner)
    exact fun y => congrFun he y
  have hSSv (v : H) : S (S v) = v := congrArg (fun T : H →L[ℂ] H => T v) hSS
  have hpξ : p ξ = t • ξ := by
    have he := congrArg S hvec
    have hlin : S (t • S ξ) = t • S (S ξ) := S.map_smul_of_tower t (S ξ)
    simpa only [hlin, hSSv] using he
  have hpn : ‖p ξ‖ = t := by
    rw [hpξ, norm_smul, Real.norm_of_nonneg ht.le, hξ, mul_one]
  have htt : t = t ^ 2 := by
    change ‖p ξ‖ ^ 2 = t ^ 2
    rw [hpn]
  nlinarith

end

end KadisonKastler

end OAI
