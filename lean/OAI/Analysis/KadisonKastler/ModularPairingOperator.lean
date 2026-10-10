import OAI.Analysis.KadisonKastler.ModularPairingProducts
import OAI.Analysis.KadisonKastler.TomitaMiddleRange
import OAI.Analysis.KadisonKastler.TomitaMiddlePairing

namespace OAI

/-! # The bounded operator equation for modular averaging

This is the application-sized form of Rieffel--Van Daele, Lemma 4.5.
All operators and algebra representatives are constructed in the original
representation. Our graph resolvent is one half of their operator R.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modular_pairing_operator (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M) (hx : IsSelfAdjoint x)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re) :
    (2 : ℂ) • (tomitaMiddleOperator (M := M) J Ω *
      conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b *
      tomitaMiddleOperator (M := M) J Ω) =
    star z • ((1 - graphResolvent M J Ω 1) * x.val * graphResolvent M J Ω 1) +
      z • (graphResolvent M J Ω 1 * x.val * (1 - graphResolvent M J Ω 1)) := by
  let R := graphResolvent M J Ω 1
  let Q : H →L[ℂ] H := 1 - R
  let T := tomitaMiddleOperator (M := M) J Ω
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hR : R.adjoint = R := (graphResolvent_positive J Ω 1).isSelfAdjoint.star_eq
  have hQ : Q.adjoint = Q := (IsSelfAdjoint.one _ |>.sub
    (graphResolvent_positive J Ω 1).isSelfAdjoint).star_eq
  have hx' : x.val.adjoint = x.val := congrArg Subtype.val hx.star_eq
  have hcore (b₁ b₂ : Algebra M.commutant) :
      inner ℂ (((2 : ℂ) • (T * conjugationOperator C b * T)) (b₂.val Ω)) (b₁.val Ω) =
      inner ℂ ((star z • (Q * x.val * R) + z • (R * x.val * Q)) (b₂.val Ω))
        (b₁.val Ω) := by
    obtain ⟨y, hy, hys⟩ := tomitaMiddle_commutant_representative J Ω hsep hcyc b₁
    obtain ⟨w, hw, hws⟩ := tomitaMiddle_commutant_representative J Ω hsep hcyc b₂
    have hys' : star y.val Ω = R (b₁.val Ω) := by
      rw [hys, show star b₁.val = (star b₁).val from rfl,
        tomitaMiddleOperator_commutant J Ω hsep hcyc]
      change R (star (star b₁.val) Ω) = R (b₁.val Ω)
      rw [star_star]
    have hws' : star w.val Ω = R (b₂.val Ω) := by
      rw [hws, show star b₂.val = (star b₂).val from rfl,
        tomitaMiddleOperator_commutant J Ω hsep hcyc]
      change R (star (star b₂.val) Ω) = R (b₂.val Ω)
      rw [star_star]
    have hl : inner ℂ (y.val Ω) (b (w.val Ω)) =
        inner ℂ ((T * conjugationOperator C b * T) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hy, hw, tomitaMiddleOperator_inner_swap J Ω hsep hcyc,
        tomitaMiddleOperator_polar J Ω hsep hcyc (b₂.val Ω)]
      rfl
    have hr₁ : inner ℂ (y.val Ω) (w.val (x.val Ω)) =
        inner ℂ ((Q * x.val * R) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hy, tomitaMiddleOperator_inner_swap J Ω hsep hcyc]
      change inner ℂ (T (C ((w * x).val Ω))) (b₁.val Ω) = _
      rw [tomitaMiddleOperator_algebra J Ω hsep hcyc (w * x)]
      change inner ℂ (Q (star (w.val * x.val) Ω)) (b₁.val Ω) = _
      rw [star_mul]
      rw [show star x.val = x.val from congrArg Subtype.val hx.star_eq]
      change inner ℂ (Q (x.val (star w.val Ω))) (b₁.val Ω) = _
      rw [hws']
      rfl
    have hr₂ : inner ℂ (y.val (x.val Ω)) (w.val Ω) =
        inner ℂ ((R * x.val * Q) (b₂.val Ω)) (b₁.val Ω) := by
      rw [hw]
      have he := congrArg star (tomitaMiddleOperator_inner_swap J Ω hsep hcyc
        (b₂.val Ω) ((y * x).val Ω))
      change (starRingEnd ℂ) (inner ℂ (T (C (b₂.val Ω))) ((y * x).val Ω)) =
        (starRingEnd ℂ) (inner ℂ (T (C ((y * x).val Ω))) (b₂.val Ω)) at he
      rw [inner_conj_symm, inner_conj_symm] at he
      change inner ℂ ((y * x).val Ω) (T (C (b₂.val Ω))) = _
      rw [he, tomitaMiddleOperator_algebra J Ω hsep hcyc (y * x)]
      change inner ℂ (b₂.val Ω) (Q (star (y.val * x.val) Ω)) = _
      rw [star_mul]
      rw [show star x.val = x.val from congrArg Subtype.val hx.star_eq]
      change inner ℂ (b₂.val Ω) (Q (x.val (star y.val Ω))) = _
      rw [hys', ← ContinuousLinearMap.adjoint_inner_left, hQ,
        ← ContinuousLinearMap.adjoint_inner_left, hx',
        ← ContinuousLinearMap.adjoint_inner_left, hR]
      rfl
    have hp := modular_pairing_products Ω b hb hbs z x hpair y w
    rw [hl, hr₁, hr₂] at hp
    simp only [smul_apply, add_apply, inner_smul_left, inner_add_left,
      map_ofNat, starRingEnd_apply, star_star]
    exact hp
  have hd : DenseRange (fun b : Algebra M.commutant => b.val Ω) :=
    Generator.commutant_orbit_dense M Ω (fun a ha => hsep ha)
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  exact hd.induction_on₂ (p := fun w v =>
    inner ℂ (((2 : ℂ) • (T * conjugationOperator C b * T)) v) w =
      inner ℂ ((star z • (Q * x.val * R) + z • (R * x.val * Q)) v) w)
    (isClosed_eq (by fun_prop) (by fun_prop)) hcore w v

end

end KadisonKastler

end OAI
