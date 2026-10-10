import OAI.NumberTheory.DirichletL.Moments.Canonical
import OAI.NumberTheory.DirichletL.ResidueCharacter

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O

theorem crtCharacter_eq_one_iff {S ι : Type*} [CommRing S] [Fintype ι]
    {R : ι → Type*} [∀ i, CommRing (R i)]
    (e : S ≃+* ∀ i, R i) (χ : ∀ i, MulChar (R i) ℂ) :
    crtCharacter e χ = 1 ↔ ∀ i, χ i = 1 := by
  constructor
  · intro h i
    apply MulChar.ext
    intro u
    let v : ∀ j, R j := Function.update (fun _ => 1) i (u : R i)
    have hv : IsUnit v := by
      rw [Pi.isUnit_iff]
      intro j
      by_cases hj : j = i
      · subst j
        simp [v]
      · simp [v, hj]
    have hx : IsUnit (e.symm v) := hv.map e.symm.toMonoidHom
    have heq := congrArg (fun f : MulChar S ℂ => f (e.symm v)) h
    rw [crtCharacter_apply, e.apply_symm_apply, MulChar.one_apply hx] at heq
    have hprod : (∏ j, χ j (v j)) = χ i (u : R i) := by
      rw [Finset.prod_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hprod] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · intro h
    apply MulChar.ext
    intro u
    rw [crtCharacter_apply, MulChar.one_apply u.isUnit]
    apply Finset.prod_eq_one
    intro i _
    rw [h i, MulChar.one_apply]
    exact (u.isUnit.map e.toMonoidHom).map (Pi.evalMonoidHom _ i)

theorem primePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    {c : ℕ} (hc : 1 ≤ c) (χ : MulChar (O ⧸ P) ℂ) :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      change Ideal.Quotient.mk P a = (u : O ⧸ P) at hx
      rw [hx]
      exact u.isUnit
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six P hg hchar]

theorem canonicalCRTCharacter_eq_one_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    canonicalCRTCharacter P hg c hc hcop = 1 ↔ ∀ i, 6 ∣ c i := by
  rw [canonicalCRTCharacter, crtCharacter_eq_one_iff]
  exact forall_congr' (fun i => canonicalPrimePowerCharacter_eq_one_iff (P i) (hg i) (hchar i) (hc i))

theorem product_nonprincipal_of_coprime {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : IsCoprime I J)
    (φ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) (hψ : ψ ≠ 1) :
    ResidueCharacter.product I J φ ψ ≠ 1 := by
  intro h
  apply hψ
  apply MulChar.ext
  intro u
  let e := Ideal.quotientInfEquivQuotientProd I J hIJ
  obtain ⟨x,hx⟩ := e.surjective ((1 : A ⧸ I), (u : A ⧸ J))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk I a, Ideal.Quotient.mk J a) = (1, (u : A ⧸ J)) at hx
  have hI := congrArg Prod.fst hx
  have hJ := congrArg Prod.snd hx
  dsimp only at hI hJ
  have hu : IsUnit (Ideal.Quotient.mk (I ⊓ J) a) := by
    apply (ResidueCharacter.isUnit_mk_inf_iff I J a).mpr
    constructor
    · rw [hI]
      exact isUnit_one
    · rw [hJ]
      exact u.isUnit
  have heq := congrArg (fun χ : MulChar (A ⧸ I ⊓ J) ℂ =>
    χ (Ideal.Quotient.mk (I ⊓ J) a)) h
  rw [ResidueCharacter.product_mk, hI, hJ, map_one, one_mul, MulChar.one_apply hu] at heq
  simpa only [MulChar.one_apply u.isUnit] using heq

theorem nonprincipal_fixed_times_local (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : c < 6)
    (hcop : IsCoprime Q (P^c)) (φ : MulChar (O ⧸ Q) ℂ) :
    ResidueCharacter.product Q (P^c) φ (canonicalPrimePowerCharacter P hg hc) ≠ 1 := by
  apply product_nonprincipal_of_coprime _ _ hcop
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by omega) hc6
    ((canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)

end SevenEighths.HeckeLocalRamification

end

end OAI
