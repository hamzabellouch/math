import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.FormalEtale
import OAI.AlgebraicGeometry.Seshadri.Analytic.FormalSeries

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries
open MaximalSeshadri.FormalCoordinates

def analyticFirst : analyticFunctionAlgebra := ⟨Prod.fst, analyticAt_fst⟩
def analyticSecond : analyticFunctionAlgebra := ⟨Prod.snd, analyticAt_snd⟩

lemma analyticFormal_first : analyticFormal analyticFirst = C (X : PowerSeries ℂ) := by
  have hc := analyticCoefficients_monomial analyticFirst (1,0) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticFirst])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticFirst)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, coeff_X, hb, Prod.ext_iff]

lemma analyticFormal_second : analyticFormal analyticSecond = (X : BiSeries) := by
  have hc := analyticCoefficients_monomial analyticSecond (0,1) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticSecond])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticSecond)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 1 <;> simp [biCoeff, coeff_X, hb, Prod.ext_iff]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def analyticPullback (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : S →ₐ[ℂ] analyticFunctionAlgebra where
  toFun s := ⟨fun z => q z s, hq s⟩
  map_one' := Subtype.ext (funext fun z => (q z).map_one)
  map_mul' s t := Subtype.ext (funext fun z => (q z).map_mul s t)
  map_zero' := Subtype.ext (funext fun z => (q z).map_zero)
  map_add' s t := Subtype.ext (funext fun z => (q z).map_add s t)
  commutes' c := Subtype.ext (funext fun z => (q z).commutes c)

def analyticTaylor (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    S →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  (binaryEquiv ℂ).symm.toAlgHom.comp (analyticFormal.comp (analyticPullback q hq))

lemma analyticTaylor_constantCoeff (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.constantCoeff (analyticTaylor q hq s) = q 0 s := by
  rw [← binaryEquiv_constantCoeff]
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact analyticFormal_constantCoeff _

lemma analyticTaylor_affineFirst (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) (c : ℂ)
    (hs : ∀ᶠ z in 𝓝 0, q z s = c + z.1) :
    analyticTaylor q hq s = MvPowerSeries.C c + MvPowerSeries.X 1 := by
  apply (binaryEquiv ℂ).injective
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, map_add, binaryEquiv_X_one]
  have heq : analyticFormal (analyticPullback q hq s) =
      analyticFormal (algebraMap ℂ analyticFunctionAlgebra c + analyticFirst) :=
    analyticFormal_congr _ _ hs
  rw [heq, map_add, analyticFormal_first, AlgHom.commutes]
  congr 1
  exact ((binaryEquiv ℂ).commutes c).symm

lemma analyticTaylor_affineSecond (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) (c : ℂ)
    (hs : ∀ᶠ z in 𝓝 0, q z s = c + z.2) :
    analyticTaylor q hq s = MvPowerSeries.C c + MvPowerSeries.X 0 := by
  apply (binaryEquiv ℂ).injective
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, map_add, binaryEquiv_X_zero]
  have heq : analyticFormal (analyticPullback q hq s) =
      analyticFormal (algebraMap ℂ analyticFunctionAlgebra c + analyticSecond) :=
    analyticFormal_congr _ _ hs
  rw [heq, map_add, analyticFormal_second, AlgHom.commutes]
  congr 1
  exact ((binaryEquiv ℂ).commutes c).symm

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

omit [Finite σ] in

lemma jetChart_unique [Algebra.FormallyUnramified (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n)
    (τ₁ τ₂ : S →ₐ[F] JetAlgebra σ F n)
    (hc : τ₁.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      τ₂.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S))
    (haug : ∀ s, jetAugment n hn (τ₁ s) = jetAugment n hn (τ₂ s)) : τ₁ = τ₂ := by
  let β := τ₁.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
  let : Algebra (MvPolynomial σ F) (JetAlgebra σ F n) := β.toRingHom.toAlgebra
  let f₁ : S →ₐ[MvPolynomial σ F] JetAlgebra σ F n :=
    { τ₁.toRingHom with commutes' := fun _ => rfl }
  let f₂ : S →ₐ[MvPolynomial σ F] JetAlgebra σ F n :=
    { τ₂.toRingHom with commutes' := fun p => (AlgHom.congr_fun hc p).symm }
  have heq := Algebra.FormallyUnramified.lift_unique_of_ringHom
    (R := MvPolynomial σ F) (jetAugment (σ := σ) (R := F) n hn).toRingHom
    (jetAugment_ker_nilpotent n hn) f₁ f₂ (RingHom.ext haug)
  apply AlgHom.ext
  intro s
  have hs : f₁ s = f₂ s := AlgHom.congr_fun heq s
  exact hs

def formalTrunc (n : ℕ) : MvPowerSeries σ F →ₐ[F] JetAlgebra σ F n :=
  (MvPowerSeries.truncTotalAlgHom σ F n).restrictScalars F

lemma formalTrunc_augment (n : ℕ) (hn : 0 < n) (f : MvPowerSeries σ F) :
    jetAugment n hn (formalTrunc n f) = MvPowerSeries.constantCoeff f := by
  change jetAugment n hn (Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f)) = _
  rw [jetAugment_mk, MvPowerSeries.constantCoeff_truncTotal_eq_ite, ite_eq_left hn]

lemma formalTrunc_polynomial (n : ℕ) (p : MvPolynomial σ F) :
    formalTrunc n (p : MvPowerSeries σ F) = Ideal.Quotient.mk _ p :=
  (MvPowerSeries.truncTotalAlgHom σ F n).commutes p

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem formalTaylor_detects_ideal_power
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) (hn : 0 < n) :
    RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n := by
  obtain ⟨g, hg, hgc⟩ := exists_regular_taylor (σ := σ) (F := F) (S := S) n hn
  have heq : (formalTrunc n).comp τ = specializeTaylor n g ρ := by
    apply jetChart_unique n hn
    · rw [specializeTaylor_coordinate n g hgc ρ]
      ext i
      change formalTrunc n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
      rw [hcoord]
      have hpoly := formalTrunc_polynomial n
        (C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + X i)
      simpa [polynomialTranslate, add_comm] using hpoly
    · intro s
      rw [AlgHom.comp_apply, formalTrunc_augment n hn, hconst,
        specializeTaylor_augment n hn g hg]
  rw [heq]
  exact regularTaylor_detects_ideal_power n hn g hg hgc ρ

theorem formalTaylor_injective [IsNoetherianRing S] [IsDomain S]
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i) :
    Function.Injective τ := by
  apply (injective_iff_map_eq_zero τ).mpr
  intro s hs
  have hproper : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top _
  have hmem : s ∈ ⨅ n : ℕ, (RingHom.ker ρ)^n := by
    rw [Ideal.mem_iInf]
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [← formalTaylor_detects_ideal_power ρ τ hconst hcoord n (Nat.pos_of_ne_zero hn)]
      change formalTrunc n (τ s) = 0
      rw [hs, map_zero]
  have hsep : (⨅ n : ℕ, (RingHom.ker ρ)^n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain (I := RingHom.ker ρ) hproper
  rw [hsep] at hmem
  exact hmem

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open MaximalSeshadri.AlgebraicJets
variable {S : Type*} [CommRing S] [Algebra ℂ S]
  [Algebra (MvPolynomial (Fin 2) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]

omit [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S] in

lemma analyticTaylor_coordinates
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) (i : Fin 2) :
    analyticTaylor q hq (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      MvPowerSeries.C (q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i))) +
        MvPowerSeries.X i := by
  fin_cases i
  · apply analyticTaylor_affineSecond
    filter_upwards [hc] with z hz
    simpa using hz 0
  · apply analyticTaylor_affineFirst
    filter_upwards [hc] with z hz
    simpa using hz 1

theorem analyticTaylor_detects_ideal_power
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) (n : ℕ) (hn : 0 < n) :
    RingHom.ker ((formalTrunc n).comp (analyticTaylor q hq)) = (RingHom.ker (q 0))^n :=
  formalTaylor_detects_ideal_power (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) (analyticTaylor_coordinates q hq hc) n hn

theorem analyticTaylor_injective [IsNoetherianRing S] [IsDomain S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) :
    Function.Injective (analyticTaylor q hq) :=
  formalTaylor_injective (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) (analyticTaylor_coordinates q hq hc)

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
