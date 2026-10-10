import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.LocalQuotients

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open IsLocalRing

lemma ringEnd_injective_of_surjective {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hs : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal R := {
    toFun := fun n => RingHom.ker (f ^ n)
    monotone' := by
      apply monotone_nat_of_le_succ
      intro n x hx
      change (f ^ (n + 1)) x = 0
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply]
      change (f ^ n) x = 0 at hx
      rw [hx, map_zero] }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (show IsNoetherian R R from inferInstance) K
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := hs.iterate n x
  have hy' : (f ^ n) y = x := hy
  have hm : y ∈ K (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hy']
    exact hx
  rw [← hn (n + 1) (Nat.le_succ n)] at hm
  change (f ^ n) y = 0 at hm
  exact (hy'.symm.trans hm)

variable {σ K : Type*} [Finite σ] [Field K]

local notation "P" => MvPowerSeries σ K
local notation "𝔪" => maximalIdeal P

lemma complete_maximal : IsAdicComplete 𝔪 P := by
  rw [FormalAdic.maximalIdeal_eq_vars]
  infer_instance

lemma map_maximal_eq_of_cotangent (φ : P →ₐ[K] P)
    (hlocal : (𝔪).map φ.toRingHom ≤ 𝔪)
    (htangent : 𝔪 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) :
    (𝔪).map φ.toRingHom = 𝔪 := by
  apply le_antisymm hlocal
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian 𝔪)
    (show 𝔪 ≤ Ideal.jacobson (⊥ : Ideal P) by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  simpa only [pow_two, Ideal.smul_eq_mul] using htangent

lemma bijective_of_cotangent (φ : P →ₐ[K] P)
    (hlocal : (𝔪).map φ.toRingHom ≤ 𝔪)
    (htangent : 𝔪 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) :
    Function.Bijective φ := by
  let := complete_maximal (σ := σ) (K := K)
  have hm := map_maximal_eq_of_cotangent φ hlocal htangent
  let : IsHausdorff ((𝔪).map φ.toRingHom) P := by
    rw [hm]
    infer_instance
  have hs : Function.Surjective φ := by
    apply surjective_of_mk_map_comp_surjective (I := 𝔪) φ.toRingHom
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap K P (MvPowerSeries.constantCoeff f), ?_⟩
    change Ideal.Quotient.mk _ (φ (algebraMap K P _)) = _
    rw [φ.commutes, Ideal.Quotient.eq]
    rw [hm, FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp [MvPowerSeries.algebraMap_apply]
  exact ⟨ringEnd_injective_of_surjective φ.toRingHom hs, hs⟩

def equivOfCotangent (φ : P →ₐ[K] P)
    (hlocal : (𝔪).map φ.toRingHom ≤ 𝔪)
    (htangent : 𝔪 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) : P ≃ₐ[K] P :=
  AlgEquiv.ofBijective φ (bijective_of_cotangent φ hlocal htangent)

omit [Finite σ] in

lemma equiv_comap_pow_maximal (e : P ≃ₐ[K] P) (n : ℕ) :
    (𝔪 ^ n).comap e.toRingHom = 𝔪 ^ n := by
  have hm : (𝔪).map e.toRingHom = 𝔪 := by
    apply IsLocalRing.eq_maximalIdeal
    change (Ideal.map e.toRingEquiv 𝔪).IsMaximal
    infer_instance
  calc
    (𝔪 ^ n).comap e.toRingHom = ((𝔪).map e.toRingHom ^ n).comap e.toRingHom :=
      congrArg (fun J : Ideal P => (J ^ n).comap e.toRingHom) hm.symm
    _ = 𝔪 ^ n := by
      rw [← Ideal.map_pow, Ideal.comap_map_of_bijective e.toRingHom e.bijective]

lemma mem_maximal_pow_iff (f : P) (n : ℕ) :
    f ∈ 𝔪 ^ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → MvPowerSeries.coeff d f = 0 := by
  rw [← FormalAdic.trunc_kernel_maximalIdeal, RingHom.mem_ker]
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor <;> intro h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd

lemma mem_maximal_sq_iff (f : P) :
    f ∈ 𝔪 ^ 2 ↔ MvPowerSeries.constantCoeff f = 0 ∧
      ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  rw [mem_maximal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun i => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ d hd
    by_cases he : d.degree = 0
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp he
      simpa [this] using h0
    · have he : d.degree = 1 := by omega
      obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr he
      exact h1 i

variable [Fintype σ] [DecidableEq σ]

lemma subst_bijective_of_inverse_linear (a : σ → P)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (b : σ → σ → K)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1) (a l) =
      if i = j then 1 else 0) :
    Function.Bijective (MvPowerSeries.substAlgHom (R := K)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)) := by
  classical
  let φ : P →ₐ[K] P := MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)
  have hx (i : σ) : (MvPowerSeries.X i : P) ∈ 𝔪 := by
    rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp
  have hlocal : (𝔪).map φ.toRingHom ≤ 𝔪 := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply le_trans (FormalAdic.maximalIdeal_eq_vars (σ := σ) (K := K)).le
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    change φ (MvPowerSeries.X i) ∈ 𝔪
    rw [MvPowerSeries.substAlgHom_X, FormalAdic.maximalIdeal_eq_ker_constantCoeff,
      RingHom.mem_ker]
    exact h0 i
  apply bijective_of_cotangent φ hlocal
  apply le_trans (FormalAdic.maximalIdeal_eq_vars (σ := σ) (K := K)).le
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  let s : P := ∑ l, MvPowerSeries.C (b i l) * a l
  have hs : s ∈ (𝔪).map φ.toRingHom := by
    apply Ideal.sum_mem
    intro l _
    apply Ideal.mul_mem_left
    have h := Ideal.mem_map_of_mem φ.toRingHom (hx l)
    simpa only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_X] using h
  have hd : (MvPowerSeries.X i : P) - s ∈ 𝔪 ^ 2 := by
    rw [mem_maximal_sq_iff]
    constructor
    · simp [s, h0]
    · intro j
      simp only [s, map_sub, map_sum, MvPowerSeries.coeff_C_mul]
      rw [hb]
      simp only [MvPowerSeries.coeff_X]
      simp only [Finsupp.single_left_inj (show (1 : ℕ) ≠ 0 by omega), eq_comm,
        sub_self]
  have hh := Submodule.add_mem
    ((𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) ((show 𝔪 ^ 2 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2 from le_sup_right) hd)
      ((show (𝔪).map φ.toRingHom ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2 from le_sup_left) hs)
  change (MvPowerSeries.X i : P) ∈ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2
  convert hh using 1
  exact (sub_add_cancel _ _).symm

omit [Finite σ] [Fintype σ] [DecidableEq σ] in

lemma constantCoeff_equiv (e : P ≃ₐ[K] P) (f : P) :
    MvPowerSeries.constantCoeff (e f) = MvPowerSeries.constantCoeff f := by
  have hf : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈ 𝔪 := by
    rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp
  have he : e (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) ∈ 𝔪 := by
    have hh := equiv_comap_pow_maximal e 1
    simp only [pow_one] at hh
    rw [← hh] at hf
    exact hf
  rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker] at he
  have hc (c : K) : e (MvPowerSeries.C c) = MvPowerSeries.C c := e.commutes c
  simpa only [map_sub, hc, MvPowerSeries.constantCoeff_C, sub_eq_zero] using he

end
end MaximalSeshadri.FormalCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open IsLocalRing MvPolynomial
open FormalCoordinates
variable {σ F S : Type*} [Fintype σ] [DecidableEq σ] [Field F]
  [CommRing S] [Algebra F S] [Algebra (MvPolynomial σ F) S]
  [IsScalarTower F (MvPolynomial σ F) S]

local notation "P" => MvPowerSeries σ F

omit [IsScalarTower F (MvPolynomial σ F) S] in

lemma exists_standardized_formalTaylor (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0) :
    ∃ e : P ≃ₐ[F] P,
      (∀ s, MvPowerSeries.constantCoeff (e.symm (τ s)) = ρ s) ∧
      ∀ i, e.symm (τ (algebraMap (MvPolynomial σ F) S (X i))) =
        MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) +
          MvPowerSeries.X i := by
  let a (i : σ) : P := τ (algebraMap (MvPolynomial σ F) S (X i)) -
    MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i)))
  have ha (i : σ) : MvPowerSeries.constantCoeff (a i) = 0 := by
    simp [a, hconst]
  have hab (i j : σ) : ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1) (a l) =
      if i = j then 1 else 0 := by
    simpa [a, MvPowerSeries.coeff_C] using hb i j
  let φ : P →ₐ[F] P := MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
  let e : P ≃ₐ[F] P := AlgEquiv.ofBijective φ
    (subst_bijective_of_inverse_linear a ha b hab)
  refine ⟨e, fun s => (constantCoeff_equiv e.symm (τ s)).trans (hconst s), ?_⟩
  intro i
  apply e.injective
  rw [AlgEquiv.apply_symm_apply, map_add]
  have heC (c : F) : e (MvPowerSeries.C c) = MvPowerSeries.C c := e.commutes c
  rw [heC]
  change τ _ = MvPowerSeries.C _ + φ (MvPowerSeries.X i)
  rw [MvPowerSeries.substAlgHom_X]
  dsimp [a]
  ring

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem fullRankTaylor_localJet_kernel (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0)
    (n : ℕ) : RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal P ^ n)).comp τ.toRingHom) = (RingHom.ker ρ)^n := by
  obtain ⟨e, hec, hex⟩ := exists_standardized_formalTaylor ρ τ hconst b hb
  let τ₀ : S →ₐ[F] P := e.symm.toAlgHom.comp τ
  have hk := formalTaylor_localJet_kernel ρ τ₀ hec hex n
  rw [← RingHom.comap_ker, Ideal.mk_ker] at hk ⊢
  change (maximalIdeal P ^ n).comap τ.toRingHom = _
  rw [← hk]
  change _ = ((maximalIdeal P ^ n).comap e.symm.toRingHom).comap τ.toRingHom
  rw [equiv_comap_pow_maximal]

omit [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S] in
                                                                     
theorem fullRankTaylor_surjective_localJet (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0)
    (n : ℕ) : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal P ^ n)).comp τ.toRingHom) := by
  obtain ⟨e, hec, hex⟩ := exists_standardized_formalTaylor ρ τ hconst b hb
  let τ₀ : S →ₐ[F] P := e.symm.toAlgHom.comp τ
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨s, hs⟩ := formalTaylor_surjective_localJet ρ τ₀ hex n
    (Ideal.Quotient.mk _ (e.symm f))
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  have hh : e.symm (τ s - f) ∈ maximalIdeal P ^ n := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hs
  have hm := equiv_comap_pow_maximal e.symm n
  change τ s - f ∈ (maximalIdeal P ^ n).comap e.symm.toRingHom at hh
  rwa [hm] at hh

end
end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
