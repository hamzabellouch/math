import Mathlib

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.FormalAdic
noncomputable section
open IsLocalRing
variable {σ R : Type*} [Finite σ] [CommRing R]

lemma completion_eval_kernel (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext x
  have h := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n) hI
  have heval : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I R n x = 0 := by
    let e := Ideal.quotientEquivAlgOfEq R (show (I ^ n • ⊤ : Ideal R) = I ^ n by simp)
    dsimp only [AdicCompletion.evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply]
    exact map_eq_zero_iff e e.injective
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  rw [heval, ← LinearMap.mem_ker, ← h]
  rw [← Ideal.map_pow]
  simp

lemma trunc_eq_completion_eval (n : ℕ) :
    (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (AdicCompletion.evalₐ (MvPolynomial.idealOfVars σ R) n).toRingHom.comp
        (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingHom := by
  apply RingHom.ext
  intro f
  change (MvPowerSeries.truncTotalAlgHom σ R n) f =
    AdicCompletion.evalₐ _ n (MvPowerSeries.toAdicCompletion σ R f)
  unfold MvPowerSeries.toAdicCompletion
  erw [AdicCompletion.evalₐ_liftAlgHom]
  intro m n h
  apply AlgHom.ext
  intro p
  simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
    MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) p

omit [Finite σ] in
lemma polynomials_map_vars :
    (MvPolynomial.idealOfVars σ R).map
        (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.coe_X i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, MvPolynomial.coe_X i⟩

lemma trunc_kernel (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  let e := MvPowerSeries.toAdicCompletionAlgEquiv σ R
  rw [trunc_eq_completion_eval, ← RingHom.comap_ker,
    completion_eval_kernel _ (MvPolynomial.idealOfVars_fg σ R)]
  have he : (algebraMap (MvPolynomial σ R) (AdicCompletion (MvPolynomial.idealOfVars σ R)
      (MvPolynomial σ R))) = e.toRingHom.comp
      (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) := by
    apply RingHom.ext
    intro p
    exact (e.commutes p).symm
  rw [he, ← Ideal.map_map, ← Ideal.map_pow]
  change (Ideal.map e.toRingHom _).comap e.toRingHom = _
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective, polynomials_map_vars]

variable {K : Type*} [Field K]

omit [Finite σ] in
lemma maximalIdeal_eq_ker_constantCoeff :
    maximalIdeal (MvPowerSeries σ K) =
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ K →+* K) := by
  ext f
  rw [mem_maximalIdeal, mem_nonunits_iff, RingHom.mem_ker, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

lemma maximalIdeal_eq_vars :
    maximalIdeal (MvPowerSeries σ K) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) := by
  rw [← pow_one (Ideal.span _), ← trunc_kernel]
  ext f
  rw [maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker, RingHom.mem_ker]
  change _ ↔ Ideal.Quotient.mk _ (MvPowerSeries.truncTotal 1 f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    rw [MvPowerSeries.coeff_truncTotal _ hd, hd0]
    exact hf
  · intro hf
    simpa [MvPowerSeries.coeff_truncTotal _ (show (0 : σ →₀ ℕ).degree < 1 by simp)]
      using hf 0 (by simp)

lemma trunc_kernel_maximalIdeal (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ K n).toRingHom =
      maximalIdeal (MvPowerSeries σ K) ^ n := by
  rw [trunc_kernel, maximalIdeal_eq_vars]

end
end MaximalSeshadri.FormalAdic

namespace MaximalSeshadri.LocalComparison
noncomputable section
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S]

lemma comap_extension_sup (f : R →+* S) (a : Ideal R) (b : Ideal S) (n : ℕ)
    (hs : Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp f))
    (hk : RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp f) = a ^ n)
    (I : Ideal R) :
    (I.map f ⊔ b ^ n).comap f = I ⊔ a ^ n := by
  have hq := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk (b ^ n))
    Ideal.Quotient.mk_surjective (I.map f)
  rw [Ideal.mk_ker] at hq
  rw [← hq, Ideal.comap_comap, Ideal.map_map,
    Ideal.comap_map_of_surjective' _ hs, hk]

lemma adicClosed [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (⨅ n : ℕ, I ⊔ maximalIdeal R ^ n) = I := by
  by_cases hI : I = ⊤
  · simp [hI]
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  apply le_antisymm
  · intro x hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hx' : Ideal.Quotient.mk I x ∈
        (⨅ n : ℕ, maximalIdeal (R ⧸ I) ^ n) := by
      rw [Submodule.mem_iInf] at hx ⊢
      intro n
      have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) (hx n)
      rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
        Ideal.map_pow, map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at hx'
    exact hx'
  · exact le_iInf fun n => le_sup_left

theorem contractExtension [IsNoetherianRing R] [IsLocalRing R]
    (f : R →+* S) (b : Ideal S)
    (hs : ∀ n : ℕ, Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp f))
    (hk : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp f) =
      maximalIdeal R ^ n) (I : Ideal R) :
    (I.map f).comap f = I := by
  apply le_antisymm
  · calc
      (I.map f).comap f ≤ ⨅ n : ℕ, I ⊔ maximalIdeal R ^ n := by
        apply le_iInf
        intro n
        rw [← comap_extension_sup f (maximalIdeal R) b n (hs n) (hk n) I]
        exact Ideal.comap_mono le_sup_left
      _ = I := adicClosed I
  · exact Ideal.le_comap_map

lemma quotientMap_surjective_of_finiteJet (f : R →+* S) (b : Ideal S)
    (I : Ideal R) (N : ℕ)
    (hs : Function.Surjective ((Ideal.Quotient.mk (b ^ N)).comp f))
    (hN : b ^ N ≤ I.map f) :
    Function.Surjective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hs (Ideal.Quotient.mk (b ^ N) y)
  refine ⟨Ideal.Quotient.mk I x, ?_⟩
  rw [Ideal.quotientMap_mk]
  apply Ideal.Quotient.eq.mpr
  apply hN
  exact Ideal.Quotient.eq.mp hx

def quotientEquiv [IsNoetherianRing R] [IsLocalRing R]
    {K : Type*} [CommRing K] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (b : Ideal S)
    (hs : ∀ n : ℕ, Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp f.toRingHom))
    (hk : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp f.toRingHom) =
      maximalIdeal R ^ n) (I : Ideal R) (N : ℕ)
    (hN : b ^ N ≤ I.map f.toRingHom) :
    (R ⧸ I) ≃ₐ[K] (S ⧸ I.map f.toRingHom) := by
  apply AlgEquiv.ofBijective (Ideal.quotientMapₐ (I.map f.toRingHom) f Ideal.le_comap_map)
  constructor
  · exact Ideal.quotientMap_injective' (f := f.toRingHom)
      (H := Ideal.le_comap_map) (contractExtension f.toRingHom b hs hk I).le
  · exact quotientMap_surjective_of_finiteJet f.toRingHom b I N (hs N) hN

theorem colength_eq [IsNoetherianRing R] [IsLocalRing R]
    {K : Type*} [Field K] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (b : Ideal S)
    (hs : ∀ n : ℕ, Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp f.toRingHom))
    (hk : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp f.toRingHom) =
      maximalIdeal R ^ n) (I : Ideal R) (N : ℕ)
    (hN : b ^ N ≤ I.map f.toRingHom) :
    Module.finrank K (R ⧸ I) = Module.finrank K (S ⧸ I.map f.toRingHom) :=
  (quotientEquiv f b hs hk I N hN).toLinearEquiv.finrank_eq

lemma exists_pow_le_of_finite [IsNoetherianRing S] [IsLocalRing S]
    {K : Type*} [Field K] [Algebra K S] (J : Ideal S)
    [FiniteDimensional K (S ⧸ J)] :
    ∃ N : ℕ, maximalIdeal S ^ N ≤ J := by
  by_cases hJ : J = ⊤
  · exact ⟨0, by simp [hJ]⟩
  let : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite K _
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (S ⧸ J)).mp this
  refine ⟨N, ?_⟩
  rw [← Ideal.mk_ker (I := J)]
  apply (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk J)).mp
  rw [Ideal.map_pow, map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  exact hN

def finiteQuotientEquiv [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S]
    {K : Type*} [Field K] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S)
    (hs : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp f.toRingHom))
    (hk : ∀ n : ℕ, RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp f.toRingHom) = maximalIdeal R ^ n)
    (I : Ideal R) [FiniteDimensional K (S ⧸ I.map f.toRingHom)] :
    (R ⧸ I) ≃ₐ[K] (S ⧸ I.map f.toRingHom) :=
  quotientEquiv f (maximalIdeal S) hs hk I
    (exists_pow_le_of_finite (K := K) (I.map f.toRingHom)).choose
    (exists_pow_le_of_finite (K := K) (I.map f.toRingHom)).choose_spec

section Localization
variable (m : Ideal R) [m.IsPrime]
variable {A : Type*} [CommRing A] [Algebra R A]
  [IsLocalization.AtPrime A m] [IsLocalRing A]

lemma localizedJet_kernel (f : R →+* S) (F : A →+* S)
    (hF : F.comp (algebraMap R A) = f) (b : Ideal S) (n : ℕ)
    (hk : RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp f) = m ^ n) :
    RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp F) = maximalIdeal A ^ n := by
  let J := RingHom.ker ((Ideal.Quotient.mk (b ^ n)).comp F)
  have hc : J.under R = m ^ n := by
    change Ideal.comap (algebraMap R A) J = m ^ n
    dsimp only [J]
    rw [RingHom.comap_ker, RingHom.comp_assoc, hF, hk]
  calc
    J = (J.under R).map (algebraMap R A) :=
      (IsLocalization.map_under m.primeCompl A J).symm
    _ = (m ^ n).map (algebraMap R A) := by rw [hc]
    _ = maximalIdeal A ^ n := by
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal m A]

omit [IsLocalRing A] in

lemma localizedJet_surjective (f : R →+* S) (F : A →+* S)
    (hF : F.comp (algebraMap R A) = f) (b : Ideal S) (n : ℕ)
    (hs : Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp f)) :
    Function.Surjective ((Ideal.Quotient.mk (b ^ n)).comp F) := by
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨algebraMap R A x, ?_⟩
  change (Ideal.Quotient.mk (b ^ n)) ((F.comp (algebraMap R A)) x) = y
  rwa [hF]

end Localization

lemma image_primeCompl_isUnit [IsLocalRing S] (m : Ideal R) [m.IsPrime]
    (f : R →+* S) (h : (maximalIdeal S).comap f = m) (s : m.primeCompl) :
    IsUnit (f s) := by
  apply notMem_maximalIdeal.mp
  intro hs
  have hm : (s : R) ∈ (maximalIdeal S).comap f := hs
  rw [h] at hm
  exact s.property hm

def localTaylorLift [IsLocalRing S] {K : Type*} [CommRing K]
    [Algebra K R] [Algebra K S] (m : Ideal R) [m.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra K A]
    [IsScalarTower K R A] [IsLocalization.AtPrime A m]
    (f : R →ₐ[K] S) (h : (maximalIdeal S).comap f.toRingHom = m) : A →ₐ[K] S :=
  IsLocalization.liftAlgHom (image_primeCompl_isUnit m f.toRingHom h)

lemma localTaylorLift_comp [IsLocalRing S] {K : Type*} [CommRing K]
    [Algebra K R] [Algebra K S] (m : Ideal R) [m.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra K A]
    [IsScalarTower K R A] [IsLocalization.AtPrime A m]
    (f : R →ₐ[K] S) (h : (maximalIdeal S).comap f.toRingHom = m) :
    (localTaylorLift m A f h).toRingHom.comp (algebraMap R A) = f.toRingHom :=
  IsLocalization.lift_comp (image_primeCompl_isUnit m f.toRingHom h)

end
end MaximalSeshadri.LocalComparison


end
end
end

end OAI
