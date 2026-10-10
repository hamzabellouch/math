import OAI.AlgebraicGeometry.SurfaceCones.RingProperties
import OAI.AlgebraicGeometry.SurfaceCones.ConeMorphism

namespace OAI


/-! Depth localization and reflexivity of finite maximal Cohen–Macaulay modules. -/

noncomputable section
namespace SmallCM

namespace LocalizationDepth

open CategoryTheory Abelian Limits IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma subsingleton_ext_of_subsingleton_left (N M : ModuleCat.{u} R)
    [Subsingleton N] (i : ℕ) : Subsingleton (Ext N M i) := by
  have hid : (𝟙 N : N ⟶ N) = 0 := by ext; exact Subsingleton.elim _ _
  apply subsingleton_of_forall_eq 0
  intro e
  calc e = (Ext.mk₀ (𝟙 N)).comp e (zero_add i) := by simp
       _ = 0 := by rw [hid, Ext.mk₀_zero, Ext.zero_comp]

omit [IsNoetherianRing R] in
lemma subsingleton_of_smul_surjective {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] {x : R} (hx : x ∈ maximalIdeal R)
    (hsurj : Function.Surjective (fun v : V => x • v)) : Subsingleton V := by
  by_contra hn
  have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hn
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
    (M := V) (maximalIdeal_le_jacobson _ hx)
  symm
  apply top_unique
  intro v _
  obtain ⟨w, rfl⟩ := hsurj v
  exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)

lemma ext_subsingleton_of_regular_quotient (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M]
    (x : R) (hxm : x ∈ maximalIdeal R) (hx : IsSMulRegular N x) (i : ℕ)
    (hExt : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x N)) M (i+1))) :
    Subsingleton (Ext N M i) := by
  let := hExt
  apply subsingleton_of_smul_surjective hxm
  intro e
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₁
    hx.smulShortComplex_shortExact M e (add_comm 1 i) (by
      change _ = (0 : Ext (ModuleCat.of R (QuotSMulTop x N)) M (i+1))
      exact hExt.elim _ _)
  change Ext N M i at f
  refine ⟨f, ?_⟩
  change (Ext.mk₀ (x • 𝟙 N)).comp f (zero_add i) = e at hf
  rw [Ext.mk₀_smul (R := R), Ext.smul_comp (R := R), Ext.mk₀_id_comp] at hf
  exact hf


lemma ext_subsingleton_of_supportDim_le_zero (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (rs : List R)
    (hm : ∀ x ∈ rs, x ∈ maximalIdeal R) (hr : IsRegular M rs)
    (hdim : Module.supportDim R N ≤ 0) (i : ℕ) (hi : i < rs.length) :
    Subsingleton (Ext N M i) := by
  by_cases hN : Subsingleton N
  · let := hN
    exact subsingleton_ext_of_subsingleton_left N M i
  have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
  have : Nontrivial M := hr.nontrivial
  have hzero : Module.supportDim R N = 0 := by
    apply le_antisymm hdim
    have : Nonempty (Module.support R N) := Module.nonempty_support_of_nontrivial.to_subtype
    exact Order.krullDim_nonneg
  exact ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) N
    (support_of_supportDim_eq_zero R N hzero).le M
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm.lt_top rs hm hr i hi

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma ext_subsingleton_of_shortExact
    {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (M : ModuleCat.{u} R) (i : ℕ)
    (h₁ : Subsingleton (Ext (ModuleCat.of R N₁) M i))
    (h₃ : Subsingleton (Ext (ModuleCat.of R N₃) M i)) :
    Subsingleton (Ext (ModuleCat.of R N₂) M i) := by
  let S := ModuleCat.shortComplexOfCompEqZero f g he.linearMap_comp_eq_zero
  have hs : S.ShortExact := ModuleCat.shortComplex_shortExact S he hf hg
  have zero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₁
  have zero₃ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₃
  exact AddCommGrpCat.subsingleton_of_isZero <|
    ShortComplex.Exact.isZero_of_both_zeros (Ext.contravariant_sequence_exact₂' hs M i)
      (zero₃.eq_zero_of_src _) (zero₁.eq_zero_of_tgt _)


/-- A regular sequence of length `n` forces Ext against every finite module
of support dimension at most `d` to vanish below `n-d`. The proof uses prime
filtrations, the regular-element dimension drop, the long exact Ext sequence,
and Nakayama; it does not assume a depth-localization theorem. -/
lemma ext_vanishing_of_supportDim_le (M : ModuleCat.{u} R)
    [Module.Finite R M] (rs : List R)
    (hm : ∀ x ∈ rs, x ∈ maximalIdeal R) (hr : IsRegular M rs)
    (d : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.supportDim R N ≤ d → ∀ i : ℕ, i + d < rs.length →
      Subsingleton (Ext (ModuleCat.of R N) M i) := by
  induction d generalizing N with
  | zero =>
    intro hdim i hi
    exact ext_subsingleton_of_supportDim_le_zero (ModuleCat.of R N) M rs hm hr hdim i
      (by simpa using hi)
  | succ d ih =>
    refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
      (A := R) (M := N) ‹Module.Finite R N›
      (motive := fun V _ _ _ => Module.supportDim R V ≤ (d+1 : ℕ) →
        ∀ i : ℕ, i + (d+1) < rs.length →
          Subsingleton (Ext (ModuleCat.of R V) M i)) ?_ ?_ ?_
    · intro V _ _ _ _ _ i _
      exact subsingleton_ext_of_subsingleton_left (ModuleCat.of R V) M i
    · intro V _ _ _ p e hdim i hi
      by_cases hp : p.asIdeal = maximalIdeal R
      · apply ext_subsingleton_of_supportDim_le_zero (ModuleCat.of R V) M rs hm hr _ i
          (by omega)
        rw [Module.supportDim_eq_of_equiv e, Module.supportDim_quotient_eq_ringKrullDim,
          hp]
        exact (ringKrullDim_eq_zero_of_isField
          ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)).le
      have hlt : p.asIdeal < maximalIdeal R :=
        lt_of_le_of_ne (le_maximalIdeal p.isPrime.ne_top) hp
      obtain ⟨x, hxm, hxp⟩ := SetLike.exists_of_lt hlt
      have hx : IsSMulRegular V x := by
        apply (e.isSMulRegular_congr x).mpr
        intro a b hab
        have hx0 : (algebraMap R (R ⧸ p.asIdeal)) x ≠ 0 := by
          exact fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
        exact mul_left_cancel₀ hx0 hab
      apply ext_subsingleton_of_regular_quotient (ModuleCat.of R V) M x hxm hx i
      apply ih (QuotSMulTop x V) _ (i+1) (by omega)
      apply ENat.WithBot.add_le_add_one_right_iff.mp
      rw [Module.supportDim_quotSMulTop_succ_eq_supportDim hx hxm]
      simpa using hdim
    · intro V₁ _ _ _ V₂ _ _ _ V₃ _ _ _ f g hf hg he ih₁ ih₃ hdim i hi
      exact ext_subsingleton_of_shortExact f g hf hg he M i
        (ih₁ ((Module.supportDim_le_of_injective f hf).trans hdim) i hi)
        (ih₃ ((Module.supportDim_le_of_surjective g hg).trans hdim) i hi)


/-- A global regular sequence gives a sufficiently long regular sequence
inside any prime, with the loss controlled by the dimension of the quotient. -/
lemma exists_regular_in_prime (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (rs : List R)
    (hm : ∀ x ∈ rs, x ∈ maximalIdeal R) (hr : IsRegular M rs)
    (p : Ideal R) [p.IsPrime] (d : ℕ) (hdim : ringKrullDim (R ⧸ p) ≤ d) :
    ∃ ts : List R, ts.length = rs.length - d ∧ (∀ x ∈ ts, x ∈ p) ∧ IsRegular M ts := by
  have : Nontrivial M := hr.nontrivial
  have hlt : p • (⊤ : Submodule R M) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      ((le_maximalIdeal (Ideal.IsPrime.ne_top' (I := p))).trans
        (maximalIdeal_le_jacobson (Module.annihilator R M)))).symm.lt_top
  refine ModuleCat.exists_isRegular_of_exists_subsingleton_ext p (rs.length-d)
    (ModuleCat.of R M) hlt (ModuleCat.of R (R ⧸ p)) ?_ ?_
  · rw [Module.support_eq_zeroLocus]
    change PrimeSpectrum.zeroLocus (↑(Module.annihilator R (R ⧸ p)) : Set R) = _
    rw [Ideal.annihilator_quotient]
  · intro i hi
    apply ext_vanishing_of_supportDim_le (ModuleCat.of R M) rs hm hr d (R ⧸ p) _ i
      (by omega)
    rwa [Module.supportDim_quotient_eq_ringKrullDim]

/-- The regular-sequence definition of depth obeys the localization inequality.
The localized module is not assumed to be graded, free, or Cohen–Macaulay. -/
lemma localDepth_le_localized_add
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (hdim : ringKrullDim (R ⧸ p) ≤ d)
    (S N : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]
    [IsLocalRing S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Nontrivial N] [Module.Finite S N]
    (f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f] :
    localDepth R M ≤ localDepth S N + d := by
  apply sSup_le
  rintro a ⟨rs, hm, hr, rfl⟩
  obtain ⟨ts, hlen, hp, ht⟩ := exists_regular_in_prime M rs hm hr p d hdim
  have hreg := ht.toIsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem S p f hp
  have hmem : ∀ x ∈ ts.map (algebraMap R S), x ∈ maximalIdeal S := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mpr (hp r hr)
  have hle : ((ts.map (algebraMap R S)).length : ℕ∞) ≤ localDepth S N :=
    le_sSup ⟨ts.map (algebraMap R S), hmem, hreg, rfl⟩
  have hnat : rs.length ≤ ts.length + d := by omega
  calc (rs.length : ℕ∞) ≤ ts.length + d := by exact_mod_cast hnat
       _ ≤ localDepth S N + d := add_le_add (by simpa using hle) le_rfl

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- A chain through `p` is obtained by concatenating chains below and above it.
This is the dimension budget needed to pass full depth to a localization. -/
lemma localization_quotient_dim_le (p : Ideal R) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] :
    ringKrullDim S + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  have : Nonempty (PrimeSpectrum R) := ⟨q⟩
  have hdim : ringKrullDim (R ⧸ p) = (Order.coheight q : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, hdim]
  have hh : p.height = Order.height q := q.height_eq_orderHeight
  rw [hh, ← WithBot.coe_add, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum R => Order.height a + Order.coheight a) q

/-- Maximal depth, expressed using the regular-sequence convention,
localizes at every point of the module's support. No equidimensionality or
catenarity is assumed, and the module is completely arbitrary (not graded). -/
lemma localized_full_depth
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdepth : ringKrullDim R ≤ (localDepth R M : WithBot ℕ∞))
    (p : Ideal R) [p.IsPrime]
    (S N : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]
    [IsLocalRing S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Nontrivial N] [Module.Finite S N]
    (f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f] :
    ringKrullDim S ≤ (localDepth S N : WithBot ℕ∞) := by
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R ⧸ p))
  have hatop : a ≠ ⊤ := by
    intro h
    exact ringKrullDim_ne_top (R := R ⧸ p) (by rw [← ha, h]; rfl)
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hatop
  have hdim : ringKrullDim (R ⧸ p) = d := ha.symm
  have hleft := localization_quotient_dim_le p S
  rw [hdim] at hleft
  have hright := localDepth_le_localized_add M p d hdim.le S N f
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := d)).mp
  exact hleft.trans (hdepth.trans (by exact_mod_cast hright))

end LocalizationDepth
end SmallCM


end


/-! Flat base change of the honest evaluation map, needed for reflexivity
of the arbitrary depth-three module in the manuscript, lines 315–346. -/
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace CMBidualBaseChange
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.Flat R S]
  [IsNoetherianRing R] [Module.Finite R M]

def dualIso : S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) := by
  letI := Module.finitePresentation_of_finite R M
  exact (Module.FinitePresentation.isBaseChange_map R M R S).equiv.trans
    ((AlgebraTensorModule.rid R S S).congrRight)

lemma dualIso_tmul (s : S) (f : Module.Dual R M) (t : S) (m : M) :
    dualIso R S M (s ⊗ₜ[R] f) (t ⊗ₜ[R] m) = s * (algebraMap R S (f m) * t) := by
  simp only [dualIso, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  change s * ((f m) • t) = _
  rw [Algebra.smul_def]

def bidualIso : S ⊗[R] Module.Dual R (Module.Dual R M) ≃ₗ[S]
    Module.Dual S (Module.Dual S (S ⊗[R] M)) :=
  (dualIso R S (Module.Dual R M)).trans (Module.Dual.congr (dualIso R S M))

lemma bidualIso_eval (s : S) (m : M) :
    bidualIso R S M (s ⊗ₜ[R] Module.Dual.eval R M m) =
      Module.Dual.eval S (S ⊗[R] M) (s ⊗ₜ[R] m) := by
  apply LinearMap.ext
  intro f
  obtain ⟨x, rfl⟩ := (dualIso R S M).surjective f
  induction x using TensorProduct.inductionOn with
  | tmul t g =>
    simp [bidualIso, Module.Dual.congr, dualIso_tmul, mul_comm, mul_left_comm]
  | add x y hx hy => simp_all

lemma eval_baseChange :
    (bidualIso R S M).toLinearMap.comp ((Module.Dual.eval R M).baseChange S) =
      Module.Dual.eval S (S ⊗[R] M) := by
  apply AlgebraTensorModule.ext
  intro s m
  exact bidualIso_eval R S M s m

lemma surjective_eval_baseChange [Module.IsReflexive S (S ⊗[R] M)] :
    Function.Surjective ((Module.Dual.eval R M).baseChange S) := by
  have h := (Module.bijective_dual_eval S (S ⊗[R] M)).2
  rw [← eval_baseChange R S M] at h
  intro y
  obtain ⟨x, hx⟩ := h (bidualIso R S M y)
  exact ⟨x, (bidualIso R S M).injective hx⟩
end CMBidualBaseChange

end


/-! The codimension-two budget for the evaluation cokernel of a full-depth
module over the literal normal three-dimensional source ring. -/
noncomputable section
namespace CMCodimension
variable {R : Type*} [CommRing R]

lemma coheight_le_one (hdim : ringKrullDim R = 3) (p : PrimeSpectrum R)
    (hp : ¬ p.asIdeal.height ≤ 1) : Order.coheight p ≤ 1 := by
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  have hs : Order.height p + Order.coheight p ≤ (3 : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    calc (↑(Order.height p + Order.coheight p) : WithBot ℕ∞) ≤ ringKrullDim R := by
           rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty,
             WithBot.coe_le_coe]
           exact le_iSup (fun q : PrimeSpectrum R => Order.height q + Order.coheight q) p
         _ = 3 := hdim
  rw [p.height_eq_orderHeight] at hp
  have aux : ∀ a b : ℕ∞, ¬ a ≤ 1 → a + b ≤ 3 → b ≤ 1 := by
    intro a b ha hab
    enat_to_nat <;> simp_all
    omega
  exact aux _ _ hp hs

lemma supportDim_le_one (N : Type*) [AddCommGroup N] [Module R N]
    (hdim : ringKrullDim R = 3)
    (hzero : ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 → p ∉ Module.support R N) :
    Module.supportDim R N ≤ 1 := by
  rw [Module.supportDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun p => ?_
  have hp : ¬ p.val.asIdeal.height ≤ 1 := fun h => hzero p.val h p.property
  have h := (Order.coheight_le_coheight_apply_of_strictMono
    (fun q : Module.support R N => q.val) (fun _ _ h => h) p).trans
    (coheight_le_one hdim p.val hp)
  exact WithBot.coe_le_coe.mpr h

lemma atPrime_pid [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : PrimeSpectrum R) (hp : p.asIdeal.height ≤ 1) :
    IsPrincipalIdealRing (Localization.AtPrime p.asIdeal) := by
  let S := Localization.AtPrime p.asIdeal
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing p.asIdeal.primeCompl S
    inferInstance
  let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  let : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
    exact WithBot.coe_le_coe.mpr hp)
  let : Ring.DimensionLEOne S := ⟨fun {_} h hprime => hprime.isMaximal_of_ne_bot h⟩
  let : IsDedekindDomain S := { toIsDomain := inferInstance }
  infer_instance
end CMCodimension


/-! The actual evaluation cokernel, not a module introduced as a hypothesis.
Its support has dimension at most one over a normal three-dimensional ring. -/
open scoped TensorProduct
open TensorProduct
namespace CMCokernel
variable {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M]

lemma eval_injective : Function.Injective (Module.Dual.eval R M) := by
  let := Module.finitePresentation_of_finite R M
  intro x y h
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨f, hf⟩ := FiniteDomainDual.exists_dual_ne_zero (R := R) hne
  apply hf
  rw [map_sub]
  apply sub_eq_zero.mpr
  exact congrArg (fun g : Module.Dual R (Module.Dual R M) => g f) h

abbrev cokernel (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  Module.Dual R (Module.Dual R M) ⧸ (Module.Dual.eval R M).range

omit [IsDomain R] [IsNoetherianRing R] [Module.Finite R M] [Module.IsTorsionFree R M] in
lemma eval_exact : Function.Exact (Module.Dual.eval R M)
    (Module.Dual.eval R M).range.mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ]

lemma notMem_support [IsIntegrallyClosed R] (p : PrimeSpectrum R)
    (hp : p.asIdeal.height ≤ 1) : p ∉ Module.support R (cokernel R M) := by
  let S := Localization.AtPrime p.asIdeal
  let : IsPrincipalIdealRing S := CMCodimension.atPrime_pid p hp
  let : Module.IsTorsionFree S (S ⊗[R] M) := IsLocalizedModule.isTorsionFree
    (TensorProduct.mk R S M 1) p.asIdeal.primeCompl
  let : Module.Free S (S ⊗[R] M) := inferInstance
  have heval : Function.Surjective ((Module.Dual.eval R M).baseChange S) :=
    CMBidualBaseChange.surjective_eval_baseChange R S M
  let q := (Module.Dual.eval R M).range.mkQ
  have hq : Function.Surjective (q.lTensor S) :=
    LinearMap.lTensor_surjective S (Submodule.mkQ_surjective _)
  have hex := lTensor_exact S (eval_exact (R := R) (M := M))
    (Submodule.mkQ_surjective (Module.Dual.eval R M).range)
  let : Subsingleton (S ⊗[R] cokernel R M) := by
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨x, rfl⟩ := hq z
    obtain ⟨y, hy⟩ := heval x
    rw [← hy]
    exact LinearMap.congr_fun hex.linearMap_comp_eq_zero y
  apply Module.notMem_support_iff.mpr
  exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (cokernel R M)).injective.subsingleton

lemma supportDim_le_one [IsIntegrallyClosed R] (hdim : ringKrullDim R = 3) :
    Module.supportDim R (cokernel R M) ≤ 1 :=
  CMCodimension.supportDim_le_one (cokernel R M) hdim (notMem_support (R := R) (M := M))
end CMCokernel

end


/-! Required comparison in the manuscript, lines 331–346. A finite full-depth module
on the exact normal dimension-three ring is reflexive, regardless of a
separate proof that the punctured spectrum is regular. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open RingTheory.Sequence
namespace CMReflexivity
universe u
variable {R M : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M]

lemma eval_surjective_of_regular_three (hdim : ringKrullDim R = 3)
    (rs : List R) (hm : ∀ a ∈ rs, a ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : rs.length = 3) :
    Function.Surjective (Module.Dual.eval R M) := by
  let N := Module.Dual R (Module.Dual R M)
  let C := CMCokernel.cokernel R M
  let f := Module.Dual.eval R M
  let q := f.range.mkQ
  let S := ModuleCat.shortComplexOfCompEqZero f q
    (CMCokernel.eval_exact (R := R) (M := M)).linearMap_comp_eq_zero
  have hs : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (CMCokernel.eval_exact (R := R) (M := M)) CMCokernel.eval_injective
    (Submodule.mkQ_surjective _)
  let : Subsingleton (Ext (ModuleCat.of R C) (ModuleCat.of R M) 1) :=
    SmallCM.LocalizationDepth.ext_vanishing_of_supportDim_le (ModuleCat.of R M) rs
      hm hreg 1 C (CMCokernel.supportDim_le_one hdim) 1 (by omega)
  obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hs (ModuleCat.of R M)
    (Ext.mk₀ (𝟙 (ModuleCat.of R M))) (show 1 + 0 = 1 from rfl)
    (Subsingleton.elim _ _)
  obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective S.X₂ (ModuleCat.of R M)).2 e
  rw [Ext.mk₀_comp_mk₀] at he
  have hret : S.f ≫ r = 𝟙 (ModuleCat.of R M) := (Ext.mk₀_bijective _ _).1 he
  have hret_apply (m : M) : r.hom (f m) = m :=
    congrArg (fun g : ModuleCat.of R M ⟶ ModuleCat.of R M => g.hom m) hret
  let p : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have hz := (Module.notMem_support_iff').mp
    (CMCokernel.notMem_support (R := R) (M := M) p (by simp [p]))
  intro x
  obtain ⟨a, ha, hax⟩ := hz (q x)
  have ha0 : a ≠ 0 := by simpa [p] using ha
  have hq : q (a • x) = 0 := by rw [map_smul]; exact hax
  have hmem : a • x ∈ f.range := (Submodule.Quotient.mk_eq_zero f.range).mp hq
  obtain ⟨m, hm⟩ := hmem
  have hm' : m = a • r.hom x := by
    simpa only [hret_apply, map_smul] using congrArg r.hom hm
  refine ⟨r.hom x, ?_⟩
  apply Module.IsTorsionFree.isSMulRegular (M := N) (isRegular_iff_ne_zero.mpr ha0)
  change a • f (r.hom x) = a • x
  rw [← map_smul, ← hm']
  exact hm

lemma reflexive_of_regular_three (hdim : ringKrullDim R = 3)
    (rs : List R) (hm : ∀ a ∈ rs, a ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsRegular M rs) (hlen : rs.length = 3) : Module.IsReflexive R M :=
  ⟨CMCokernel.eval_injective, eval_surjective_of_regular_three hdim rs hm hreg hlen⟩
end CMReflexivity

end


/-! The literal source double dual agrees with a reflexive input on any
open subspace of its affine base. This does not assume local freeness. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace CMReflexiveSheaf
variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  (M : ModuleCat R) [Module.Finite R M] [Module.IsReflexive R M]

def identityEIso : CoherentModelActual.E (Spec.map (𝟙 R)) M ≅ tilde M := by
  let e : CoherentModelActual.affineModule (𝟙 R) M ≃ₗ[R] M :=
    ((ModuleCat.extendScalarsId R).app M).toLinearEquiv
  let d : Module.Dual R (Module.Dual R (CoherentModelActual.affineModule (𝟙 R) M)) ≃ₗ[R] M :=
    (Module.Dual.congr (Module.Dual.congr e)).trans (Module.evalEquiv R M).symm
  exact CoherentModelActual.affineEIso (𝟙 R) M ≪≫
    (tilde.functor R).mapIso d.toModuleIso

def openEIso {U : Scheme.{0}} (j : U ⟶ Spec R) [IsOpenImmersion j] :
    CoherentModelActual.E j M ≅ (pullback j).obj (tilde M) :=
  (CoherentModelActual.openPullbackEIsoOfComp j (Spec.map (𝟙 R)) j (by simp) M).symm ≪≫
    (pullback j).mapIso (identityEIso M)
omit [IsNoetherianRing R] in
theorem openImmersion_over_open {W : Scheme.{0}} (p : W ⟶ Spec R)
    (U : (Spec R).Opens) [IsIso (p ∣_ U)] :
    IsOpenImmersion ((p ⁻¹ᵁ U).ι ≫ p) := by
  rw [← morphismRestrict_ι p U]
  infer_instance

def punctureEIso {W : Scheme.{0}} (p : W ⟶ Spec R)
    (U : (Spec R).Opens) [IsIso (p ∣_ U)] :
    (pullback (p ⁻¹ᵁ U).ι).obj (CoherentModelActual.E p M) ≅
      (pullback (p ∣_ U)).obj ((pullback U.ι).obj (tilde M)) := by
  letI := openImmersion_over_open p U
  exact CoherentModelActual.openPullbackEIso (p ⁻¹ᵁ U).ι p M ≪≫
    openEIso M ((p ⁻¹ᵁ U).ι ≫ p) ≪≫
    (pullbackCongr (morphismRestrict_ι p U).symm).app (tilde M) ≪≫
    (pullbackComp (p ∣_ U) U.ι).symm.app (tilde M)
end CMReflexiveSheaf

end

end OAI
