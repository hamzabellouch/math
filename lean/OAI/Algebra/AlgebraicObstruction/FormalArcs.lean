import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.AnalyticReducedness

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

open IsLocalRing

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

section Principal
variable [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

theorem complete_principal_powerSeries (π : R)
    (hπpow : ∀ n : ℕ, π^n ≠ 0)
    (hmπ : maximalIdeal R = Ideal.span {π})
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal R)).comp (algebraMap K R))) :
    ∃ e : PowerSeries K ≃ₐ[K] R, e PowerSeries.X = π := by
  classical
  let : WithIdeal K := ⟨⊥⟩
  let : WithIdeal R := ⟨maximalIdeal R⟩
  have hadic : IsAdic (maximalIdeal R) := rfl
  have hcomplete := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (maximalIdeal R) R)
  let : CompleteSpace R := hcomplete.1
  let : T2Space R := hcomplete.2
  have hmap : Continuous (algebraMap K R) :=
    (WithIdeal.uniformContinuous_of_map_le (f := algebraMap K R) (by
      change (⊥ : Ideal K).map (algebraMap K R) ≤ maximalIdeal R
      rw [Ideal.map_bot]
      exact bot_le)).continuous
  have hπeval : PowerSeries.HasEval π :=
    WithIdeal.isTopologicallyNilpotent_of_mem (by
      change π ∈ maximalIdeal R
      rw [hmπ]
      exact Ideal.subset_span (by simp))
  let f : PowerSeries K →+* R := PowerSeries.eval₂Hom hmap hπeval
  have hfX : f PowerSeries.X = π := by
    simp only [f,PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_X]
  have hfC (c : K) : f (PowerSeries.C c) = algebraMap K R c := by
    simp only [f,PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_C]
  have hfI : (Ideal.span {PowerSeries.X}).map f = maximalIdeal R := by
    rw [Ideal.map_span,Set.image_singleton,hfX,hmπ]
  have : IsHausdorff ((Ideal.span {PowerSeries.X}).map f) R := by
    rw [hfI]
    infer_instance
  have hsurj : Function.Surjective f := by
    apply surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) f
    rw [hfI]
    intro z
    obtain ⟨c,hc⟩ := hres z
    refine ⟨PowerSeries.C c,?_⟩
    simpa only [RingHom.comp_apply,hfC] using hc
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro g hg
    by_contra hg0
    have hfactor := PowerSeries.X_pow_order_mul_divXPowOrder (f := g)
    have hunit := (PowerSeries.isUnit_divided_by_X_pow_order hg0).map f
    have heq := congrArg f hfactor
    rw [map_mul,map_pow,hfX,hg] at heq
    apply hπpow g.order.toNat
    exact hunit.mul_left_cancel (by simpa only [mul_comm,mul_zero,zero_mul] using heq)
  let e : PowerSeries K ≃+* R := RingEquiv.ofBijective f ⟨hinj,hsurj⟩
  exact ⟨{ e with commutes' := fun c ↦ hfC c },hfX⟩

end Principal

variable [IsDomain R] [IsDiscreteValuationRing R]

theorem completeDVR_powerSeries [IsAdicComplete (maximalIdeal R) R]
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal R)).comp (algebraMap K R))) :
    Nonempty (PowerSeries K ≃ₐ[K] R) := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e,he⟩ := complete_principal_powerSeries π
    (fun n ↦ pow_ne_zero n hπ.ne_zero) hπ.maximalIdeal_eq hres
  exact ⟨e⟩

theorem DVR_completion_powerSeries
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal R)).comp (algebraMap K R))) :
    Nonempty (PowerSeries K ≃ₐ[K] AdicCompletion (maximalIdeal R) R) := by
  classical
  let B := AdicCompletion (maximalIdeal R) R
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R B) :=
    AdicCompletion.of_injective (maximalIdeal R) R
  have hm : maximalIdeal B = Ideal.span {algebraMap R B π} := by
    exact (AdicCompletion.maximalIdeal_eq_map).trans
      ((congrArg (Ideal.map (algebraMap R B)) hπ.maximalIdeal_eq).trans
        (by rw [Ideal.map_span,Set.image_singleton]))
  have hp (n : ℕ) : (algebraMap R B π)^n ≠ 0 := by
    rw [← map_pow]
    exact fun h ↦ pow_ne_zero n hπ.ne_zero (hinj (h.trans (map_zero _).symm))
  have hr : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal B)).comp (algebraMap K B)) := by
    intro z
    obtain ⟨w,hw⟩ := (AdicCompletion.residueField_map_bijective R).2 z
    obtain ⟨c,hc⟩ := hres w
    refine ⟨c,?_⟩
    change residue R (algebraMap K R c) = w at hc
    change residue B (algebraMap K B c) = z
    have hx := IsLocalRing.ResidueField.map_residue (algebraMap R B)
      (algebraMap K R c)
    rw [hc] at hx
    rw [hw] at hx
    rw [← IsScalarTower.algebraMap_apply K R B c] at hx
    exact hx.symm
  obtain ⟨e,he⟩ := complete_principal_powerSeries (algebraMap R B π) hp hm hr
  exact ⟨e⟩

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
variable {K S C : Type*} [Field K] [IsAlgClosed K]
  [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra K S]
  [CommRing C] [IsDedekindDomain C]
  [Algebra S C] [Algebra K C] [IsScalarTower K S C]
  [Module.Finite S C] [Module.IsTorsionFree S C]

include C in

theorem finite_normalization_arc
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S)))
    (b : S) (hb : b ≠ 0) (hbm : b ∈ maximalIdeal S) :
    ∃ f : S →ₐ[K] PowerSeries K,
      Function.Injective f ∧ IsLocalHom f.toRingHom := by
  classical
  obtain ⟨p,hp,hpm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := C) (maximalIdeal S) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective S C)]
      exact bot_le)
  change p.comap (algebraMap S C) = maximalIdeal S at hpm
  let : p.IsMaximal := hp
  have hp0 : p ≠ ⊥ := by
    intro hz
    have hx : algebraMap S C b ∈ p := by rw [← Ideal.mem_comap,hpm]; exact hbm
    rw [hz,Ideal.mem_bot] at hx
    exact hb ((FaithfulSMul.algebraMap_injective S C) (hx.trans (map_zero _).symm))
  let D := Localization.AtPrime p
  let : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hp0 D
  have : IsLocalHom (algebraMap S D) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap S D)).out 1 5).mpr
    change (maximalIdeal D).comap (algebraMap S D) = maximalIdeal S
    have hd : (maximalIdeal D).comap (algebraMap C D) = p :=
      IsLocalization.AtPrime.under_maximalIdeal D p
    rw [IsScalarTower.algebraMap_eq S C D,← Ideal.comap_comap,hd,hpm]
  have : Module.Finite S p.ResidueField := Module.Finite.trans C p.ResidueField
  have : Module.Finite K (ResidueField S) :=
    Module.Finite.of_surjective (Algebra.linearMap K (ResidueField S)) hres
  have : IsScalarTower K (ResidueField S) p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap K p.ResidueField x =
        algebraMap S p.ResidueField (algebraMap K S x)
      exact IsScalarTower.algebraMap_apply K S p.ResidueField x
  have : Module.Finite (ResidueField S) p.ResidueField :=
    Module.Finite.of_restrictScalars_finite S (ResidueField S) p.ResidueField
  have : Module.Finite K p.ResidueField :=
    Module.Finite.trans (ResidueField S) p.ResidueField
  have hr : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal D)).comp (algebraMap K D)) := by
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
      (K := p.ResidueField)).2
  obtain ⟨e⟩ := DVR_completion_powerSeries (R := D) hr
  let g : S →ₐ[K] AdicCompletion (maximalIdeal D) D :=
    (IsScalarTower.toAlgHom K D _).comp (IsScalarTower.toAlgHom K S D)
  let f : S →ₐ[K] PowerSeries K := e.symm.toAlgHom.comp g
  have hdinj : Function.Injective (algebraMap C D) :=
    IsLocalization.injective D p.primeCompl_le_nonZeroDivisors
  have hsinj : Function.Injective (algebraMap S D) := by
    rw [IsScalarTower.algebraMap_eq S C D]
    exact hdinj.comp (FaithfulSMul.algebraMap_injective S C)
  have hbinj : Function.Injective (algebraMap D (AdicCompletion (maximalIdeal D) D)) :=
    AdicCompletion.of_injective (maximalIdeal D) D
  refine ⟨f,e.symm.injective.comp (hbinj.comp hsinj),?_⟩
  change IsLocalHom (e.symm.toRingHom.comp
    ((algebraMap D (AdicCompletion (maximalIdeal D) D)).comp (algebraMap S D)))
  have : IsLocalHom e.symm.toRingHom := isLocalHom_toRingHom e.symm
  exact RingHom.isLocalHom_comp _ _

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
variable {K S : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra K S]
  [Algebra (PowerSeries K) S] [IsScalarTower K (PowerSeries K) S]
  [Module.Finite (PowerSeries K) S] [Module.IsTorsionFree (PowerSeries K) S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem finite_powerSeries_curve_arc
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S)))
    (b : S) (hb : b ≠ 0) (hbm : b ∈ maximalIdeal S) :
    ∃ f : S →ₐ[K] PowerSeries K,
      Function.Injective f ∧ IsLocalHom f.toRingHom := by
  classical
  let A := PowerSeries K
  let L := FractionRing S
  let C := integralClosure A L
  have : Module.Finite (FractionRing A) L := inferInstance
  have : CharZero A := charZero_of_injective_ringHom (PowerSeries.C_injective (R := K))
  have : CharZero (FractionRing A) := inferInstance
  have : Algebra.IsSeparable (FractionRing A) L := inferInstance
  have : IsDedekindDomain C := inferInstance
  have : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) L C
  let j : S →ₐ[A] C := IsIntegralClosure.lift A C L
  let : Algebra S C := j.toRingHom.toAlgebra
  have : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq fun a ↦ (j.commutes a).symm
  have : IsScalarTower S C L := IsScalarTower.of_algebraMap_eq fun s ↦
    (IsIntegralClosure.algebraMap_lift A C L s).symm
  let : Algebra K C := ((algebraMap A C).comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K S C := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap A C (algebraMap K A k) = j (algebraMap K S k)
    rw [IsScalarTower.algebraMap_apply K A S,j.commutes]
  have : Module.Finite S C := Module.Finite.of_restrictScalars_finite A S C
  have hinj : Function.Injective (algebraMap S C) := by
    intro x y h
    apply IsFractionRing.injective S L
    rw [IsScalarTower.algebraMap_apply S C L x,
      IsScalarTower.algebraMap_apply S C L y,h]
  have : Module.IsTorsionFree S C :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  exact finite_normalization_arc (C := C) hres b hb hbm

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
open scoped Pointwise

private theorem mem_principal_smul_pi {A ι : Type*} [CommRing A]
    (a : A) (x : ι → A) :
    x ∈ (Ideal.span {a} : Ideal A) • (⊤ : Submodule A (ι → A)) ↔
      ∀ i, x i ∈ Ideal.span {a} := by
  simp only [Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y,rfl⟩ i
    exact ⟨y i,rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y,funext fun i ↦ (hy i).symm⟩

private theorem principal_pi_precomplete {A ι : Type*} [CommRing A]
    (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {a}) (ι → A) := by
  classical
  constructor
  intro f hf
  have hc (i : ι) : ∃ z : A, ∀ n,
      f n i ≡ z [SMOD ((Ideal.span {a})^n • (⊤ : Submodule A A))] := by
    apply IsPrecomplete.prec'
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem,Ideal.span_singleton_pow] at h
    have hi := (mem_principal_smul_pi (a^m) _).mp h i
    simpa only [SModEq.sub_mem,Ideal.span_singleton_pow,smul_eq_mul,Ideal.mul_top,
      Pi.sub_apply] using hi
  choose z hz using hc
  refine ⟨z,fun n ↦ ?_⟩
  rw [SModEq.sub_mem,Ideal.span_singleton_pow,mem_principal_smul_pi]
  intro i
  simpa only [SModEq.sub_mem,Ideal.span_singleton_pow,smul_eq_mul,Ideal.mul_top,
    Pi.sub_apply] using hz i n

variable {K S : Type*} [Field K] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra K S]

theorem finite_primary_quotient (I : Ideal S)
    (hI : I.radical = maximalIdeal S)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    Module.Finite K (S ⧸ I) := by
  have him : I ≤ maximalIdeal S := hI ▸ Ideal.le_radical
  let f : (S ⧸ I) →ₐ[K] ResidueField S := Ideal.Quotient.factorₐ K him
  have : Module.Finite K (ResidueField S) :=
    Module.Finite.of_surjective (Algebra.linearMap K (ResidueField S)) hres
  apply Module.finite_of_surjective_of_ker_le_nilradical f
    (Ideal.Quotient.factor_surjective him) ?_ (IsNoetherian.noetherian _)
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    intro hx
    have hxm : x ∈ maximalIdeal S := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [← hI] at hxm
    obtain ⟨n,hn⟩ := hxm
    apply mem_nilradical.mpr
    exact ⟨n,by
      change (Ideal.Quotient.mk I x)^n = 0
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hn⟩

theorem finite_over_parameter [Algebra (PowerSeries K) S]
    [IsScalarTower K (PowerSeries K) S]
    (b : S) (hb : b ∈ maximalIdeal S)
    (hfX : algebraMap (PowerSeries K) S PowerSeries.X = b)
    [Module.Finite K (S ⧸ Ideal.span {b})] :
    Module.Finite (PowerSeries K) S := by
  classical
  let A := PowerSeries K
  let I : Ideal A := Ideal.span {PowerSeries.X}
  let J : Ideal S := Ideal.span {b}
  have hm : I.map (algebraMap A S) = J := by
    rw [Ideal.map_span,Set.image_singleton,hfX]
  have hjm : J ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem (maximalIdeal S)).mpr hb
  have : IsHausdorff J S := IsHausdorff.of_isLocalRing J S
    (fun h ↦ (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hjm)))
  have : IsHausdorff I S := IsHausdorff.map_algebraMap_iff.mp (hm ▸ ‹IsHausdorff J S›)
  let B := Module.finBasis K (S ⧸ J)
  obtain ⟨v,hv⟩ := Classical.axiom_of_choice
    (fun i ↦ Ideal.Quotient.mk_surjective (B i))
  let l : (Fin (Module.finrank K (S ⧸ J)) → A) →ₗ[A] S :=
    Fintype.linearCombination A v
  have : IsPrecomplete I (Fin (Module.finrank K (S ⧸ J)) → A) :=
    principal_pi_precomplete PowerSeries.X
  have hl : Function.Surjective l := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    have heq : I • (⊤ : Submodule A S) = J.restrictScalars A := by
      rw [Ideal.smul_top_eq_map,hm]
    rw [heq]
    change Function.Surjective (fun c ↦ Ideal.Quotient.mk J (l c))
    intro z
    refine ⟨fun i ↦ algebraMap K A (B.repr z i),?_⟩
    change Ideal.Quotient.mk J (∑ i, algebraMap K A (B.repr z i) • v i) = z
    rw [map_sum]
    simp_rw [IsScalarTower.algebraMap_smul A]
    change (∑ i, (Ideal.Quotient.mkₐ K J) (B.repr z i • v i)) = z
    simp_rw [map_smul]
    change (∑ i, B.repr z i • Ideal.Quotient.mk J (v i)) = z
    simp_rw [hv]
    exact B.sum_repr z
  exact Module.Finite.of_surjective l hl

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open IsLocalRing
variable {K S : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
  [Algebra K S] [IsAdicComplete (maximalIdeal S) S]

theorem primary_parameter_arc (b : S) (hb : b ≠ 0)
    (hprimary : (Ideal.span {b}).radical = maximalIdeal S)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S)).comp (algebraMap K S))) :
    ∃ f : S →ₐ[K] PowerSeries K,
      Function.Injective f ∧ IsLocalHom f.toRingHom := by
  classical
  have hbm : b ∈ maximalIdeal S := by
    rw [← hprimary]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self b)
  let : WithIdeal K := ⟨⊥⟩
  let : WithIdeal S := ⟨maximalIdeal S⟩
  have hadic : IsAdic (maximalIdeal S) := rfl
  have hc := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (maximalIdeal S) S)
  let : CompleteSpace S := hc.1
  let : T2Space S := hc.2
  have hmap : Continuous (algebraMap K S) :=
    (WithIdeal.uniformContinuous_of_map_le (f := algebraMap K S) (by
      change (⊥ : Ideal K).map (algebraMap K S) ≤ maximalIdeal S
      rw [Ideal.map_bot]
      exact bot_le)).continuous
  have hbeval : PowerSeries.HasEval b :=
    WithIdeal.isTopologicallyNilpotent_of_mem hbm
  let g : PowerSeries K →+* S := PowerSeries.eval₂Hom hmap hbeval
  have hgX : g PowerSeries.X = b := by
    simp only [g,PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_X]
  have hgC (c : K) : g (PowerSeries.C c) = algebraMap K S c := by
    simp only [g,PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_C]
  have hinj : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro a ha
    by_contra ha0
    have hfactor := PowerSeries.X_pow_order_mul_divXPowOrder (f := a)
    have hunit := (PowerSeries.isUnit_divided_by_X_pow_order ha0).map g
    have heq := congrArg g hfactor
    rw [map_mul,map_pow,hgX,ha] at heq
    exact pow_ne_zero a.order.toNat hb
      (hunit.mul_left_cancel (by simpa only [mul_comm,mul_zero,zero_mul] using heq))
  let : Algebra (PowerSeries K) S := g.toAlgebra
  have : IsScalarTower K (PowerSeries K) S :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (hgC c).symm
  have : Module.IsTorsionFree (PowerSeries K) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.Finite K (S ⧸ Ideal.span {b}) :=
    finite_primary_quotient (Ideal.span {b}) hprimary hres
  have : Module.Finite (PowerSeries K) S := finite_over_parameter b hbm hgX
  exact finite_powerSeries_curve_arc hres b hb hbm

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

end

end OAI
