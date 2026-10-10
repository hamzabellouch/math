import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.SymbolicPowers
import OAI.Algebra.AlgebraicObstruction.ArcDetection

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries.WithPiTopology
variable {R σ τ : Type*} [CommRing R] [Fintype σ]

lemma substitution_pderiv_polynomial (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (j : τ) (p : MvPolynomial σ R) :
    pderiv (R := R) j (subst a (p : MvPowerSeries σ R)) =
      ∑ i, subst a (pderiv (R := R) i (p : MvPowerSeries σ R)) * pderiv (R := R) j (a i) := by
  classical
  have hz : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← substAlgHom_apply (R := R) ha, map_zero]
  have ho : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← substAlgHom_apply (R := R) ha, map_one]
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.coe_C, pderiv_C, subst_C, hz, zero_mul,
      Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, subst_add ha, add_mul, Finset.sum_add_distrib, hp, hq]
  | mul_X p k hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha,
      Derivation.leibniz, smul_eq_mul, subst_add ha, hp, add_mul,
      Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    · simp [pderiv_X, Pi.single_apply, apply_ite, hz, ho]
    · simp only [mul_assoc]

omit [Fintype σ] in
lemma continuous_pderiv [TopologicalSpace R] [IsTopologicalRing R] (i : σ) :
    Continuous (pderiv (R := R) i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  apply continuous_pi
  intro n
  change Continuous (fun f : MvPowerSeries σ R ↦ coeff n (pderiv (R := R) i f))
  simp only [coeff_pderiv]
  exact (continuous_coeff R _).mul continuous_const

lemma substitution_pderiv (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (j : τ) (f : MvPowerSeries σ R) :
    pderiv (R := R) j (subst a f) =
      ∑ i, subst a (pderiv (R := R) i f) * pderiv (R := R) j (a i) := by
  let : UniformSpace R := ⊥
  have h := denseRange_toMvPowerSeries (σ := σ) (R := R)
  have h1 : Continuous (fun f : MvPowerSeries σ R ↦ pderiv (R := R) j (subst a f)) :=
    (continuous_pderiv j).comp (continuous_subst ha)
  have h2 : Continuous (fun f : MvPowerSeries σ R ↦
      ∑ i, subst a (pderiv (R := R) i f) * pderiv (R := R) j (a i)) := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_subst ha).comp (continuous_pderiv i)).mul continuous_const
  exact congrFun (h.equalizer h1 h2 (funext (substitution_pderiv_polynomial a ha j))) f

omit [Fintype σ] in
lemma constantCoeff_subst_centered [Fintype σ] (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h := constantCoeff_subst_eq_zero ha ha0
    (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem primitive_constant_on_arc [IsAddTorsionFree R]
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (I : Ideal (MvPowerSeries σ R))
    (hI : I ≤ RingHom.ker (substAlgHom (R := R) ha).toRingHom)
    (f : MvPowerSeries σ R) (hgrad : ∀ i, pderiv (R := R) i f ∈ I) :
    subst a (f - C (constantCoeff f)) = 0 := by
  have hg (i : σ) : subst a (pderiv (R := R) i f) = 0 := by
    have h := hI (hgrad i)
    change substAlgHom (R := R) ha (pderiv (R := R) i f) = 0 at h
    simpa only [substAlgHom_apply] using h
  have he : subst a f = C (constantCoeff f) := by
    apply pderiv.ext
    · intro j
      rw [substitution_pderiv a ha j]
      simp only [hg, zero_mul, Finset.sum_const_zero, pderiv_C]
    · rw [constantCoeff_subst_centered a ha ha0, constantCoeff_C]
  rw [subst_sub ha, subst_C, he, sub_self]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc
open MvPowerSeries IsLocalRing
variable {K σ : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Fintype σ]

theorem radical_primitive_constant (I : Ideal (MvPowerSeries σ K))
    (hI : I.IsRadical) (P : MvPowerSeries σ K)
    (hgrad : ∀ i, pderiv (R := K) i P ∈ I) : P - C (constantCoeff P) ∈ I := by
  classical
  by_contra hnot
  have hIne : I ≠ ⊤ := by
    intro h
    apply hnot
    simp [h]
  let B := MvPowerSeries σ K
  let Q := B ⧸ I
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  have : IsAdicComplete (maximalIdeal Q) Q := local_quotient_complete I
  let q : B →ₐ[K] Q := Ideal.Quotient.mkₐ K I
  have hsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalHom q.toRingHom := IsLocalHom.of_surjective _ hsurj
  let b := P - C (constantCoeff P)
  have hqb : q b ≠ 0 := fun h ↦ hnot (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hbm : b ∈ maximalIdeal B := by
    rw [maximalIdeal_eq_variables,span_variables_eq_constant_kernel]
    change constantCoeff b = 0
    simp [b]
  obtain ⟨g,hglocal,hgb⟩ := reduced_detecting_arc (q b) hqb
    (map_nonunit q.toRingHom b hbm) (quotient_residue_surjective I residue_mps_surjective)
  have : IsLocalHom g.toRingHom := hglocal
  let f : B →ₐ[K] PowerSeries K := g.comp q
  have : IsLocalHom f.toRingHom := by
    change IsLocalHom (g.toRingHom.comp q.toRingHom)
    infer_instance
  let a : σ → MvPowerSeries Unit K := fun i ↦ f (X i)
  have ha0 (i : σ) : constantCoeff (a i) = 0 := by
    have hx : (X i : B) ∈ maximalIdeal B := by
      rw [maximalIdeal_eq_variables]
      exact Ideal.subset_span (Set.mem_range_self i)
    have hh := map_nonunit f.toRingHom (X i) hx
    rw [maximalIdeal_eq_variables,span_variables_eq_constant_kernel] at hh
    exact hh
  have ha : HasSubst a := ⟨fun i ↦ ha0 i ▸ IsNilpotent.zero,fun _ ↦ Set.toFinite _⟩
  let s : B →ₐ[K] PowerSeries K := substAlgHom (R := K) ha
  have : IsLocalHom s.toRingHom := ⟨by
    intro x hx
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    have hh := MvPowerSeries.isUnit_iff_constantCoeff.mp hx
    change IsUnit (constantCoeff (substAlgHom (R := K) ha x)) at hh
    rw [substAlgHom_apply] at hh
    rw [constantCoeff_subst_centered a ha ha0] at hh
    exact hh⟩
  have hfs : f = s := local_mps_hom_ext f s (fun i ↦ by
    change a i = substAlgHom (R := K) ha (X i)
    rw [substAlgHom_apply,subst_X ha])
  have hkill : I ≤ RingHom.ker s.toRingHom := by
    intro x hx
    change s x = 0
    rw [← hfs]
    change g (q x) = 0
    rw [show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx,map_zero]
  have hconst := primitive_constant_on_arc a ha ha0 I hkill P hgrad
  apply hgb
  change f b = 0
  rw [hfs]
  change substAlgHom (R := K) ha b = 0
  rw [substAlgHom_apply]
  exact hconst

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.FormalArc

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open BoundaryOnly.FormalObstruction.AlgebraicReplacement MvPowerSeries
variable {K α : Type} [Field K] [CharZero K] [IsAlgClosed K] [Finite α]

noncomputable instance chartCoeffAlgebra (E : AffineEtaleChart K α) : Algebra K E.S :=
  Algebra.compHom E.S (algebraMap K (MvPolynomial α K))
instance chartCoeffTower (E : AffineEtaleChart K α) : IsScalarTower K (MvPolynomial α K) E.S :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable def pointAlgHom (E : AffineEtaleChart K α) : E.S →ₐ[K] K :=
  { ((constantCoeff : MvPowerSeries α K →+* K).comp E.expansion.toRingHom) with
    commutes' := fun k ↦ by
      change constantCoeff (E.expansion (algebraMap (MvPolynomial α K) E.S (MvPolynomial.C k))) = k
      rw [E.expansion.commutes]
      simp [MvPowerSeries.algebraMap_apply'] }

theorem radical_extended (E : AffineEtaleChart K α) (I : Ideal E.LocalRing)
    (hI : I.IsRadical) (hIne : I ≠ ⊤) :
    (I.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))).IsRadical := by
  have : Algebra.FiniteType K E.S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial α K)) inferInstance
  have : IsLocalization.AtPrime E.LocalRing (RingHom.ker E.pointAlgHom.toRingHom) := by
    change IsLocalization.AtPrime E.LocalRing E.point
    infer_instance
  exact AnalyticReducedness.radical_local_completion E.pointAlgHom E.LocalRing I hI hIne

theorem primitive_constant_reduction (E : AffineEtaleChart K α) (L : Ideal E.LocalRing)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (hgrad : ∀ i : α, E.completionDeriv i b ∈ L.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))) :
    ∃ a₀ : E.LocalRing ⧸ L.radical,
      TaylorTarget.quotientCoefficient
        (S := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) L.radical a₀ =
      Ideal.Quotient.mk (L.radical.map (algebraMap E.LocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))) b := by
  classical
  let := Fintype.ofFinite α
  let B := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing
  let I := L.radical
  let J := I.map (algebraMap E.LocalRing B)
  by_cases hI : I = ⊤
  · refine ⟨0,?_⟩
    have hJ : J = ⊤ := by
      change I.map (algebraMap E.LocalRing B) = ⊤
      rw [hI,Ideal.map_top]
    change TaylorTarget.quotientCoefficient (S := B) I 0 = Ideal.Quotient.mk J b
    rw [map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (show b ∈ J by rw [hJ]; trivial)).symm
  have hJ : J.IsRadical := E.radical_extended I L.radical_isRadical hI
  let H := J.map E.completionEquiv.toRingHom
  have hH : H.IsRadical := by
    change (J.map (E.completionEquiv : B →+* MvPowerSeries α K)).IsRadical
    rw [Ideal.map_comap_of_equiv]
    exact hJ.comap _
  have hg : ∀ i, pderiv (R := K) i (E.completionEquiv b) ∈ H := by
    intro i
    have hi := Ideal.mem_map_of_mem E.completionEquiv.toRingHom
      ((Ideal.map_mono (show L ≤ I from Ideal.le_radical)) (hgrad i))
    change E.completionEquiv (E.completionEquiv.symm (pderiv (R := K) i (E.completionEquiv b))) ∈ H at hi
    rwa [RingEquiv.apply_symm_apply] at hi
  have hc := FormalArc.radical_primitive_constant H hH (E.completionEquiv b) hg
  let k := constantCoeff (E.completionEquiv b)
  let a : E.LocalRing := algebraMap K E.LocalRing k
  have ha : E.completionEquiv (AdicCompletion.of _ _ a) = C k := by
    rw [E.completionEquiv_of]
    change E.localExpansion (algebraMap (MvPolynomial α K) E.LocalRing (MvPolynomial.C k)) = _
    rw [E.localExpansion.commutes]
    simp [MvPowerSeries.algebraMap_apply']
  have hb : b - AdicCompletion.of _ _ a ∈ J := by
    apply (Ideal.apply_mem_of_equiv_iff (f := E.completionEquiv) (I := J)).mp
    change E.completionEquiv (b - AdicCompletion.of _ _ a) ∈ H
    rw [map_sub,ha]
    exact hc
  refine ⟨Ideal.Quotient.mk I a,?_⟩
  change Ideal.Quotient.mk J (AdicCompletion.of _ _ a) = Ideal.Quotient.mk J b
  exact (Ideal.Quotient.eq.mpr hb).symm

theorem primitive_approximation (E : AffineEtaleChart K α) (L : Ideal E.LocalRing)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (hgrad : ∀ i : α, E.completionDeriv i b ∈ L.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)))
    (hjets : ∀ i : α, ∀ q : ℕ, 1 ≤ q → ∃ a : E.LocalRing,
      E.completionDeriv i b - AdicCompletion.of _ _ a ∈
        (L.map (algebraMap E.LocalRing
          (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)))^q)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : E.LocalRing, b - AdicCompletion.of _ _ a ∈
      (L^m).map (algebraMap E.LocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)) :=
  E.primitive_approximation_from_constant_reduction L b
    (E.primitive_constant_reduction L b hgrad) hjets m hm

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
