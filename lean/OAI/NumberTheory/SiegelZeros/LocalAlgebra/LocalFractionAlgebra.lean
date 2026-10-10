import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousDeformation

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
section
open scoped BigOperators DirectSum
open MvPolynomial
namespace WeightedTorusJets

open MvPolynomial

theorem generic_homogeneous_deformation_quotient_bound
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d : ℕ) :
    Module.Finite (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) ∧
      Module.finrank (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) ≤
        d ^ Fintype.card σ := by
  classical
  have h := Geometry.quotient_finrank_le_prod_of_homogeneous_image_le_rectangular
    (L := K)
    (Ideal.span (Set.range (fun i =>
      map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i))))
    (fun _ : σ => d) (fun n => by
      exact finrank_degreePiece_deformed_le_pure_powers f d n)
  simpa only [Finset.prod_const, Finset.card_univ] using h

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem exists_lift_of_mem_leadingFormIdeal {ι σ K : Type*} [Fintype ι] [CommRing K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (hf : ∀ i, (f i).totalDegree ≤ D)
    (p : MvPolynomial σ K) (n : ℕ) (hp : p.IsHomogeneous n)
    (hmem : p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i))) :
    ∃ q ∈ Ideal.span (Set.range f), q.totalDegree ≤ n ∧ homogeneousComponent n q = p := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ K)).mp hmem
  have ha : ∑ i, a i * homogeneousComponent D (f i) = p := by
    simpa only [smul_eq_mul] using ha
  by_cases hDn : D ≤ n
  · have hright (i : ι) : homogeneousComponent n (a i * homogeneousComponent D (f i)) =
        homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) := by
      rw [mul_comm (a i), GradedQuotient.homogeneousComponent_mul_of_le
        (homogeneousComponent_isHomogeneous D (f i)) hDn, mul_comm]
    have hleft (i : ι) : homogeneousComponent n (homogeneousComponent (n - D) (a i) * f i) =
        homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) := by
      rw [GradedQuotient.homogeneousComponent_mul_of_le
        (homogeneousComponent_isHomogeneous (n - D) (a i)) (Nat.sub_le n D),
        Nat.sub_sub_self hDn]
    have he : ∑ i, homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) = p := by
      simpa only [map_sum, hright, homogeneousComponent_eq_self hp] using
        congrArg (homogeneousComponent n) ha
    refine ⟨∑ i, homogeneousComponent (n - D) (a i) * f i, ?_, ?_, ?_⟩
    · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · exact totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans
        ((Nat.add_le_add (homogeneousComponent_isHomogeneous (n - D) (a i)).totalDegree_le
          (hf i)).trans_eq (Nat.sub_add_cancel hDn))
    · simpa only [map_sum, hleft] using he
  · have hz (i : ι) : homogeneousComponent n (a i * homogeneousComponent D (f i)) = 0 := by
      rw [mul_comm, GradedQuotient.homogeneousComponent_mul_of_lt
        (homogeneousComponent_isHomogeneous D (f i)) (Nat.lt_of_not_ge hDn)]
    have he : p = 0 := by
      have h := congrArg (homogeneousComponent n) ha
      simpa only [map_sum, hz, Finset.sum_const_zero, homogeneousComponent_eq_self hp] using h.symm
    exact ⟨0, Ideal.zero_mem _, by simp, by simp [he]⟩

theorem homogeneousComponent_mem_leadingFormIdeal {ι σ K : Type*} [CommRing K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (p : MvPolynomial σ K)
    (hp : p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i))) (n : ℕ) :
    homogeneousComponent n p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i)) := by
  let : GradedAlgebra (homogeneousSubmodule σ K) := MvPolynomial.gradedAlgebra
  apply homogeneousComponent_mem_of_mem _ hp n
  apply Ideal.homogeneous_span
  rintro g ⟨i, rfl⟩
  exact ⟨D, homogeneousComponent_isHomogeneous D (f i)⟩

theorem eq_zero_or_totalDegree_lt_of_homogeneousComponent_eq_zero {σ K : Type*} [CommRing K]
    (p : MvPolynomial σ K) (n : ℕ) (hp : p.totalDegree ≤ n)
    (hn : homogeneousComponent n p = 0) : p = 0 ∨ p.totalDegree < n := by
  classical
  by_cases hn0 : n = 0
  · left
    subst n
    have hhom : p.IsHomogeneous 0 :=
      (totalDegree_zero_iff_isHomogeneous σ).mp (Nat.eq_zero_of_le_zero hp)
    simpa only [homogeneousComponent_eq_self hhom] using hn
  · right
    rw [totalDegree, Finset.sup_lt_iff (Nat.pos_of_ne_zero hn0)]
    intro d hd
    have hdle : d.degree ≤ n := (le_totalDegree hd).trans hp
    apply lt_of_le_of_ne hdle
    intro he
    have hz := congrArg (fun q : MvPolynomial σ K => q.coeff d) hn
    have hdne := mem_support_iff.mp hd
    exact hdne (by simpa [coeff_homogeneousComponent, he] using hz)

theorem representatives_of_homogeneous_lifts {σ K : Type*} [CommRing K]
    (I J : Ideal (MvPolynomial σ K)) (S : Submodule K (MvPolynomial σ K))
    (hS : ∀ p ∈ S, ∀ n, homogeneousComponent n p ∈ S)
    (hJ : ∀ p ∈ J, ∀ n, homogeneousComponent n p ∈ J)
    (hlift : ∀ (p : MvPolynomial σ K) (n : ℕ), p.IsHomogeneous n → p ∈ J →
      ∃ q ∈ I, q.totalDegree ≤ n ∧ homogeneousComponent n q = p)
    (hrep : ∀ p : MvPolynomial σ K, ∃ s ∈ S, p - s ∈ J) :
    ∀ p : MvPolynomial σ K, ∃ s ∈ S, p - s ∈ I := by
  have H : ∀ n : ℕ, ∀ p : MvPolynomial σ K, p.totalDegree ≤ n →
      ∃ s ∈ S, p - s ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      obtain ⟨s, hs, hps⟩ := hrep (homogeneousComponent n p)
      let t := homogeneousComponent n s
      have htS : t ∈ S := hS s hs n
      have htHom : t.IsHomogeneous n := homogeneousComponent_isHomogeneous n s
      have hptHom : (homogeneousComponent n p - t).IsHomogeneous n :=
        (homogeneousComponent_isHomogeneous n p).sub htHom
      have hptJ : homogeneousComponent n p - t ∈ J := by
        simpa only [map_sub,
          homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous n p)] using hJ _ hps n
      obtain ⟨q, hqI, hqdeg, hqtop⟩ := hlift _ n hptHom hptJ
      let r := p - t - q
      have hrdeg : r.totalDegree ≤ n :=
        (totalDegree_sub _ _).trans (max_le
          ((totalDegree_sub _ _).trans (max_le hp htHom.totalDegree_le)) hqdeg)
      have hrtop : homogeneousComponent n r = 0 := by
        simp only [r, map_sub, homogeneousComponent_eq_self htHom, hqtop, sub_self]
      rcases eq_zero_or_totalDegree_lt_of_homogeneousComponent_eq_zero r n hrdeg hrtop with hr | hr
      · refine ⟨t, htS, ?_⟩
        have he : p - t = q := sub_eq_zero.mp hr
        rwa [he]
      · obtain ⟨u, huS, hruI⟩ := ih r.totalDegree hr r le_rfl
        refine ⟨t + u, S.add_mem htS huS, ?_⟩
        have he : p - (t + u) = (r - u) + q := by dsimp [r]; abel
        rw [he]
        exact I.add_mem hruI hqI
  intro p
  exact H p.totalDegree p le_rfl

end WeightedTorusJets.Geometry

open Module

namespace WeightedTorusJets

theorem exists_monomial_basis_quotient
    {K σ : Type*} [Field K] (J : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ J)] :
    ∃ m : Fin (finrank K (MvPolynomial σ K ⧸ J)) → (σ →₀ ℕ),
      LinearIndependent K (fun i => Ideal.Quotient.mk J (MvPolynomial.monomial (m i) 1)) ∧
      Submodule.span K (Set.range fun i =>
        Ideal.Quotient.mk J (MvPolynomial.monomial (m i) 1)) = ⊤ := by
  classical
  let v := fun m : σ →₀ ℕ => Ideal.Quotient.mk J (MvPolynomial.monomial m 1)
  let f := (Ideal.Quotient.mkₐ K J).toLinearMap
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    have h := congrArg (Submodule.map f) (MvPolynomial.basisMonomials σ K).span_eq
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective K J)] at h
    simpa [← Set.range_comp, MvPolynomial.coe_basisMonomials, Function.comp_def, f, v] using h
  obtain ⟨b, hb, hbspan, hblin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  choose m hm using hb
  have hdim : finrank K (Submodule.span K (Set.range v)) =
      finrank K (MvPolynomial σ K ⧸ J) := by rw [hspan, finrank_top]
  let e := finCongr hdim.symm
  have hrows : (fun i => v (m (e i))) = b ∘ e := by
    funext i
    exact hm (e i)
  refine ⟨m ∘ e, ?_, ?_⟩
  · change LinearIndependent K (fun i => v (m (e i)))
    rw [hrows]
    exact hblin.comp e e.injective
  · change Submodule.span K (Set.range fun i => v (m (e i))) = ⊤
    rw [hrows, e.surjective.range_comp, hbspan, hspan]

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem homogeneousComponent_mem_span_monomials {τ σ K : Type*} [CommRing K]
    (m : τ → (σ →₀ ℕ)) (p : MvPolynomial σ K)
    (hp : p ∈ Submodule.span K (Set.range fun i => monomial (m i) (1 : K))) (n : ℕ) :
    homogeneousComponent n p ∈ Submodule.span K (Set.range fun i => monomial (m i) (1 : K)) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial (1 : K) rfl)]
      split_ifs
      · exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add p q hp hq hp' hq' => simpa only [map_add] using Submodule.add_mem _ hp' hq'
  | smul c p hp hp' => simpa only [map_smul] using Submodule.smul_mem _ c hp'

theorem quotient_span_eq_top_iff_representatives {τ σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (v : τ → MvPolynomial σ K) :
    Submodule.span K (Set.range fun i => Ideal.Quotient.mk J (v i)) = ⊤ ↔
      ∀ p : MvPolynomial σ K,
        ∃ s ∈ Submodule.span K (Set.range v), p - s ∈ J := by
  let L := (Ideal.Quotient.mkₐ K J).toLinearMap
  have hmap : (Submodule.span K (Set.range v)).map L =
      Submodule.span K (Set.range fun i => Ideal.Quotient.mk J (v i)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hmap]
  constructor
  · intro h p
    have hp : L p ∈ (Submodule.span K (Set.range v)).map L := by rw [h]; exact Submodule.mem_top
    obtain ⟨s, hs, he⟩ := Submodule.mem_map.mp hp
    exact ⟨s, hs, Ideal.Quotient.eq.mp he.symm⟩
  · intro h
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, he⟩ := h p
    exact Submodule.mem_map.mpr ⟨s, hs, (Ideal.Quotient.eq.mpr he).symm⟩

theorem finite_and_finrank_le_leadingFormQuotient {ι σ K : Type*} [Fintype ι] [Field K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (hf : ∀ i, (f i).totalDegree ≤ D)
    [Module.Finite K (MvPolynomial σ K ⧸
      Ideal.span (Set.range fun i => homogeneousComponent D (f i)))] :
    Module.Finite K (MvPolynomial σ K ⧸ Ideal.span (Set.range f)) ∧
      Module.finrank K (MvPolynomial σ K ⧸ Ideal.span (Set.range f)) ≤
        Module.finrank K (MvPolynomial σ K ⧸
          Ideal.span (Set.range fun i => homogeneousComponent D (f i))) := by
  classical
  let J := Ideal.span (Set.range fun i => homogeneousComponent D (f i))
  obtain ⟨m, _, hmspan⟩ := WeightedTorusJets.exists_monomial_basis_quotient J
  have hrepJ := (quotient_span_eq_top_iff_representatives J
    (fun i => monomial (m i) (1 : K))).mp hmspan
  have hrepI := representatives_of_homogeneous_lifts (Ideal.span (Set.range f)) J
    (Submodule.span K (Set.range fun i => monomial (m i) (1 : K)))
    (homogeneousComponent_mem_span_monomials m)
    (homogeneousComponent_mem_leadingFormIdeal f D)
    (exists_lift_of_mem_leadingFormIdeal f D hf) hrepJ
  have hspanI := (quotient_span_eq_top_iff_representatives (Ideal.span (Set.range f))
    (fun i => monomial (m i) (1 : K))).mpr hrepI
  refine ⟨Module.Finite.of_fg_top ?_, ?_⟩
  · rw [← hspanI]
    exact Submodule.fg_span (Set.finite_range _)
  · simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top hspanI

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

theorem polynomialDeformation_totalDegree_le {σ R : Type*} [CommRing R]
    (f : σ → MvPolynomial σ R) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (i : σ) : (polynomialDeformation f d i).totalDegree ≤ d := by
  have hmap : (map Polynomial.C (f i)).totalDegree ≤ (f i).totalDegree :=
    Finset.sup_mono (support_map_subset _ _)
  unfold polynomialDeformation
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    simpa only [totalDegree_C, zero_add] using hmap.trans (hf i)
  · refine (totalDegree_mul _ _).trans ?_
    simpa only [totalDegree_C, zero_add] using
      (isHomogeneous_X_pow (R := Polynomial R) i d).totalDegree_le

theorem map_polynomialDeformation_totalDegree_le {σ R S : Type*}
    [CommRing R] [CommRing S] (φ : Polynomial R →+* S)
    (f : σ → MvPolynomial σ R) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (i : σ) : (map φ (polynomialDeformation f d i)).totalDegree ≤ d := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans
    (polynomialDeformation_totalDegree_le f d hf i)

end WeightedTorusJets

namespace WeightedTorusJets

open MvPolynomial

theorem generic_affine_deformation_quotient_bound
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d) :
    Module.Finite (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)))) ∧
      Module.finrank (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)))) ≤
        d ^ Fintype.card σ := by
  have htop (i : σ) :
      homogeneousComponent d
          (map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)) =
        map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i) := by
    rw [homogeneousDeformation, map_homogeneousComponent]
  have hIdeals := congrArg
    (fun g : σ → MvPolynomial σ (RatFunc K) => Ideal.span (Set.range g)) (funext htop)
  let e := (Ideal.quotientEquivAlgOfEq (RatFunc K) hIdeals).toLinearEquiv
  obtain ⟨hfinite, hbound⟩ := generic_homogeneous_deformation_quotient_bound f d
  let : Module.Finite (RatFunc K)
      (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
        map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) := hfinite
  let : Module.Finite (RatFunc K)
      (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
        homogeneousComponent d
          (map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i))))) :=
    Module.Finite.equiv e.symm
  have h := Geometry.finite_and_finrank_le_leadingFormQuotient
    (fun i => map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)) d
    (map_polynomialDeformation_totalDegree_le _ f d hf)
  exact ⟨h.1, h.2.trans (e.finrank_eq.trans_le hbound)⟩

end WeightedTorusJets

end


namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_polynomial_height (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsMaximal] : p.height = n := by
  induction n with
  | zero =>
    have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have h0 : p.height ≤ 0 := WithBot.coe_le_coe.mp (by simpa using h)
    exact le_antisymm h0 bot_le
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := p.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver q := ⟨rfl⟩
    have hq : q.height = n := ih q
    calc
      p.height = P.height := (e.height_map p).symm
      _ = q.height + 1 := Polynomial.height_eq_height_add_one q P
      _ = (n + 1 : ℕ) := by rw [hq]; simp

end WeightedTorusJets.Geometry



namespace WeightedTorusJets.Deformation

@[instance_reducible] noncomputable def localFractionAlgebra
    {R F : Type*} [CommRing R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) F :=
  (IsLocalization.lift (S := Localization.AtPrime p) (g := algebraMap R F)
    (fun s : p.primeCompl => isUnit_iff_ne_zero.mpr (by
      apply (map_ne_zero_iff (algebraMap R F) (IsFractionRing.injective R F)).mpr
      intro hs
      exact s.property (hs ▸ p.zero_mem)))).toAlgebra

theorem localFractionAlgebra_isScalarTower
    {R F : Type*} [CommRing R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    let := localFractionAlgebra (F := F) p
    IsScalarTower R (Localization.AtPrime p) F := by
  let := localFractionAlgebra (F := F) p
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R F r = IsLocalization.lift _ (algebraMap R (Localization.AtPrime p) r)
  rw [IsLocalization.lift_eq]

theorem localFractionAlgebra_isFractionRing
    {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    let := localFractionAlgebra (F := F) p
    IsFractionRing (Localization.AtPrime p) F := by
  let := localFractionAlgebra (F := F) p
  have := localFractionAlgebra_isScalarTower (F := F) p
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
    (Localization.AtPrime p) F

end WeightedTorusJets.Deformation



open TensorProduct

namespace WeightedTorusJets.Deformation

theorem surjective_baseChange_localization
    {R F Q B : Type*} [CommRing R] [Field F] [Algebra R F]
    [CommRing Q] [Algebra R Q] [CommRing B] [Algebra R B]
    [Algebra Q B] [IsScalarTower R Q B]
    (M : Submonoid Q) [IsLocalization M B]
    [Module.Finite F (F ⊗[R] Q)] :
    Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id R F) (IsScalarTower.toAlgHom R Q B)) := by
  let G := F ⊗[R] Q
  let L := F ⊗[R] B
  let : Algebra G L :=
    (Algebra.TensorProduct.map (AlgHom.id R F) (IsScalarTower.toAlgHom R Q B)).toAlgebra
  have : IsScalarTower F G L :=
    .of_algebraMap_eq (by intro x; simp [G, L, RingHom.algebraMap_toAlgebra])
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := F))) L :=
    IsLocalization.tensorProduct_tensorProduct_right R F M B
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have : IsArtinianRing G := isArtinian_of_tower F (inferInstance : IsArtinian F G)
  exact IsArtinianRing.localization_surjective
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := F))) L

theorem surjective_baseChange_localized_quotient
    {R F P S : Type*} [CommRing R] [Field F] [Algebra R F]
    [CommRing P] [Algebra R P] [CommRing S] [Algebra R S]
    [Algebra P S] [IsScalarTower R P S]
    (M : Submonoid P) [IsLocalization M S] (I : Ideal P)
    [Module.Finite F (F ⊗[R] (P ⧸ I))] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R F)
      (Ideal.quotientMapₐ (I.map (algebraMap P S))
        (IsScalarTower.toAlgHom R P S) Ideal.le_comap_map)) := by
  have : IsScalarTower R (P ⧸ I) (S ⧸ I.map (algebraMap P S)) :=
    .of_algebraMap_eq (by
      intro r
      change Ideal.Quotient.mk _ (algebraMap R S r) =
        Ideal.Quotient.mk _ (algebraMap P S (algebraMap R P r))
      rw [IsScalarTower.algebraMap_apply R P S])
  exact surjective_baseChange_localization (R := R) (F := F)
    (B := S ⧸ I.map (algebraMap P S)) (Algebra.algebraMapSubmonoid (P ⧸ I) M)

noncomputable def genericFiberLocalBaseEquiv
    {R A F B : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    [Field F] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    (F ⊗[A] B) ≃ₐ[F] (F ⊗[R] B) := by
  have := IsLocalization.tensorProduct_compatibleSMul M A F B
  exact Algebra.TensorProduct.equivOfCompatibleSMul R A F F B

end WeightedTorusJets.Deformation

open TensorProduct

namespace WeightedTorusJets.Deformation

variable {R A σ ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

noncomputable def mvPolynomialQuotientBaseChange (I : Ideal (MvPolynomial σ R)) :
    A ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[A]
      MvPolynomial σ A ⧸ I.map (MvPolynomial.map (algebraMap R A)) := by
  refine (Algebra.TensorProduct.tensorQuotientEquiv A (MvPolynomial σ R) A I).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R A) ?_)
  change I.map (MvPolynomial.map (algebraMap R A)) =
    (I.map (Algebra.TensorProduct.includeRight (R := R) (A := A)
      (B := MvPolynomial σ R)).toRingHom).map
        (MvPolynomial.algebraTensorAlgEquiv R A).toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp

@[simp]
theorem mvPolynomialQuotientBaseChange_tmul_mk
    (I : Ideal (MvPolynomial σ R)) (a : A) (p : MvPolynomial σ R) :
    mvPolynomialQuotientBaseChange (A := A) I (a ⊗ₜ[R] Ideal.Quotient.mk I p) =
      a • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p) := by
  simp only [mvPolynomialQuotientBaseChange, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ A _).toLinearMap.map_smul a _

noncomputable def mvPolynomialSpanQuotientBaseChange (f : ι → MvPolynomial σ R) :
    A ⊗[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range f)) ≃ₐ[A]
      MvPolynomial σ A ⧸ Ideal.span
        (Set.range (fun i => MvPolynomial.map (algebraMap R A) (f i))) :=
  (mvPolynomialQuotientBaseChange (A := A) (Ideal.span (Set.range f))).trans
    (Ideal.quotientEquivAlgOfEq A (by rw [Ideal.map_span, ← Set.range_comp']))

@[simp]
theorem mvPolynomialSpanQuotientBaseChange_tmul_mk
    (f : ι → MvPolynomial σ R) (a : A) (p : MvPolynomial σ R) :
    mvPolynomialSpanQuotientBaseChange (A := A) f
        (a ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p) =
      a • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p) := by
  simp [mvPolynomialSpanQuotientBaseChange]

@[simp]
theorem mvPolynomialSpanQuotientBaseChange_symm_mk_map
    (f : ι → MvPolynomial σ R) (p : MvPolynomial σ R) :
    (mvPolynomialSpanQuotientBaseChange (A := A) f).symm
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R A) p)) =
      1 ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p := by
  apply (mvPolynomialSpanQuotientBaseChange (A := A) f).injective
  simp

end WeightedTorusJets.Deformation

end

end SiegelZeros

end OAI
