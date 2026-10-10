import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLaurent
import OAI.NumberTheory.SiegelZeros.Structure.IdealPowLayer

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets.Geometry

theorem torus_quotient_dimension_pos_of_cotangent_finrank_le_three
    {K : Type*} [Field K]
    (q : Ideal (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) [q.IsPrime]
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≤ 3) :
    0 < ringKrullDim (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ⧸ q) := by
  obtain ⟨d, hd, _⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ⧸ q)
  have hrank : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = 4 - d := by
    simpa [hd] using
      torus_component_cotangent_eq_codimension (K := K) 4 q
  have hpos : 0 < d := by omega
  rw [hd]
  exact_mod_cast hpos

theorem laurent_quotient_dimension_pos_of_torus_cotangent_finrank_le_three
    {K : Type*} [Field K]
    (q : Ideal (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) [q.IsPrime]
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≤ 3) :
    0 < ringKrullDim (AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸
      q.comap (laurentEquivLocalization K (Fin 4)).toRingHom) := by
  let e := laurentEquivLocalization K (Fin 4)
  have he : q = (q.comap e.toRingHom).map e.toRingHom :=
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective q).symm
  rw [ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquivAlg _ q e he).toRingEquiv]
  exact torus_quotient_dimension_pos_of_cotangent_finrank_le_three q hdim



open MvPolynomial

theorem torus_prime_fractionField_residue_equiv
    {K : Type*} [Field K]
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K)))) :
    let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
    let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
    let P := q.asIdeal.comap (laurentEquivLocalization K (Fin 4)).toRingHom
    let S := Localization.AtPrime q.asIdeal
    ∃ E : FractionRing (L ⧸ P) ≃ₐ[K] IsLocalRing.ResidueField S,
      ∀ i : Fin 4, E (algebraMap (L ⧸ P) (FractionRing (L ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) =
          algebraMap T (IsLocalRing.ResidueField S)
            (algebraMap (MvPolynomial (Fin 4) K) T (X i)) := by
  dsimp only
  let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
  let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
  let e := laurentEquivLocalization K (Fin 4)
  let P := q.asIdeal.comap e.toRingHom
  let S := Localization.AtPrime q.asIdeal
  let F := IsLocalRing.ResidueField S
  have : P.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  let : Algebra (T ⧸ q.asIdeal) F := localizationResidueQuotientAlgebra (A := S) q.asIdeal
  obtain ⟨htower, hfrac⟩ := localization_residue_quotientAlgebra_data (A := S) q.asIdeal
  have : IsScalarTower K (T ⧸ q.asIdeal) F := by
    apply IsScalarTower.of_algebraMap_eq' (R := K) (S := T ⧸ q.asIdeal) (A := F)
    ext c
    change algebraMap K F c = algebraMap (T ⧸ q.asIdeal) F
      (Ideal.Quotient.mk q.asIdeal (algebraMap K T c))
    rw [localization_residue_quotientAlgebra_mk]
    exact IsScalarTower.algebraMap_apply K T F c
  let E₀ : (L ⧸ P) ≃ₐ[K] (T ⧸ q.asIdeal) := Ideal.quotientEquivAlg P q.asIdeal e
    (q.asIdeal.map_comap_of_surjective e.toRingHom e.surjective).symm
  let E : FractionRing (L ⧸ P) ≃ₐ[K] F := IsFractionRing.algEquivOfAlgEquiv E₀
  refine ⟨E, fun i ↦ ?_⟩
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap (T ⧸ q.asIdeal) F
    (Ideal.Quotient.mk q.asIdeal (e (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) = _
  rw [localization_residue_quotientAlgebra_mk, laurentEquivLocalization_coordinate]

theorem torus_prime_residue_logarithmicForm_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))))
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 3)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let S := Localization.AtPrime q.asIdeal
    logarithmicForm (F := IsLocalRing.ResidueField S) c
      (fun i : Fin 4 ↦ Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
      (algebraMap (MvPolynomial (Fin 4) K) S (X i))) ≠ 0 := by
  dsimp only
  let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
  let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
  let P := q.asIdeal.comap (laurentEquivLocalization K (Fin 4)).toRingHom
  let S := Localization.AtPrime q.asIdeal
  let F := IsLocalRing.ResidueField S
  have : P.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  have hpos := laurent_quotient_dimension_pos_of_torus_cotangent_finrank_le_three
    q.asIdeal hdim
  have hn := logarithmicForm_ne_zero_on_torus_subvariety P hpos c hc
  obtain ⟨E, hE⟩ := torus_prime_fractionField_residue_equiv q
  let x : Fin 4 → FractionRing (L ⧸ P) := fun i ↦ algebraMap (L ⧸ P) _
    (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
  have hcoords (i : Fin 4) : E (x i) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
        (algebraMap (MvPolynomial (Fin 4) K) S (X i)) := by
    rw [hE]
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 4) K) T F]
    rfl
  dsimp only [S] at hcoords
  intro hzero
  apply hn
  have hm := WeightedTorusJets.logarithmic_relation_map_algHom E.symm.toAlgHom c _
    (by simpa only [logarithmicForm, div_eq_mul_inv] using hzero)
  simpa only [AlgEquiv.coe_toAlgHom, ← hcoords, AlgEquiv.symm_apply_apply,
    logarithmicForm, div_eq_mul_inv] using hm

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem source_local_torus_rectangle_graded_length_gt {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c)
    (v : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (q : PrimeSpectrum TorusCoordRing) (b : ℕ) (F : PolyRing)
    (hq : (rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet (fun j => (v j : Fin 4 → K)) a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b).IsMinimalPrime q.asIdeal)
    (hnext : rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet (fun j => (v j : Fin 4 → K)) a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) (b + 1) ≤ q.asIdeal)
    (hpos : 1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)))
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 4) :
    ((4 * N) ^ (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal))) : ℕ) <
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⧸
      Ideal.map (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal))
        (rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing
            (invariantJet (fun j => (v j : Fin 4 → K)) a F))
          (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b)) := by
  let p : Ideal PolyRing := q.asIdeal.comap (algebraMap PolyRing TorusCoordRing)
  have : p.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  have : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers torusCoordinateProduct) (Localization.AtPrime q.asIdeal) q.asIdeal
  have hX (i : Fin 4) : MvPolynomial.X i ∉ p := by
    intro hi
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hi (torus_coordinate_isUnit i))
  have hx (i : Fin 4) : IsUnit
      (algebraMap PolyRing (Localization.AtPrime q.asIdeal) (MvPolynomial.X i)) :=
    IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨MvPolynomial.X i, hX i⟩ : p.primeCompl)
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hc.ne_zero (0 : Fin 4) (congrFun hzero 0)
  obtain ⟨I, hI, hD⟩ := exists_selected_independent_conormal_derivations
    (S := Localization.AtPrime q.asIdeal) p.primeCompl
    (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) hx c hc0 v
    (fun hsmall => torus_prime_residue_logarithmicForm_ne_zero q hsmall c hc)
  change I.card = min (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
    (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal))) 3 at hI
  have hposI : I.Nonempty := Finset.card_pos.mp (by rw [hI]; omega)
  have hprimary := (local_torus_stage_primary_data (fun j => (v j : Fin 4 → K)) q
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b F hq).1
  have hlower := derivativeStageIdeal_graded_length_lower
    (localTorusDerivationOverRat (fun j => (v j : Fin 4 → K)) q)
    (localTorusDerivationOverRat_commute _ q 0 1)
    (localTorusDerivationOverRat_commute _ q 0 2)
    (localTorusDerivationOverRat_commute _ q 1 2)
    (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) I hposI
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊)
    (fun j => (by decide : 2 ≤ 9).trans (rectangle_cutoff_ge_nine hH hHN j)) b
    (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
      (algebraMap PolyRing TorusCoordRing F))
    (local_torus_stage_le_maximal (fun j => (v j : Fin 4 → K)) q _ (b + 1) F hnext)
    (by simpa only [localTorusDerivationOverRat_cotangent_eq_direct (fun j => (v j : Fin 4 → K)) q p.primeCompl] using hD) hprimary
  have hnum := rectangle_floor_product_gt_nat hH hHN hpos hdim I hI
  rw [local_torus_derivativeStageIdeal_eq]
  rw [Finset.prod_coe_sort I (fun j : Fin 3 => ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1)] at hlower
  exact lt_of_lt_of_le (by exact_mod_cast hnum) hlower


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem uniform_rectangular_multiplicity
    {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (v : Module.Basis (Fin 3) ℂ
      (LinearMap.ker (dotProductEquiv ℂ (Fin 4) c)))
    (F : MvPolynomial (Fin 4) ℂ) (hF : F ∈ polynomialBox ℂ N)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1)
          (invariantJet (fun j ↦ (v j : Fin 4 → ℂ)) a F) = 0) :
    F = 0 := by
  by_contra hF0
  obtain ⟨b, _, q, _, hq, hqnext, hpos, hdim⟩ :=
    torus_rectangle_shared_component_data hH hHN (fun j ↦ (v j : Fin 4 → ℂ)) F hF0 hvanish
  have hlength := source_local_torus_rectangle_graded_length_gt hH hHN c hc v q b F
    hq hqnext.le hpos hdim
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hH.trans hHN)
  have hupper := rectangleJetIdeal_length_le q.asIdeal
    (fun j ↦ (v j : Fin 4 → ℂ))
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b hN hF hq
  exact (not_lt_of_ge hupper) hlength



theorem idealPowLayer_eq {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ)
    (x y : ↥(I ^ n)) :
    (Submodule.Quotient.mk x : idealPowLayer I n) = Submodule.Quotient.mk y ↔
      (x - y : A) ∈ I ^ (n + 1) := by
  rw [Submodule.Quotient.eq, ← idealPowLayer_kernel I n]
  constructor
  · intro h
    exact Submodule.mem_map.mpr ⟨x - y, by simpa only [Submodule.ker_mkQ] using h, rfl⟩
  · intro h
    obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp h
    have hzy : z = x - y := Subtype.ext heq
    simpa only [Submodule.ker_mkQ, hzy] using hz



theorem quotient_taylor_degree_one
    {R σ : Type*} [CommRing R] [Algebra ℚ R] [Fintype σ]
    (J m : Ideal R) (hJm : J ≤ m)
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0)
    (D : σ → Derivation ℚ R R)
    (φ : (R ⧸ J) →+* (MvPolynomial σ (R ⧸ m) ⧸
      Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial σ (R ⧸ m)) ^ k i)))
    (hres : ((rectangularAugmentation k hk).toRingHom.comp φ).comp
      (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (x : m)
    (hfirst : φ (Ideal.Quotient.mk J x) -
      ∑ i, Ideal.Quotient.mk m (D i x) •
        Ideal.Quotient.mk (Ideal.span (Set.range fun j => (MvPolynomial.X j : MvPolynomial σ (R ⧸ m)) ^ k j))
          (MvPolynomial.X i) ∈
      (RingHom.ker (rectangularAugmentation (K := R ⧸ m) k hk)) ^ 2) :
    let N := RingHom.ker (rectangularAugmentation (K := R ⧸ m) k hk)
    let vars (i : σ) : ↥(N ^ 1) := ⟨
      Ideal.Quotient.mk (Ideal.span (Set.range fun j => (MvPolynomial.X j : MvPolynomial σ (R ⧸ m)) ^ k j))
        (MvPolynomial.X i), by
          simp only [pow_one]
          exact (quotientAugmentation_mk _ _ (MvPolynomial.X i)).trans
            (MvPolynomial.constantCoeff_X _ i)⟩
    mapIdealPowLayerQuotientAugmentation J m hJm φ (rectangularAugmentation k hk) hres 1
      (Submodule.Quotient.mk (⟨Ideal.Quotient.mk J x, by
        simpa only [pow_one] using Ideal.mem_map_of_mem (Ideal.Quotient.mk J) x.property⟩ :
          ↥((m.map (Ideal.Quotient.mk J)) ^ 1))) =
      ∑ i, Ideal.Quotient.mk m (D i x) •
        (Submodule.Quotient.mk (vars i) : idealPowLayer N 1) := by
  classical
  intro N vars
  rw [mapIdealPowLayerQuotientAugmentation_mk]
  have hsum : (Submodule.Quotient.mk
      (∑ i, Ideal.Quotient.mk m (D i x) • vars i) : idealPowLayer N 1) =
      ∑ i, Ideal.Quotient.mk m (D i x) •
        (Submodule.Quotient.mk (vars i) : idealPowLayer N 1) := by
    change (Submodule.mkQ _)
      (∑ i, Ideal.Quotient.mk m (D i x) • vars i) = _
    simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.mkQ_apply]
  rw [← hsum]
  apply (idealPowLayer_eq N 1 _ _).mpr
  simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul_of_tower] using hfirst



theorem rectangular_variable_ideal_isMaximal {σ K : Type*} [Field K]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    ((MvPolynomial.idealOfVars σ K).map
      (Ideal.Quotient.mk (Ideal.span (Set.range fun i =>
        (MvPolynomial.X i : MvPolynomial σ K) ^ k i)))).IsMaximal := by
  rw [← ker_quotientAugmentation _ (rectangularIdeal_le_ker_constantCoeff k hk)]
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap K _ c, (quotientAugmentation _ _).commutes c⟩

end WeightedTorusJets.Geometry


end SiegelZeros

end OAI
