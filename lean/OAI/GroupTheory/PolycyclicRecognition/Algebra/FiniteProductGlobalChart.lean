import OAI.GroupTheory.PolycyclicRecognition.Geometry.DynkinGlobalExponential

namespace OAI

/-! # Global exponential charts from one finite product formula

The polynomial degree can be any finite common bound supplied by a concrete
representation. It need not already equal the Lie nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter Topology
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem globalExponentialChart_of_finite_products
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G),
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial (coefficients n) X)) :
    ∃ chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, chart x = Exp x := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup E), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ E), (inferInstance : LieAlgebra ℝ L) with }
  let finiteL : FiniteDimensional ℝ L := by
    change FiniteDimensional ℝ E
    infer_instance
  let : LocallyPathConnectedSpace L := by
    change LocallyPathConnectedSpace E
    infer_instance
  let : PreconnectedSpace L := by
    change PreconnectedSpace E
    infer_instance
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  let coeff := coefficients 2
  have hprod := products 2
  have hmul (x y : L) : Exp (finiteDynkinPolynomial coeff ![x, y]) = Exp x * Exp y := by
    symm
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hprod ![x, y]
  have haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v :=
    finiteDynkinPolynomial_single_of_product hExp coeff hprod
  let lt := @leftDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL c d coeff haxis hd
  let rt := @rightDynkinTranslationHomeomorph L (inferInstance : RealNormedLieAlgebra L)
    finiteL c d coeff haxis hd
  have hlt0 (a : L) : lt a 0 = a := by
    change finiteDynkinPolynomial coeff ![a, 0] = a
    have heq : ![a, 0] = (Pi.single 0 a : Fin 2 → L) := by
      funext i; fin_cases i <;> simp
    rw [heq, haxis]
  let b := finBasis ℝ L
  let coeffN := coefficients (finrank ℝ L)
  have hprodN := products (finrank ℝ L)
  obtain ⟨hreg, hder⟩ := local_exponential_regularity_of_dynkin hExp coeffN hprodN b
  let D : (Fin (finrank ℝ L) → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv.trans
    (tangentSpaceCastModel (𝓘(ℝ, E)) (1 : G))
  have hcomb : tangentCombination (E := E) (fun i => (b i : E)) = D.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    erw [tangentCombination_apply]
    change (∑ i, x i • b i) = b.equivFun.symm x
    exact (b.equivFun_symm_apply x).symm
  rw [hcomb] at hder
  obtain ⟨hinj, hmap⟩ := locally_injective_open_of_mfderiv_equiv D hreg hder
  let B := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph
  have hmap' : Filter.map Exp (𝓝 (0 : L)) = 𝓝 (1 : G) := by
    calc
      Filter.map Exp (𝓝 (0 : L)) = Filter.map Exp (Filter.map B (𝓝 0)) := by
        rw [B.map_nhds_eq]; simp [B]
      _ = Filter.map (Exp ∘ b.equivFun.symm) (𝓝 0) := Filter.map_map
      _ = 𝓝 (1 : G) := by simpa only [Function.comp_apply, map_zero, hExp.map_zero] using hmap
  have hinj' : ∃ U ∈ 𝓝 (0 : L), InjOn Exp U := by
    obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨B '' U, ?_, ?_⟩
    · have hh := B.isOpenMap.image_mem_nhds hU
      simpa [B] using hh
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
      exact congrArg B (hi hx hy he)
  have hlocal : IsLocalHomeomorph Exp :=
    localHomeomorph_of_translations Exp lt hlt0 hmul hmap' hinj'
  have hright : Continuous (fun p : L × L => rt p.1 p.2) :=
    (@continuous_binaryDynkin L (inferInstance : RealNormedLieAlgebra L) finiteL c coeff).comp
      (continuous_snd.prodMk continuous_fst)
  have hsurj : Function.Surjective Exp :=
    exponential_surjective_of_range_mem_nhds hExp coeff (fun x y => (hmul x y).symm)
      (by rw [← hmap']; exact Filter.range_mem_map)
  have hcov : IsCoveringMap Exp := covering_of_translations Exp rt
    (fun a x => hmul x a) hExp.map_zero hlocal
    (@continuous_rightDynkinTranslationInverse L (inferInstance : RealNormedLieAlgebra L)
      finiteL c d coeff haxis hd) hright lt hmul
    hsurj
  have : LocallyPathConnectedSpace G :=
    (hcov.isQuotientMap hsurj).locallyPathConnectedSpace
  exact ⟨homeomorphOfSimplyConnectedCovering Exp hcov, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
