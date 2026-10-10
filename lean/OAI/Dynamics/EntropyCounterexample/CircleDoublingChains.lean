import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.CircleDoublingChains

abbrev Circle := AddCircle (1 : ℝ)
abbrev singularSet := TopCat.toSSet.obj (TopCat.of Circle)
abbrev coefficients := ModuleCat.of ℝ ℝ
abbrev chains := realSingularChainComplex Circle

def loopMap : C(Convexity.StdSimplex ℝ (Fin 2), Circle) :=
  ⟨fun p => (p 1 : Circle),
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (Convexity.StdSimplex.continuous_weights_apply ℝ 1)⟩

def triangleMap : C(Convexity.StdSimplex ℝ (Fin 3), Circle) :=
  ⟨fun p => (p 1 + 2 * p 2 : ℝ),
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).add
        (continuous_const.mul (Convexity.StdSimplex.continuous_weights_apply ℝ 2)))⟩

def doubling : Circle → Circle := fun x => x + x

lemma continuous_doubling : Continuous doubling := by
  exact continuous_id.add continuous_id

def doublingMap : C(Circle, Circle) := ⟨doubling, continuous_doubling⟩

def loopSimplex : singularSet _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm loopMap

def triangleSimplex : singularSet _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm triangleMap

def doubledLoopSimplex : singularSet _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) _).symm (doublingMap.comp loopMap)

lemma triangle_face_zero : singularSet.δ 0 triangleSimplex = loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change Convexity.StdSimplex ℝ (Fin 2) at p
  change ((Convexity.StdSimplex.map (0 : Fin 3).succAbove p) 1 +
    2 * (Convexity.StdSimplex.map (0 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle)
  have h0 : (Convexity.StdSimplex.map (0 : Fin 3).succAbove p) 1 = p 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (0 : Fin 3).succAbove x = (1 : Fin 3)) = {0} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  have h1 : (Convexity.StdSimplex.map (0 : Fin 3).succAbove p) 2 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (0 : Fin 3).succAbove x = (2 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  rw [h0, h1]
  have hsum : p 0 + p 1 = 1 := by
    simpa only [Fin.sum_univ_two] using p.total_of_fintype
  have hp : p 0 + 2 * p 1 = p 1 + 1 := by linarith
  rw [hp, AddCircle.coe_add_period]

lemma triangle_face_one : singularSet.δ 1 triangleSimplex = doubledLoopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change Convexity.StdSimplex ℝ (Fin 2) at p
  change ((Convexity.StdSimplex.map (1 : Fin 3).succAbove p) 1 +
    2 * (Convexity.StdSimplex.map (1 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle) + (p 1 : Circle)
  have h0 : (Convexity.StdSimplex.map (1 : Fin 3).succAbove p) 1 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (1 : Fin 3).succAbove x = (1 : Fin 3)) = ∅ := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_empty]
  have h1 : (Convexity.StdSimplex.map (1 : Fin 3).succAbove p) 2 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (1 : Fin 3).succAbove x = (2 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  rw [h0, h1, zero_add, two_mul, AddCircle.coe_add]

lemma triangle_face_two : singularSet.δ 2 triangleSimplex = loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change Convexity.StdSimplex ℝ (Fin 2) at p
  change ((Convexity.StdSimplex.map (2 : Fin 3).succAbove p) 1 +
    2 * (Convexity.StdSimplex.map (2 : Fin 3).succAbove p) 2 : ℝ) = (p 1 : Circle)
  have h0 : (Convexity.StdSimplex.map (2 : Fin 3).succAbove p) 1 = p 1 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (2 : Fin 3).succAbove x = (1 : Fin 3)) = {1} := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_singleton]
  have h1 : (Convexity.StdSimplex.map (2 : Fin 3).succAbove p) 2 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 2 =>
        (2 : Fin 3).succAbove x = (2 : Fin 3)) = ∅ := by decide
    simp only [RealSimplex.map_apply, hf, Finset.sum_empty]
  rw [h0, h1, mul_zero, add_zero]

lemma loop_endpoints : singularSet.δ 0 loopSimplex = singularSet.δ 1 loopSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) _).injective
  ext p
  change Convexity.StdSimplex ℝ (Fin 1) at p
  change ((Convexity.StdSimplex.map (0 : Fin 2).succAbove p) 1 : Circle) =
    ((Convexity.StdSimplex.map (1 : Fin 2).succAbove p) 1 : Circle)
  have h0 : (Convexity.StdSimplex.map (0 : Fin 2).succAbove p) 1 = 1 := by
    have hf : (Finset.univ.filter fun x : Fin 1 =>
        (0 : Fin 2).succAbove x = (1 : Fin 2)) = {0} := by decide
    rw [RealSimplex.map_apply, hf, Finset.sum_singleton]
    simpa only [Fin.sum_univ_one] using p.total_of_fintype
  have h1 : (Convexity.StdSimplex.map (1 : Fin 2).succAbove p) 1 = 0 := by
    have hf : (Finset.univ.filter fun x : Fin 1 =>
        (1 : Fin 2).succAbove x = (1 : Fin 2)) = ∅ := by decide
    rw [RealSimplex.map_apply, hf, Finset.sum_empty]
  rw [h0, h1, AddCircle.coe_period, AddCircle.coe_zero]

def loopChain : coefficients ⟶ chains.X 1 := singularSet.ιChainComplex loopSimplex

def triangleChain : coefficients ⟶ chains.X 2 := singularSet.ιChainComplex triangleSimplex

def doubledLoopChain : coefficients ⟶ chains.X 1 :=
  singularSet.ιChainComplex doubledLoopSimplex

lemma loopChain_boundary : loopChain ≫ chains.d 1 0 = 0 := by
  change singularSet.ιChainComplex loopSimplex ≫
    (singularSet.chainComplex coefficients).d 1 0 = 0
  rw [SSet.ιChainComplex_d]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • singularSet.ιChainComplex (singularSet.δ i loopSimplex)) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, loop_endpoints, add_neg_cancel]

lemma triangleChain_boundary :
    triangleChain ≫ chains.d 2 1 = loopChain - doubledLoopChain + loopChain := by
  change singularSet.ιChainComplex triangleSimplex ≫
    (singularSet.chainComplex coefficients).d 2 1 = _
  rw [SSet.ιChainComplex_d]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • singularSet.ιChainComplex (singularSet.δ i triangleSimplex)) = _
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, neg_one_sq, one_smul, neg_smul,
    triangle_face_zero, triangle_face_one, triangle_face_two,
    loopChain, doubledLoopChain]
  erw [sub_eq_add_neg]
  rfl

lemma doubledLoopSimplex_eq_map : doubledLoopSimplex =
    (TopCat.toSSet.map (TopCat.ofHom doublingMap)).app _ loopSimplex := by
  rfl

lemma doubledLoopChain_eq_map :
    doubledLoopChain = loopChain ≫ (realSingularChainMap doubling continuous_doubling).f 1 := by
  rw [loopChain]
  change _ = singularSet.ιChainComplex loopSimplex ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom doublingMap)) coefficients).f 1
  rw [SSet.ι_chainComplexMap_f]
  exact congrArg singularSet.ιChainComplex doubledLoopSimplex_eq_map

def loop : chains.X 1 := loopChain.hom 1

def triangle : chains.X 2 := triangleChain.hom 1

lemma loop_boundary : (chains.d 1 0).hom loop = 0 := by
  exact ConcreteCategory.congr_hom loopChain_boundary (1 : ℝ)

lemma triangle_boundary : (chains.d 2 1).hom triangle =
    loop - ((realSingularChainMap doubling continuous_doubling).f 1).hom loop + loop := by
  have h := ConcreteCategory.congr_hom triangleChain_boundary (1 : ℝ)
  rw [doubledLoopChain_eq_map] at h
  exact h

lemma doubling_loop_sub_two_is_boundary :
    ∃ w : chains.X 2, (chains.d 2 1).hom w =
      ((realSingularChainMap doubling continuous_doubling).f 1).hom loop - (2 : ℝ) • loop := by
  refine ⟨-triangle, ?_⟩
  rw [map_neg, triangle_boundary, two_smul]
  abel

lemma loop_cycle_sc : (chains.sc 1).g.hom loop = 0 := by
  change (chains.d 1 ((ComplexShape.down ℕ).next 1)).hom loop = 0
  rw [ChainComplex.next_nat_succ 0]
  exact loop_boundary

def loopClass : RealSingularHomology 1 Circle :=
  moduleHomologyClass (chains.sc 1) loop loop_cycle_sc

lemma loopClass_eq_zero_iff : loopClass = 0 ↔
    ∃ w : chains.X 2, (chains.d 2 1).hom w = loop := by
  have h := moduleHomologyClass_eq_zero_iff (chains.sc 1)
    (show (chains.sc 1).X₂ from loop) loop_cycle_sc
  change loopClass = 0 ↔ (∃ w : chains.X ((ComplexShape.down ℕ).prev 1),
    (chains.d ((ComplexShape.down ℕ).prev 1) 1).hom w = loop) at h
  rw [ChainComplex.prev ℕ 1] at h
  exact h

theorem doubling_loopClass :
    realHomologyMap 1 doubling continuous_doubling loopClass = (2 : ℝ) • loopClass := by
  let S := chains.sc 1
  let z : S.X₂ := loop
  let φ : S ⟶ S :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) 1).map
      (realSingularChainMap doubling continuous_doubling)
  have hz : S.g.hom z = 0 := loop_cycle_sc
  have hz' : S.g.hom (φ.τ₂.hom z) = 0 := by
    have h := congrArg (fun k : S.X₂ ⟶ S.X₃ => k.hom z) φ.comm₂₃
    change S.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
    simpa only [hz, map_zero] using h
  have hdiff : S.g.hom (φ.τ₂.hom z - (2 : ℝ) • z) = 0 := by
    simp only [map_sub, map_smul, hz', hz, smul_zero, sub_self]
  have he : ∃ w : S.X₁, S.f.hom w = φ.τ₂.hom z - (2 : ℝ) • z := by
    change ∃ w : chains.X ((ComplexShape.down ℕ).prev 1),
      (chains.d ((ComplexShape.down ℕ).prev 1) 1).hom w =
        ((realSingularChainMap doubling continuous_doubling).f 1).hom loop - (2 : ℝ) • loop
    rw [ChainComplex.prev ℕ 1]
    exact doubling_loop_sub_two_is_boundary
  let π : LinearMap.ker S.g.hom →ₗ[ℝ] S.homology :=
    S.moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
      (LinearMap.range S.moduleCatToCycles).mkQ
  let u : LinearMap.ker S.g.hom := ⟨z, LinearMap.mem_ker.mpr hz⟩
  let u' : LinearMap.ker S.g.hom := ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hzero := (moduleHomologyClass_eq_zero_iff S
    (φ.τ₂.hom z - (2 : ℝ) • z) hdiff).mpr he
  change π (u' - (2 : ℝ) • u) = 0 at hzero
  have heq : π u' = (2 : ℝ) • π u := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_smul] using hzero
  change (ShortComplex.homologyMap φ).hom (moduleHomologyClass S z hz) =
    (2 : ℝ) • moduleHomologyClass S z hz
  rw [moduleHomologyClass_map φ z hz hz']
  exact heq

theorem exists_doubling_eigenvector_of_loop_not_boundary
    (h : ¬ ∃ w : chains.X 2, (chains.d 2 1).hom w = loop) :
    ∃ v : RealSingularHomology 1 Circle,
      v ≠ 0 ∧ realHomologyMap 1 doubling continuous_doubling v = (2 : ℝ) • v :=
  ⟨loopClass, mt loopClass_eq_zero_iff.mp h, doubling_loopClass⟩

end Problem340.CircleDoublingChains

end

end OAI
