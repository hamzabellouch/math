import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

section ModuleCycles

variable {R : Type*} [Ring R]

def moduleHomologyClass (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) : S.homology :=
  S.moduleCatHomologyIso.toLinearEquiv.symm
    (Submodule.Quotient.mk (⟨z, LinearMap.mem_ker.mpr hz⟩ : LinearMap.ker S.g.hom))

theorem moduleHomologyClass_eq_zero_iff (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S z hz = 0 ↔ ∃ w : S.X₁, S.f.hom w = z := by
  unfold moduleHomologyClass
  conv_lhs =>
    exact propext S.moduleCatHomologyIso.toLinearEquiv.symm.map_eq_zero_iff
  change (Submodule.Quotient.mk (⟨z, LinearMap.mem_ker.mpr hz⟩ : LinearMap.ker S.g.hom) :
    LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    exact Subtype.ext hw

theorem moduleHomologyClass_ne_zero_of_not_boundary
    (S : ShortComplex (ModuleCat R)) (z : S.X₂) (hz : S.g.hom z = 0)
    (hboundary : ¬ ∃ w : S.X₁, S.f.hom w = z) :
    moduleHomologyClass S z hz ≠ 0 :=
  mt (moduleHomologyClass_eq_zero_iff S z hz).mp hboundary

theorem moduleHomologyClass_eq_pi (S : ShortComplex (ModuleCat R))
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S z hz = S.homologyπ.hom
      (S.moduleCatCyclesIso.inv.hom ⟨z, LinearMap.mem_ker.mpr hz⟩) := by
  exact (S.moduleCatCyclesIso_inv_π_apply ⟨z, LinearMap.mem_ker.mpr hz⟩).symm

theorem moduleHomologyClass_map {S T : ShortComplex (ModuleCat R)}
    (φ : S ⟶ T) (z : S.X₂) (hz : S.g.hom z = 0)
    (hz' : T.g.hom (φ.τ₂.hom z) = 0) :
    (ShortComplex.homologyMap φ).hom (moduleHomologyClass S z hz) =
      moduleHomologyClass T (φ.τ₂.hom z) hz' := by
  rw [moduleHomologyClass_eq_pi, moduleHomologyClass_eq_pi]
  let zs := S.moduleCatCyclesIso.inv.hom ⟨z, LinearMap.mem_ker.mpr hz⟩
  let zt := T.moduleCatCyclesIso.inv.hom ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hs : S.iCycles.hom zs = z :=
    S.moduleCatCyclesIso_inv_iCycles_apply ⟨z, LinearMap.mem_ker.mpr hz⟩
  have ht : T.iCycles.hom zt = φ.τ₂.hom z :=
    T.moduleCatCyclesIso_inv_iCycles_apply ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hc : (ShortComplex.cyclesMap φ).hom zs = zt := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun k : S.cycles ⟶ T.X₂ => k.hom zs)
      (ShortComplex.cyclesMap_i φ)
    change T.iCycles.hom ((ShortComplex.cyclesMap φ).hom zs) =
      φ.τ₂.hom (S.iCycles.hom zs) at h
    simpa only [hs, ht] using h
  have h := congrArg (fun k : S.cycles ⟶ T.homology => k.hom zs)
    (ShortComplex.homologyπ_naturality φ)
  change (ShortComplex.homologyMap φ).hom (S.homologyπ.hom zs) =
    T.homologyπ.hom ((ShortComplex.cyclesMap φ).hom zs) at h
  rw [hc] at h
  exact h

theorem moduleHomology_eigenvector_of_cycle
    (S : ShortComplex (ModuleCat R)) (φ : S ⟶ S)
    (z : S.X₂) (hz : S.g.hom z = 0)
    (hboundary : ¬ ∃ w : S.X₁, S.f.hom w = z)
    (c : R) (heigen : ∃ w : S.X₁, S.f.hom w = φ.τ₂.hom z - c • z) :
    ∃ v : S.homology, v ≠ 0 ∧ (ShortComplex.homologyMap φ).hom v = c • v := by
  have hz' : S.g.hom (φ.τ₂.hom z) = 0 := by
    have h := congrArg (fun k : S.X₂ ⟶ S.X₃ => k.hom z) φ.comm₂₃
    change S.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
    simpa only [hz, map_zero] using h
  have hdiff : S.g.hom (φ.τ₂.hom z - c • z) = 0 := by
    simp only [map_sub, map_smul, hz', hz, smul_zero, sub_self]
  let π : LinearMap.ker S.g.hom →ₗ[R] S.homology :=
    S.moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
      (LinearMap.range S.moduleCatToCycles).mkQ
  let u : LinearMap.ker S.g.hom := ⟨z, LinearMap.mem_ker.mpr hz⟩
  let u' : LinearMap.ker S.g.hom := ⟨φ.τ₂.hom z, LinearMap.mem_ker.mpr hz'⟩
  have hzero := (moduleHomologyClass_eq_zero_iff S
    (φ.τ₂.hom z - c • z) hdiff).mpr heigen
  change π (u' - c • u) = 0 at hzero
  have heq : π u' = c • π u := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_smul] using hzero
  refine ⟨moduleHomologyClass S z hz,
    moduleHomologyClass_ne_zero_of_not_boundary S z hz hboundary, ?_⟩
  rw [moduleHomologyClass_map φ z hz hz']
  exact heq

end ModuleCycles

abbrev realSingularChainComplex (X : Type) [TopologicalSpace X] :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)).obj (TopCat.of X)

abbrev realSingularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    realSingularChainComplex X ⟶ realSingularChainComplex Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)).map (TopCat.ofHom (continuousMapOf f hf))

theorem exists_realSingularHomology_two_ne_zero_of_cycle
    (X : Type) [TopologicalSpace X]
    (z : (realSingularChainComplex X).X 2)
    (hz : ((realSingularChainComplex X).d 2 1).hom z = 0)
    (hboundary : ¬ ∃ w : (realSingularChainComplex X).X 3,
      ((realSingularChainComplex X).d 3 2).hom w = z) :
    ∃ v : RealSingularHomology 2 X, v ≠ 0 := by
  let C := realSingularChainComplex X
  have hz' : (C.sc 2).g.hom z = 0 := by
    change (C.d 2 ((ComplexShape.down ℕ).next 2)).hom z = 0
    have hnext : (ComplexShape.down ℕ).next 2 = 1 := ChainComplex.next_nat_succ 1
    rw [hnext]
    exact hz
  have hb' : ¬ ∃ w : (C.sc 2).X₁, (C.sc 2).f.hom w = z := by
    change ¬ ∃ w : C.X ((ComplexShape.down ℕ).prev 2),
      (C.d ((ComplexShape.down ℕ).prev 2) 2).hom w = z
    have hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
    rw [hprev]
    exact hboundary
  exact ⟨moduleHomologyClass (C.sc 2) z hz',
    moduleHomologyClass_ne_zero_of_not_boundary (C.sc 2) z hz' hb'⟩

theorem realHomologyMap_two_eigenvector_of_cycle
    (X : Type) [TopologicalSpace X] (f : X → X) (hf : Continuous f)
    (z : (realSingularChainComplex X).X 2)
    (hz : ((realSingularChainComplex X).d 2 1).hom z = 0)
    (hboundary : ¬ ∃ w : (realSingularChainComplex X).X 3,
      ((realSingularChainComplex X).d 3 2).hom w = z)
    (c : ℝ) (heigen : ∃ w : (realSingularChainComplex X).X 3,
      ((realSingularChainComplex X).d 3 2).hom w =
        ((realSingularChainMap f hf).f 2).hom z - c • z) :
    ∃ v : RealSingularHomology 2 X, v ≠ 0 ∧ realHomologyMap 2 f hf v = c • v := by
  let C := realSingularChainComplex X
  let φ : C.sc 2 ⟶ C.sc 2 :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) 2).map
      (realSingularChainMap f hf)
  have hnext : (ComplexShape.down ℕ).next 2 = 1 := ChainComplex.next_nat_succ 1
  have hprev : (ComplexShape.down ℕ).prev 2 = 3 := ChainComplex.prev ℕ 2
  have hz' : (C.sc 2).g.hom z = 0 := by
    change (C.d 2 ((ComplexShape.down ℕ).next 2)).hom z = 0
    rw [hnext]
    exact hz
  have hb' : ¬ ∃ w : (C.sc 2).X₁, (C.sc 2).f.hom w = z := by
    change ¬ ∃ w : C.X ((ComplexShape.down ℕ).prev 2),
      (C.d ((ComplexShape.down ℕ).prev 2) 2).hom w = z
    rw [hprev]
    exact hboundary
  have he' : ∃ w : (C.sc 2).X₁, (C.sc 2).f.hom w = φ.τ₂.hom (show (C.sc 2).X₂ from z) - c • (show (C.sc 2).X₂ from z) := by
    change ∃ w : C.X ((ComplexShape.down ℕ).prev 2),
      (C.d ((ComplexShape.down ℕ).prev 2) 2).hom w =
        ((realSingularChainMap f hf).f 2).hom z - c • z
    rw [hprev]
    exact heigen
  exact moduleHomology_eigenvector_of_cycle (C.sc 2) φ z hz' hb' c he'

end Problem340

end

end OAI
