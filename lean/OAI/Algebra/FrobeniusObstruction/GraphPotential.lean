import Mathlib
import OAI.Algebra.FrobeniusObstruction.MovingCharts

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
open Frobenius
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

abbrev ParameterScalar := Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell

def normalIndices : Finset (InternalVar n) := Finset.univ.filter fun c => c.1 = true

@[simp] theorem mem_normalIndices (c : InternalVar n) : c ∈ normalIndices (n := n) ↔ c.1 = true := by
  simp [normalIndices]

def normalPlane : ParameterScalar (n := n) (k := k) ell →ₐ[ThreeParameters.Ring k]
    ParameterScalar (n := n) (k := k) ell :=
  planeRestriction ell (Nat.Prime.pos Fact.out) normalIndices

omit [CharP k ell] in
@[simp] theorem normalPlane_coordinate (b : Bool) (t : TangentVar n) :
    normalPlane (k := k) ell (coordinate ell (b,t)) =
      if b then 0 else coordinate ell (b,t) := by
  simp only [normalPlane, planeRestriction_coordinate, mem_normalIndices]

theorem normalPlane_movingGraphSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    ((normalPlane (n := n) ell).restrictScalars k).comp (movingGraphSlot ell a ha false) =
      movingGraphSlot ell a ha false := by
  refine algHom_ext (ι := GraphVar n) (k := k)
    (S := ParameterScalar (n := n) (k := k) ell) ell _ _ ?_
  intro v
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, movingGraphSlot_coordinate]
  cases v with
  | inl i => exact AlgHom.commutes (normalPlane (n := n) ell) _
  | inr t => simp [movingGraphCoordinates]

omit [CharP k ell] in
theorem normalPlane_smul (r : k) (x : ParameterScalar (n := n) (k := k) ell) :
    normalPlane ell (r • x) = r • normalPlane ell x :=
  map_smul ((normalPlane ell).restrictScalars k) r x

omit [CharP k ell] in
theorem normalPlane_fixedComplement (D : FormalData (k := k) n) (c : InternalVar n) :
    normalPlane ell (baseChange (l := ThreeParameters.Ring k) ell (fixedComplement ell D c)) = 0 := by
  simp only [fixedComplement, map_sum, map_smul, baseChange_coordinate,
    normalPlane_smul, normalPlane_coordinate, ite_true, smul_zero, Finset.sum_const_zero]

                                                                                  
def ambientCoordinates (a : SlopeVar d → ThreeParameters.Ring k) :
    AmbientVar n → ParameterScalar (n := n) (k := k) ell
  | .inl i => @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
      inferInstance inferInstance inferInstance (a i)
  | .inr c => coordinate ell c

theorem ambientCoordinates_pow (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (i : AmbientVar n) :
    ambientCoordinates (n := n) ell a i ^ ell = 0 := by
  cases i with
  | inl i =>
      change (@algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
        inferInstance inferInstance inferInstance (a i)) ^ ell = 0
      rw [← map_pow, ThreeParameters.augmentation_zero_pow k ell (a i) (ha i), map_zero]
  | inr c => exact coordinate_pow ell c

def ambientSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    Frobenius.Ring (ι := AmbientVar n) (k := k) ell →ₐ[k] ParameterScalar (n := n) (k := k) ell :=
  eval ell (ambientCoordinates ell a) (ambientCoordinates_pow ell a ha)

@[simp] theorem ambientSlot_coordinate (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (v : AmbientVar n) :
    ambientSlot ell a ha (coordinate ell v) = ambientCoordinates (n := n) ell a v :=
  eval_coordinate ell _ _ _

theorem graphCoordinates_constant_zero (D : FormalData (k := k) n) (v : AmbientVar n) :
    MvPowerSeries.constantCoeff (graphCoordinates n D.Y v) = 0 := by
  cases v with
  | inl i => simp [graphCoordinates]
  | inr c => exact graph_constant_zero D c

def formalGraph (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := AmbientVar n) (k := k) ell →ₐ[k]
      Frobenius.Ring (ι := GraphVar n) (k := k) ell :=
  substitute ell (graphCoordinates n D.Y) (graphCoordinates_constant_zero D)

@[simp] theorem formalGraph_mk (D : FormalData (k := k) n) (p : MvPowerSeries (AmbientVar n) k) :
    formalGraph ell D (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPowerSeries.subst (graphCoordinates n D.Y) p) :=
  substitute_mk ell _ _ _

                                                                 
theorem graph_restriction_hom (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    (((normalPlane (n := n) ell).comp (movingChart ell D a ha)).restrictScalars k).comp
      (ambientSlot ell a ha) = (movingGraphSlot ell a ha false).comp (formalGraph ell D) := by
  refine algHom_ext (ι := AmbientVar n) (k := k)
    (S := ParameterScalar (n := n) (k := k) ell) ell _ _ ?_
  intro v
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, ambientSlot_coordinate,
    formalGraph, substitute_coordinate]
  cases v with
  | inl i =>
      change normalPlane ell (movingChart ell D a ha
        ((algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)) (a i))) = _
      rw [AlgHom.commutes, AlgHom.commutes]
      exact (movingGraphSlot_coordinate ell a ha false (.inl i)).symm
  | inr c =>
      change normalPlane ell (movingChart ell D a ha (coordinate ell c)) = _
      rw [movingChart_coordinate, movingChartCoordinate, map_add, normalPlane_fixedComplement, add_zero]
      exact AlgHom.congr_fun (normalPlane_movingGraphSlot ell a ha)
        (Ideal.Quotient.mk _ (D.Y c))

def movingPotential (D : FormalData (k := k) n) (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) : ParameterScalar (n := n) (k := k) ell :=
  ambientSlot ell a ha (Ideal.Quotient.mk _ (potential n D.P))

theorem movingPotential_graph_zero (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    normalPlane ell (movingChart ell D a ha (movingPotential ell D a ha)) = 0 := by
  have h := AlgHom.congr_fun (graph_restriction_hom ell D a ha)
    (Ideal.Quotient.mk _ (potential n D.P))
  change _ = 0
  simp only [AlgHom.comp_apply, formalGraph_mk, D.graph_zero, map_zero] at h
  exact h

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
open Frobenius
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

omit [Fact (Nat.Prime ell)] in
theorem partial_ambientCoordinates (a : SlopeVar d → ThreeParameters.Ring k)
    (i : InternalVar n) (v : AmbientVar n) :
    partialDeriv ell i (ambientCoordinates ell a v) =
      if v = .inr i then 1 else 0 := by
  cases v with
  | inl a => simp only [ambientCoordinates, Derivation.map_algebraMap, reduceCtorEq, ite_false]
  | inr c =>
      simp only [ambientCoordinates, coordinate, partial_coordinate, Sum.inr.injEq]
      by_cases h : i = c
      · simp [h]
      · simp [h, Ne.symm h]

                                                                                 
omit [Fact (Nat.Prime ell)] in
theorem parameter_chain_rule
    (f : Frobenius.Ring (ι := AmbientVar n) (k := k) ell →ₐ[k]
      ParameterScalar (n := n) (k := k) ell)
    (i : InternalVar n) (x : Frobenius.Ring (ι := AmbientVar n) (k := k) ell) :
    partialDeriv ell i (f x) =
      ∑ v : AmbientVar n, f (partialDeriv ell v x) * partialDeriv ell i (f (coordinate ell v)) := by
  let : Module k (ParameterScalar (n := n) (k := k) ell) :=
    @Algebra.toModule k (ParameterScalar (n := n) (k := k) ell) inferInstance inferInstance inferInstance
  exact derivation_chain_rule (S := ParameterScalar (n := n) (k := k) ell)
    (k := k) (ι := AmbientVar n) ell f
    ((partialDeriv (k := ThreeParameters.Ring k) ell i).restrictScalars k) x

theorem sum_mul_single {J R : Type*} [Fintype J] [DecidableEq J] [Semiring R]
    (u : J → R) (i : J) : (∑ v, u v * (if v = i then 1 else 0)) = u i := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

                                                                                             
theorem partial_ambientSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (i : InternalVar n) (x : Frobenius.Ring (ι := AmbientVar n) (k := k) ell) :
    partialDeriv ell i (ambientSlot ell a ha x) =
      ambientSlot ell a ha (partialDeriv ell (.inr i) x) := by
  have h := parameter_chain_rule ell (ambientSlot ell a ha) i x
  simp only [ambientSlot_coordinate, partial_ambientCoordinates] at h
  exact h.trans (sum_mul_single (fun v => ambientSlot ell a ha (partialDeriv ell v x)) (.inr i))

theorem movingPotential_restricted_partial (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (c : InternalVar n) :
    normalPlane ell (movingChart ell D a ha (partialDeriv ell c (movingPotential ell D a ha))) =
      movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (restrictedGradient n D.P D.Y c)) := by
  rw [movingPotential, partial_ambientSlot, partial_mk]
  have h := AlgHom.congr_fun (graph_restriction_hom ell D a ha)
    (Ideal.Quotient.mk _ (MvPowerSeries.pderiv (.inr c) (potential n D.P)))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, formalGraph_mk] at h
  exact h

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
open Frobenius
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

@[simp] theorem normalPlane_slot_apply (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (x : Frobenius.Ring (ι := GraphVar n) (k := k) ell) :
    normalPlane ell (movingGraphSlot ell a ha false x) = movingGraphSlot ell a ha false x :=
  AlgHom.congr_fun (normalPlane_movingGraphSlot ell a ha) x

theorem movingPotential_mem_normalIdeal (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    movingPotential ell D a ha ∈
      chartNormalIdeal ell (movingChartEquiv ell htwo D a ha).symm normalIndices := by
  apply (chart_restriction_eq_zero_iff ell (Nat.Prime.pos Fact.out)
    (movingChartEquiv ell htwo D a ha).symm normalIndices _).mp
  exact movingPotential_graph_zero ell D a ha

                                                                            
                                                       
theorem graphIdeal_ambient_discrepancy (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (g : MvPowerSeries (GraphVar n) k) (hg : g ∈ gradientIdeal n D.P D.Y) :
    ∃ h : InternalVar n → ParameterScalar (n := n) (k := k) ell,
      ((movingChartEquiv ell htwo D a ha).symm
        (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ g)) -
        ∑ c, h c * partialDeriv ell c (movingPotential ell D a ha)) ∈
          chartNormalIdeal ell (movingChartEquiv ell htwo D a ha).symm normalIndices := by
  obtain ⟨h, hh⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
  let e := movingChartEquiv ell htwo D a ha
  refine ⟨fun c => e.symm (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (h c))), ?_⟩
  apply (chart_restriction_eq_zero_iff ell (Nat.Prime.pos Fact.out) e.symm normalIndices _).mp
  change normalPlane ell (e (e.symm (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ g)) -
    ∑ c, e.symm (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (h c))) *
      partialDeriv ell c (movingPotential ell D a ha))) = 0
  simp only [map_sub, map_sum, map_mul, AlgEquiv.apply_symm_apply, normalPlane_slot_apply]
  have he (x : ParameterScalar (n := n) (k := k) ell) : e x = movingChart ell D a ha x := rfl
  simp only [he, movingPotential_restricted_partial]
  apply sub_eq_zero.mpr
  simp only [← map_mul, ← map_sum]
  apply congrArg (movingGraphSlot ell a ha false)
  apply congrArg (Ideal.Quotient.mk (powerIdeal (k := k) ell))
  exact hh.symm

end BoundaryOnly.FormalObstruction

end

end OAI
