import Mathlib
import OAI.Algebra.FrobeniusObstruction.GraphPotential
import OAI.Algebra.FrobeniusObstruction.GlobalForms

namespace OAI

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction.Frobenius
open MixedForms
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]
variable (ell : ℕ) [CharP k ell]

                                                                                     
def normalCoordinateList
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) : List (Ring (ι := ι) (k := k) ell) :=
  s.toList.map (fun i => e (coordinate ell i))

omit [Fintype ι] [DecidableEq ι] [CharP k ell] in
theorem normalCoordinateList_span
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) : Ideal.span {u | u ∈ normalCoordinateList ell e s} =
      chartNormalIdeal ell e s := by
  congr 1
  ext u
  simp only [normalCoordinateList, List.mem_map, Finset.mem_toList,
    Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]

omit [Fintype ι] [DecidableEq ι] [CharP k ell] in
theorem normalCoordinateList_pow (hell : 0 < ell)
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (u : Ring (ι := ι) (k := k) ell)
    (hu : u ∈ normalCoordinateList ell e s) : u ^ (ell-1+1) = 0 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
  rw [Nat.sub_add_cancel hell, ← map_pow, coordinate_pow, map_zero]

def chartNormal
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) : Forms (k := k) (A := Ring (ι := ι) (k := k) ell) (ι := ι) :=
  normal (partialDeriv ell) (ell-1) (normalCoordinateList ell e s)

theorem chartNormal_d
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) : d (partialDeriv ell) (chartNormal ell e s) = 0 :=
  d_normal _ (partial_commute ell) _ _

theorem chartNormal_annihilate (hell : 0 < ell)
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (g : Ring (ι := ι) (k := k) ell)
    (hg : g ∈ chartNormalIdeal ell e s) : coeff g * chartNormal ell e s = 0 :=
  coeff_mul_normal_ideal _ _ _ (normalCoordinateList_pow ell hell e s) g
    (by rwa [normalCoordinateList_span])

theorem chartNormal_delta (hell : 0 < ell)
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (F : Ring (ι := ι) (k := k) ell)
    (hF : F ∈ chartNormalIdeal ell e s) :
    delta (partialDeriv ell) F (chartNormal ell e s) = 0 :=
  delta_normal _ _ _ (normalCoordinateList_pow ell hell e s) F
    (by rwa [normalCoordinateList_span])

theorem chartNormal_primitive (hell : 0 < ell)
    (e : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (F g : Ring (ι := ι) (k := k) ell)
    (h : ι → Ring (ι := ι) (k := k) ell)
    (hF : F ∈ chartNormalIdeal ell e s)
    (hg : g - ∑ i, h i * partialDeriv ell i F ∈ chartNormalIdeal ell e s) :
    coeff g * chartNormal ell e s = delta (partialDeriv ell) F
      (∑ i, coeff (h i) * contract i (chartNormal ell e s)) :=
  normal_primitive _ _ _ (normalCoordinateList_pow ell hell e s) F g h
    (by rwa [normalCoordinateList_span]) (by rwa [normalCoordinateList_span])

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

                                                                                  
                                                                              
abbrev ParameterForms := Forms (k := k)
  (A := ParameterScalar (n := n) (k := k) ell) (ι := InternalVar n)

def parameterPartial (i : InternalVar n) :
    Derivation k (ParameterScalar (n := n) (k := k) ell)
      (ParameterScalar (n := n) (k := k) ell) :=
  (partialDeriv (k := ThreeParameters.Ring k) ell i).restrictScalars k

omit [Fact ell.Prime] in
@[simp] theorem parameterPartial_apply (i : InternalVar n)
    (x : ParameterScalar (n := n) (k := k) ell) :
    parameterPartial ell i x = partialDeriv ell i x := rfl

omit [Fact ell.Prime] in
theorem parameterPartial_commute (i j : InternalVar n)
    (x : ParameterScalar (n := n) (k := k) ell) :
    parameterPartial ell i (parameterPartial ell j x) =
    parameterPartial ell j (parameterPartial ell i x) := partial_commute ell i j x

def movingNormal (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    ParameterForms (n := n) (k := k) ell :=
  normal (parameterPartial ell) (ell-1)
    (normalCoordinateList ell (movingChartEquiv ell htwo D a ha).symm normalIndices)

theorem movingNormal_d (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    MixedForms.d (parameterPartial ell) (movingNormal ell htwo D a ha) = 0 :=
  d_normal _ (parameterPartial_commute ell) _ _

theorem movingNormal_delta (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    delta (parameterPartial ell) (movingPotential ell D a ha)
      (movingNormal ell htwo D a ha) = 0 :=
  delta_normal _ _ _ (normalCoordinateList_pow ell (Nat.Prime.pos Fact.out) _ _)
    _ (by rw [normalCoordinateList_span]; exact movingPotential_mem_normalIdeal ell htwo D a ha)

theorem movingNormal_annihilate (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (g : ParameterScalar (n := n) (k := k) ell)
    (hg : g ∈ chartNormalIdeal ell (movingChartEquiv ell htwo D a ha).symm normalIndices) :
    coeff g * movingNormal ell htwo D a ha = 0 :=
  coeff_mul_normal_ideal _ _ _ (normalCoordinateList_pow ell (Nat.Prime.pos Fact.out) _ _)
    g (by rwa [normalCoordinateList_span])

                                                                                 
theorem movingNormal_primitive (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (g : MvPowerSeries (GraphVar n) k) (hg : g ∈ gradientIdeal n D.P D.Y) :
    ∃ eta : ParameterForms (n := n) (k := k) ell,
      delta (parameterPartial ell) (movingPotential ell D a ha) eta =
        coeff ((movingChartEquiv ell htwo D a ha).symm
          (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ g))) *
            movingNormal ell htwo D a ha := by
  obtain ⟨h, hh⟩ := graphIdeal_ambient_discrepancy ell htwo D a ha g hg
  refine ⟨∑ i, coeff (h i) * contract i (movingNormal ell htwo D a ha), ?_⟩
  apply Eq.symm
  apply normal_primitive _ _ _ (normalCoordinateList_pow ell (Nat.Prime.pos Fact.out) _ _) _ _ h
  · rw [normalCoordinateList_span]; exact movingPotential_mem_normalIdeal ell htwo D a ha
  · rw [normalCoordinateList_span]; exact hh

                                                                           
theorem movingNormal_cubic_primitive (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (i j l : Fin d) :
    ∃ eta : ParameterForms (n := n) (k := k) ell,
      delta (parameterPartial ell) (movingPotential ell D a ha) eta =
        coeff (@algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
          inferInstance inferInstance inferInstance (a (i,0) * a (j,0) * a (l,0))) *
            movingNormal ell htwo D a ha := by
  obtain ⟨eta, he⟩ := movingNormal_primitive ell htwo D a ha
    (slope n i * slope n j * slope n l) (D.positive_cubic i j l)
  have hs : (movingChartEquiv ell htwo D a ha).symm
      (movingGraphSlot ell a ha false
        (Ideal.Quotient.mk _ (slope n i * slope n j * slope n l))) =
      @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
        inferInstance inferInstance inferInstance (a (i,0) * a (j,0) * a (l,0)) := by
    simp only [map_mul, slope]
    change (movingChartEquiv ell htwo D a ha).symm
      (movingGraphSlot ell a ha false (coordinate ell (.inl (i,0)))) *
        (movingChartEquiv ell htwo D a ha).symm
          (movingGraphSlot ell a ha false (coordinate ell (.inl (j,0)))) *
        (movingChartEquiv ell htwo D a ha).symm
          (movingGraphSlot ell a ha false (coordinate ell (.inl (l,0)))) = _
    simp only [movingGraphSlot_coordinate, movingGraphCoordinates, AlgEquiv.commutes]
  rw [hs] at he
  exact ⟨eta, he⟩

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k l : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [CommRing l]
variable (ell : ℕ) [CharP k ell] [CharP l ell]

omit [Fintype ι] [DecidableEq ι] [CharP k ell] [CharP l ell] in
theorem series_pderiv_map (f : k →+* l) (i : ι) (x : Series (ι := ι) (k := k)) :
    MvPowerSeries.map f (MvPowerSeries.pderiv i x) =
      MvPowerSeries.pderiv i (MvPowerSeries.map f x) := by
  ext e
  simp only [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, map_mul, map_add, map_natCast, map_one]

omit [DecidableEq ι] in
theorem mapCoefficients_partial (f : k →+* l) (i : ι)
    (x : Ring (ι := ι) (k := k) ell) :
    mapCoefficients ell f (partialDeriv ell i x) =
      partialDeriv ell i (mapCoefficients ell f x) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [partial_mk, mapCoefficients_mk, series_pderiv_map]

variable [Algebra k l]
omit [DecidableEq ι] in
theorem baseChange_partial (i : ι)
    (x : Ring (ι := ι) (k := k) ell) :
    baseChange (l := l) ell (partialDeriv ell i x) =
      partialDeriv ell i (baseChange (l := l) ell x) :=
  mapCoefficients_partial ell (algebraMap k l) i x

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.MixedForms
open scoped TensorProduct
variable {k A B ι : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Fintype ι] [DecidableEq ι]

                                                         
def coefficientMap (f : A →ₐ[k] B) :
    Forms (k := k) (A := A) (ι := ι) →ₐ[k] Forms (k := k) (A := B) (ι := ι) :=
  Algebra.TensorProduct.map f (AlgHom.id k _)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coefficientMap_tmul (f : A →ₐ[k] B)
    (a : A) (e : Ext (k := k) (ι := ι)) :
    coefficientMap f (a ⊗ₜ[k] e) = f a ⊗ₜ[k] e := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coefficientMap_coeff (f : A →ₐ[k] B) (a : A) :
    coefficientMap (ι := ι) f (coeff a) = coeff (f a) := rfl

 theorem coefficientMap_d (f : A →ₐ[k] B)
    (pA : ι → Derivation k A A) (pB : ι → Derivation k B B)
    (hp : ∀ i a, f (pA i a) = pB i (f a))
    (x : Forms (k := k) (A := A) (ι := ι)) :
    coefficientMap f (d pA x) = d pB (coefficientMap f x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp only [d_tmul, coefficientMap_tmul, map_sum, hp]

 theorem coefficientMap_gradient (f : A →ₐ[k] B)
    (pA : ι → Derivation k A A) (pB : ι → Derivation k B B)
    (hp : ∀ i a, f (pA i a) = pB i (f a)) (F : A) :
    coefficientMap f (gradient pA F) = gradient pB (f F) := by
  exact coefficientMap_d f pA pB hp (coeff F)

 theorem coefficientMap_delta (f : A →ₐ[k] B)
    (pA : ι → Derivation k A A) (pB : ι → Derivation k B B)
    (hp : ∀ i a, f (pA i a) = pB i (f a)) (F : A)
    (x : Forms (k := k) (A := A) (ι := ι)) :
    coefficientMap f (delta pA F x) = delta pB (f F) (coefficientMap f x) := by
  simp only [delta_apply, map_mul, coefficientMap_gradient f pA pB hp]

 theorem coefficientMap_cartier (f : A →ₐ[k] B)
    (pA : ι → Derivation k A A) (pB : ι → Derivation k B B)
    (hp : ∀ i a, f (pA i a) = pB i (f a)) (e : ℕ) (u : A) :
    coefficientMap f (cartier pA e u) = cartier pB e (f u) := by
  simp only [cartier, map_mul, coefficientMap_coeff, map_pow,
    coefficientMap_gradient f pA pB hp]

 theorem coefficientMap_normal (f : A →ₐ[k] B)
    (pA : ι → Derivation k A A) (pB : ι → Derivation k B B)
    (hp : ∀ i a, f (pA i a) = pB i (f a)) (e : ℕ) (us : List A) :
    coefficientMap f (normal pA e us) = normal pB e (us.map f) := by
  induction us with
  | nil => simp only [normal, List.map_nil, List.prod_nil, map_one]
  | cons u us ih =>
      simpa only [normal, List.map_cons, List.prod_cons, map_mul,
        coefficientMap_cartier f pA pB hp] using congrArg
        (fun x => cartier pB e (f u) * x) ih

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

theorem movingChart_inverse_specialFiber (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (x : ParameterScalar (n := n) (k := k) ell) :
    reduction ell ((movingChartEquiv ell htwo D a ha).symm x) =
      (specialChartEquiv ell htwo D).symm (reduction ell x) := by
  apply (specialChartEquiv ell htwo D).injective
  rw [AlgEquiv.apply_symm_apply]
  change specialChart ell D (reduction ell ((movingChartEquiv ell htwo D a ha).symm x)) = _
  rw [← movingChart_specialFiber ell D a ha]
  change reduction ell ((movingChartEquiv ell htwo D a ha)
    ((movingChartEquiv ell htwo D a ha).symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

def specialNormal (D : FormalData (k := k) n) :
    Forms (k := k) (A := Frobenius.Ring (ι := InternalVar n) (k := k) ell)
      (ι := InternalVar n) :=
  chartNormal ell (specialChartEquiv ell htwo D).symm normalIndices

theorem reduce_normalList (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    (normalCoordinateList ell (movingChartEquiv ell htwo D a ha).symm normalIndices).map
      (reduction ell) = normalCoordinateList ell (specialChartEquiv ell htwo D).symm normalIndices := by
  simp only [normalCoordinateList, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, movingChart_inverse_specialFiber, reduction_coordinate]

theorem reduce_movingNormal (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    coefficientMap (reduction ell) (movingNormal ell htwo D a ha) =
      specialNormal ell htwo D := by
  have hp (i : InternalVar n) (x : ParameterScalar (n := n) (k := k) ell) :
      reduction ell (parameterPartial ell i x) = partialDeriv ell i (reduction ell x) :=
    mapCoefficients_partial ell (ThreeParameters.augmentation k) i x
  have hn := coefficientMap_normal (reduction (ι := InternalVar n) (k := k) ell)
    (parameterPartial ell) (partialDeriv ell) hp (ell-1)
    (normalCoordinateList ell (movingChartEquiv ell htwo D a ha).symm normalIndices)
  rw [reduce_normalList ell htwo D a ha] at hn
  exact hn

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

def specialAmbient : Frobenius.Ring (ι := AmbientVar n) (k := k) ell →ₐ[k]
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  eval ell (Sum.elim (fun _ => 0) (coordinate ell)) (by
    intro v
    cases v with
    | inl _ => exact zero_pow (Nat.Prime.ne_zero Fact.out)
    | inr c => exact coordinate_pow ell c)

omit [CharP k ell] in
@[simp] theorem specialAmbient_slope (i : SlopeVar d) :
    specialAmbient (n := n) (k := k) ell (coordinate ell (.inl i)) = 0 :=
  eval_coordinate _ _ _ _

omit [CharP k ell] in
@[simp] theorem specialAmbient_internal (i : InternalVar n) :
    specialAmbient (n := n) (k := k) ell (coordinate ell (.inr i)) = coordinate ell i :=
  eval_coordinate _ _ _ _

 theorem reduce_ambientSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (x : Frobenius.Ring (ι := AmbientVar n) (k := k) ell) :
    reduction ell (ambientSlot ell a ha x) = specialAmbient ell x := by
  have h : (reduction ell).comp (ambientSlot ell a ha) =
      specialAmbient (n := n) (k := k) ell := by
    apply algHom_ext
    intro v
    simp only [AlgHom.comp_apply, ambientSlot_coordinate]
    cases v with
    | inl i => simp only [ambientCoordinates, reduction_base, ha, map_zero, specialAmbient_slope]
    | inr c => simp only [ambientCoordinates, reduction_coordinate, specialAmbient_internal]
  exact AlgHom.congr_fun h x

def specialPotential (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  specialAmbient ell (Ideal.Quotient.mk _ (potential n D.P))

 theorem reduce_movingPotential (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    reduction ell (movingPotential ell D a ha) = specialPotential ell D :=
  reduce_ambientSlot ell a ha _

 theorem specialNormal_d (D : FormalData (k := k) n) :
    MixedForms.d (partialDeriv ell) (specialNormal ell htwo D) = 0 :=
  chartNormal_d ell _ _

omit [Fact ell.Prime] in
theorem parameter_reduction_partial (i : InternalVar n)
    (x : ParameterScalar (n := n) (k := k) ell) :
    reduction ell (parameterPartial ell i x) = partialDeriv ell i (reduction ell x) :=
  mapCoefficients_partial ell (ThreeParameters.augmentation k) i x

 theorem specialNormal_delta (D : FormalData (k := k) n) :
    delta (partialDeriv ell) (specialPotential ell D) (specialNormal ell htwo D) = 0 := by
  let a : SlopeVar d → ThreeParameters.Ring k := fun _ => 0
  have ha : ∀ i, ThreeParameters.augmentation k (a i) = 0 := fun _ => map_zero _
  have h := congrArg (coefficientMap (reduction ell)) (movingNormal_delta ell htwo D a ha)
  rw [coefficientMap_delta _ _ _ (parameter_reduction_partial ell),
    reduce_movingPotential, reduce_movingNormal, map_zero] at h
  exact h

                                                                                
theorem specialNormal_primitive (D : FormalData (k := k) n)
    (g : MvPowerSeries (GraphVar n) k) (hg : g ∈ gradientIdeal n D.P D.Y) :
    ∃ eta : Forms (k := k) (A := Frobenius.Ring (ι := InternalVar n) (k := k) ell)
        (ι := InternalVar n),
      delta (partialDeriv ell) (specialPotential ell D) eta =
        coeff ((specialChartEquiv ell htwo D).symm
          (graphSlot ell false (Ideal.Quotient.mk _ g))) * specialNormal ell htwo D := by
  let a : SlopeVar d → ThreeParameters.Ring k := fun _ => 0
  have ha : ∀ i, ThreeParameters.augmentation k (a i) = 0 := fun _ => map_zero _
  obtain ⟨eta, he⟩ := movingNormal_primitive ell htwo D a ha g hg
  refine ⟨coefficientMap (reduction ell) eta, ?_⟩
  have h := congrArg (coefficientMap (reduction ell)) he
  rw [coefficientMap_delta _ _ _ (parameter_reduction_partial ell),
    reduce_movingPotential, map_mul, coefficientMap_coeff,
    movingChart_inverse_specialFiber, reduce_movingNormal] at h
  have hr := AlgHom.congr_fun (reduce_movingGraphSlot ell a ha false)
    (Ideal.Quotient.mk _ g)
  change reduction ell (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ g)) = _ at hr
  rw [hr] at h
  exact h

end BoundaryOnly.FormalObstruction

end
end

end OAI
