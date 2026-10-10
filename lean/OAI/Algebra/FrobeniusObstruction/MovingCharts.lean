import Mathlib
import OAI.Algebra.FrobeniusObstruction.TangentCharts
import OAI.Algebra.FrobeniusObstruction.VanishingIdeals

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
open Frobenius
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

                                                                             
def movingGraphCoordinates (a : SlopeVar d → ThreeParameters.Ring k) (b : Bool) :
    GraphVar n → Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell
  | .inl i => @algebraMap (ThreeParameters.Ring k)
      (Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell) inferInstance inferInstance inferInstance (a i)
  | .inr t => coordinate ell (b,t)

theorem movingGraphCoordinates_pow (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (b : Bool) (v : GraphVar n) :
    movingGraphCoordinates (n := n) ell a b v ^ ell = 0 := by
  cases v with
  | inl i =>
    change (@algebraMap (ThreeParameters.Ring k)
      (Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell) inferInstance inferInstance inferInstance (a i)) ^ ell = 0
    rw [← map_pow, ThreeParameters.augmentation_zero_pow k ell _ (ha i), map_zero]
  | inr t => exact coordinate_pow ell (b,t)

def movingGraphSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (b : Bool) :
    Frobenius.Ring (ι := GraphVar n) (k := k) ell →ₐ[k]
      Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell :=
  eval ell (movingGraphCoordinates ell a b) (movingGraphCoordinates_pow ell a ha b)

@[simp] theorem movingGraphSlot_coordinate (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (b : Bool) (v : GraphVar n) :
    movingGraphSlot ell a ha b (coordinate ell v) = movingGraphCoordinates ell a b v :=
  eval_coordinate ell _ _ _

theorem reduce_movingGraphSlot (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (b : Bool) :
    (reduction ell).comp (movingGraphSlot (n := n) ell a ha b) = graphSlot ell b := by
  apply algHom_ext
  intro v
  simp only [AlgHom.comp_apply, movingGraphSlot_coordinate]
  cases v with
  | inl i => simp [movingGraphCoordinates, ha]
  | inr t => simp [movingGraphCoordinates]

def movingChartCoordinate (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (c : InternalVar n) :
    Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell :=
  movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (D.Y c)) +
    baseChange (l := ThreeParameters.Ring k) ell (fixedComplement ell D c)

theorem movingChartCoordinate_pow (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (c : InternalVar n) :
    movingChartCoordinate ell D a ha c ^ ell = 0 := by
  let : CharP (Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell) ell :=
    quotient_charP (Nat.Prime.pos Fact.out)
  have h (c : InternalVar n) :
      (Ideal.Quotient.mk (powerIdeal (k := k) ell) (D.Y c)) ^ ell = 0 := by
    apply frobenius_zero_of_constant
    rw [constantHom_mk, graph_constant_zero D c]
    exact zero_pow (Nat.Prime.ne_zero Fact.out)
  have hslot (a : SlopeVar d → ThreeParameters.Ring k)
      (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (b : Bool) (c : InternalVar n) :
      (movingGraphSlot ell a ha b (Ideal.Quotient.mk _ (D.Y c))) ^ ell = 0 := by
    rw [← map_pow, h, map_zero]
  have hL : (baseChange (l := ThreeParameters.Ring k) ell (fixedComplement ell D c)) ^ ell = 0 := by
    rw [← map_pow, fixedComplement_pow, map_zero]
  change (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (D.Y c)) +
    baseChange (l := ThreeParameters.Ring k) ell (fixedComplement ell D c)) ^ ell = 0
  have hadd := add_pow_char
    (movingGraphSlot ell a ha false (Ideal.Quotient.mk _ (D.Y c)))
    (baseChange (l := ThreeParameters.Ring k) ell (fixedComplement ell D c)) ell
  exact hadd.trans (by rw [hslot, hL, zero_add])

def movingChart (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell →ₐ[ThreeParameters.Ring k]
      Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell :=
  eval ell (movingChartCoordinate ell D a ha) (movingChartCoordinate_pow ell D a ha)

@[simp] theorem movingChart_coordinate (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) (c : InternalVar n) :
    movingChart ell D a ha (coordinate ell c) = movingChartCoordinate ell D a ha c :=
  eval_coordinate ell _ _ _

theorem movingChart_specialFiber (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (x : Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell) :
    reduction ell (movingChart ell D a ha x) = specialChart ell D (reduction ell x) := by
  apply specialFiber_of_coordinates
  intro c
  rw [movingChart_coordinate, specialChart_coordinate, movingChartCoordinate, map_add]
  rw [reduction_baseChange]
  have h := AlgHom.congr_fun (reduce_movingGraphSlot (n := n) ell a ha false)
    (Ideal.Quotient.mk (powerIdeal (k := k) ell) (D.Y c))
  exact congrArg (fun x => x + fixedComplement ell D c) h

                                                                        
                                                                          
include htwo in
theorem movingChart_bijective (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    Function.Bijective (movingChart ell D a ha) :=
  bijective_of_specialFiber ell (movingChart ell D a ha) (specialChartEquiv ell htwo D)
    (movingChart_specialFiber ell D a ha)

def movingChartEquiv (D : FormalData (k := k) n)
    (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0) :
    Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell ≃ₐ[ThreeParameters.Ring k]
      Frobenius.Ring (ι := InternalVar n) (k := ThreeParameters.Ring k) ell :=
  AlgEquiv.ofBijective (movingChart ell D a ha) (movingChart_bijective ell htwo D a ha)

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι κ k : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing k]
variable (ell : ℕ) [CharP k ell] [Fact ell.Prime]

theorem centered_mk_pow (a : Series (ι := κ) (k := k))
    (ha : MvPowerSeries.constantCoeff a = 0) :
    (Ideal.Quotient.mk (powerIdeal (ι := κ) (k := k) ell) a) ^ ell = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply series_frobenius_mem
  rw [ha]
  exact zero_pow (Fact.out : ell.Prime).ne_zero

omit [DecidableEq ι] in
private theorem substitute_kernel (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (p : Series (ι := ι) (k := k)) (hp : p ∈ powerIdeal ell) :
    ((Ideal.Quotient.mkₐ k (powerIdeal (ι := κ) ell)).comp
      (MvPowerSeries.substAlgHom (R := k)
        (MvPowerSeries.hasSubst_of_constantCoeff_zero ha))) p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  simp only [map_sum, map_mul, map_pow, AlgHom.comp_apply, MvPowerSeries.substAlgHom_X]
  apply Finset.sum_eq_zero
  intro i _
  change _ * (Ideal.Quotient.mk (powerIdeal (ι := κ) (k := k) ell) (a i)) ^ ell = 0
  rw [centered_mk_pow ell (a i) (ha i), mul_zero]

                                                                                 
def substitute (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := κ) (k := k) ell :=
  Ideal.Quotient.liftₐ (powerIdeal (ι := ι) (k := k) ell)
    ((Ideal.Quotient.mkₐ k (powerIdeal (ι := κ) (k := k) ell)).comp
      (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)))
    (substitute_kernel ell a ha)

omit [DecidableEq ι] in
@[simp] theorem substitute_mk (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (p : Series (ι := ι) (k := k)) :
    substitute ell a ha (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPowerSeries.subst a p) := by
  change Ideal.Quotient.mk _ (MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) p) = _
  rw [MvPowerSeries.substAlgHom_apply]

omit [DecidableEq ι] in
@[simp] theorem substitute_coordinate (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : ι) :
    substitute ell a ha (coordinate ell i) = Ideal.Quotient.mk _ (a i) := by
  rw [coordinate, substitute_mk, MvPowerSeries.subst_X
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]

                                                                         
                               
theorem substitute_eq_eval (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    substitute ell a ha = eval ell
      (fun i => Ideal.Quotient.mk (powerIdeal (ι := κ) (k := k) ell) (a i))
      (fun i => centered_mk_pow ell (a i) (ha i)) := by
  apply algHom_ext
  intro i
  rw [substitute_coordinate, eval_coordinate]

                                                                           
                                                                                
theorem eval_substitute {S : Type*} [CommRing S] [Algebra k S]
    (a : ι → Series (ι := κ) (k := k))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (b : κ → S) (hb : ∀ j, b j ^ ell = 0)
    (x : Ring (ι := ι) (k := k) ell) :
    eval ell b hb (substitute ell a ha x) =
      eval ell (fun i => eval ell b hb (Ideal.Quotient.mk _ (a i)))
        (fun i => by
          rw [← map_pow, centered_mk_pow ell (a i) (ha i), map_zero]) x := by
  have h : (eval ell b hb).comp (substitute ell a ha) =
      eval ell (fun i => eval ell b hb (Ideal.Quotient.mk _ (a i)))
        (fun i => by rw [← map_pow, centered_mk_pow ell (a i) (ha i), map_zero]) := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, substitute_coordinate, eval_coordinate]
  exact AlgHom.congr_fun h x

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]
variable (ell : ℕ) (hell : 0 < ell)

noncomputable def planeRestriction (s : Finset ι) :
    Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell :=
  eval ell (fun i => if i ∈ s then 0 else coordinate ell i) (by
    intro i
    split_ifs
    · exact zero_pow (by omega)
    · exact coordinate_pow ell i)

@[simp] theorem planeRestriction_coordinate (s : Finset ι) (i : ι) :
    planeRestriction ell hell s (coordinate (k := k) ell i) =
      if i ∈ s then 0 else coordinate ell i := by
  exact eval_coordinate _ _ _ _

noncomputable def coordinatePlaneIdeal (s : Finset ι) : Ideal (Ring (ι := ι) (k := k) ell) :=
  Ideal.span (coordinate ell '' (s : Set ι))

theorem coordinatePlaneIdeal_le_ker (s : Finset ι) :
    coordinatePlaneIdeal (k := k) ell s ≤ RingHom.ker (planeRestriction (k := k) ell hell s) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  change planeRestriction (k := k) ell hell s (coordinate ell i) = 0
  change i ∈ s at hi
  simp only [planeRestriction_coordinate, ite_eq_left hi]

theorem planeRestriction_mod_ideal (s : Finset ι) :
    (Ideal.Quotient.mkₐ k (coordinatePlaneIdeal (k := k) ell s)).comp
      (planeRestriction ell hell s) = Ideal.Quotient.mkₐ k (coordinatePlaneIdeal (k := k) ell s) := by
  refine algHom_ext (ι := ι) (k := k)
    (S := Ring (ι := ι) (k := k) ell ⧸ coordinatePlaneIdeal (k := k) ell s) ell _ _ ?_
  intro i
  simp only [AlgHom.comp_apply, planeRestriction_coordinate]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,hi,rfl⟩)
  · rw [ite_eq_right hi]

                                                         
theorem planeRestriction_eq_zero_iff (s : Finset ι) (x : Ring (ι := ι) (k := k) ell) :
    planeRestriction ell hell s x = 0 ↔ x ∈ coordinatePlaneIdeal ell s := by
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := AlgHom.congr_fun (planeRestriction_mod_ideal (k := k) ell hell s) x
    simp only [AlgHom.comp_apply, hx, map_zero] at h
    exact h.symm
  · intro hx
    exact coordinatePlaneIdeal_le_ker ell hell s hx

def chartNormalIdeal (f : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) : Ideal (Ring (ι := ι) (k := k) ell) :=
  Ideal.span ((fun i => f (coordinate ell i)) '' (s : Set ι))

                                                                             
omit [Fintype ι] [DecidableEq ι] in
theorem chartNormalIdeal_mem_iff
    (f : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (x : Ring (ι := ι) (k := k) ell) :
    x ∈ chartNormalIdeal ell f s ↔ f.symm x ∈ coordinatePlaneIdeal ell s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      simp only [AlgEquiv.symm_apply_apply]
      exact Ideal.subset_span ⟨i,hi,rfl⟩
    | zero => simpa only [map_zero] using (coordinatePlaneIdeal (k := k) ell s).zero_mem
    | add a b ha hb hfa hfb =>
      rw [map_add]; exact (coordinatePlaneIdeal ell s).add_mem hfa hfb
    | smul a b hb hfb =>
      change f.symm (a*b) ∈ _
      rw [map_mul]; exact Ideal.mul_mem_left _ _ hfb
  · intro hx
    have H : ∀ y ∈ coordinatePlaneIdeal (k := k) ell s, f y ∈ chartNormalIdeal ell f s := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i,hi,rfl⟩ := hy
        exact Ideal.subset_span ⟨i,hi,rfl⟩
      | zero => simpa only [map_zero] using (chartNormalIdeal ell f s).zero_mem
      | add a b ha hb hfa hfb =>
        rw [map_add]; exact (chartNormalIdeal ell f s).add_mem hfa hfb
      | smul a b hb hfb =>
        change f (a*b) ∈ _
        rw [map_mul]; exact Ideal.mul_mem_left _ _ hfb
    simpa only [AlgEquiv.apply_symm_apply] using H (f.symm x) hx

theorem chart_restriction_eq_zero_iff
    (f : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell)
    (s : Finset ι) (x : Ring (ι := ι) (k := k) ell) :
    planeRestriction ell hell s (f.symm x) = 0 ↔ x ∈ chartNormalIdeal ell f s := by
  rw [planeRestriction_eq_zero_iff, chartNormalIdeal_mem_iff]

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
