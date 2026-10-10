import Mathlib
import OAI.Algebra.FrobeniusObstruction.ActualBlocks

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.ActualBlocks
open Frobenius MixedForms FormsSplit GlobalForms SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) [Fact ell.Prime] [CharP k ell] (hchar : 2 < ell)

 theorem selected_block_cycles (hd : 5 ≤ d) (D : FormalData (k := k) n) :
    ∃ (v : Ext (k := k) (ι := InternalVar n) →ₗ[k] k)
      (J : Finset (Fin d)) (x : ∀ i, Block (n := n) (k := k) ell i),
      3 ≤ J.card ∧
      (∀ i, delta (partialDeriv ell) (blockPotential ell D i) (x i) = 0) ∧
      (∀ i ∈ J, ∃ y : Block (n := n) (k := k) ell i,
        delta (partialDeriv ell) (blockPotential ell D i) y =
          -delta (partialDeriv ell) (blockSlope ell D i) (x i)) ∧
      fixedResidue (quotientCoeff ell (topExponent ell) (topExponent_good (by omega))) v
        (specialNormal ell (by omega) D *
          (List.ofFn fun i => includeBlock ell i (x i)).prod) ≠ 0 := by
  let hell : 0 < ell := by omega
  let htwo : 1 < ell := by omega
  have htwoK : (2 : k) ≠ 0 := by
    intro h
    have hv : ell ∣ 2 := (CharP.cast_eq_zero_iff k ell 2).mp (by simpa using h)
    have := Nat.le_of_dvd (by omega : 0 < 2) hv
    omega
  obtain ⟨v,hpair⟩ := specialNormal_pairing ell htwo D
  let alpha := specialNormal ell htwo D
  let beta := negativeNormal ell htwo D
  let e := tensorToForms (n := n) (k := k) ell hell
  let pd := fun i : Fin d => partialDeriv (ι := Variables n i) (k := k) ell
  let q := blockPotential ell D
  let s := blockSlope ell D
  let rho := quotientCoeff (ι := InternalVar n) (k := k) ell (topExponent ell) (topExponent_good hell)
  let Φ : (⨂[k] i, Block (n := n) (k := k) ell i) →ₗ[k] k :=
    (fixedResidue rho v).comp (((Algebra.lmul k _).toLinearMap alpha).comp e.toLinearMap)
  have heD (z : ⨂[k] i, Block (n := n) (k := k) ell i) :
      e (differential (Block (n := n) (k := k) ell) BlockTensor.P (BlockTensor.D pd) z) =
        MixedForms.d (partialDeriv ell) (e z) := tensorToForms_D ell hell z
  have heδ (z : ⨂[k] i, Block (n := n) (k := k) ell i) :
      e (differential (Block (n := n) (k := k) ell) BlockTensor.P (BlockTensor.delta pd q) z) =
        delta (partialDeriv ell) (specialPotential ell D) (e z) := tensorToForms_delta ell hell D z
  have hPhiD (z) : Φ (differential (Block (n := n) (k := k) ell) BlockTensor.P (BlockTensor.D pd) z) = 0 := by
    change fixedResidue rho v (alpha * e _) = 0
    rw [heD]
    exact fixedResidue_mul_d (partialDeriv ell) rho v (residue_partial_zero ell hell)
      alpha (e z) (specialNormal_d ell htwo D)
  have hPhiδ (z) : Φ (differential (Block (n := n) (k := k) ell) BlockTensor.P (BlockTensor.delta pd q) z) = 0 := by
    change fixedResidue rho v (alpha * e _) = 0
    rw [heδ, left_cycle_mul_delta _ _ _ _ (specialNormal_delta ell htwo D), map_zero]
  have hz : differential (Block (n := n) (k := k) ell) BlockTensor.P
      (BlockTensor.delta pd q) (e.symm beta) = 0 := by
    apply e.injective
    rw [heδ, e.apply_symm_apply, LinearEquiv.map_zero]
    exact negativeNormal_delta ell htwo D
  have hDz : differential (Block (n := n) (k := k) ell) BlockTensor.P
      (BlockTensor.D pd) (e.symm beta) = 0 := by
    apply e.injective
    rw [heD, e.apply_symm_apply, LinearEquiv.map_zero]
    exact negativeNormal_d ell htwo D
  have hPhiz : Φ (e.symm beta) ≠ 0 := by
    change fixedResidue rho v (alpha * e (e.symm beta)) ≠ 0
    rw [e.apply_symm_apply]
    exact hpair
  have htriple (I : Finset (Fin d)) (_hi : I ⊆ Finset.univ) (hI : I.card = 3) :
      ∃ y, tensorAction (Block (n := n) (k := k) ell) (BlockTensor.S s) I (e.symm beta) =
        differential (Block (n := n) (k := k) ell) BlockTensor.P (BlockTensor.delta pd q) y := by
    obtain ⟨i,j,l,hij,hil,hjl,rfl⟩ := Finset.card_eq_three.mp hI
    obtain ⟨eta,heta⟩ := negativeNormal_triple ell htwo D i j l
    refine ⟨e.symm eta, ?_⟩
    apply e.injective
    rw [heδ, e.apply_symm_apply]
    change tensorToForms ell hell (tensorAction _ _ _ _) = _
    rw [tensorToForms_S]
    change coeff _ * e (e.symm beta) = _
    rw [e.apply_symm_apply]
    dsimp only [s]
    simpa [hij, hil, hjl, beta, mul_assoc] using heta.symm
  obtain ⟨J,x,_hJ,hJcard,hx,hy,hΦx⟩ := BlockTensor.selected_cycles pd q htwoK
    (fun i a b z => partial_commute ell a b z) s Finset.univ
    (by simpa using hd) Φ hPhiδ hPhiD (e.symm beta) hz hDz hPhiz htriple
  refine ⟨v,J,x,hJcard,hx,hy,?_⟩
  change fixedResidue rho v (alpha * e (PiTensorProduct.tprod k x)) ≠ 0 at hΦx
  simpa only [e, tensorToForms_tprod] using hΦx

end BoundaryOnly.FormalObstruction.ActualBlocks

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
open scoped BigOperators
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) [Fact ell.Prime] [CharP k ell]

 def firstSlopes (s : Fin d → ThreeParameters.Ring k) : SlopeVar d → ThreeParameters.Ring k :=
  fun ij => if ij.2 = 0 then s ij.1 else 0

 theorem firstSlopes_augmentation (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0) (ij : SlopeVar d) :
    ThreeParameters.augmentation k (firstSlopes s ij) = 0 := by
  dsimp [firstSlopes]
  split_ifs <;> simp only [hs, map_zero]

 theorem zeroSlopes_constant_zero (i : Fin d) (j : WallVar n i) :
    MvPowerSeries.constantCoeff (zeroSlopes (k := k) n i j) = 0 := by
  cases j <;> simp [zeroSlopes]

 theorem wallSpecial_zeroSlopes (b : Bool) (i : Fin d)
    (p : MvPowerSeries (WallVar n i) k) :
    wallSpecial (n := n) (k := k) ell b i (Ideal.Quotient.mk _ p) =
      includeVariables (k := k) ell (fun y => (b,⟨i,y⟩))
        (Ideal.Quotient.mk _ (MvPowerSeries.subst (zeroSlopes n i) p)) := by
  have h : wallSpecial (n := n) (k := k) ell b i =
      (includeVariables (k := k) ell (fun y : Fin (n i) => ((b,⟨i,y⟩) : InternalVar n))).comp
        (substitute ell (zeroSlopes n i) (zeroSlopes_constant_zero i)) := by
    apply Frobenius.algHom_ext (ι := WallVar n i) (k := k) ell
    intro j
    simp only [AlgHom.comp_apply, substitute_coordinate]
    cases j with
    | inl j => simp only [zeroSlopes, map_zero, wallSpecial_slope]
    | inr y =>
      rw [wallSpecial_internal]
      change coordinate ell (b,⟨i,y⟩) =
        includeVariables (k := k) ell (fun y : Fin (n i) => ((b,⟨i,y⟩) : InternalVar n))
          (coordinate ell y)
      exact (includeVariables_coordinate (k := k) ell
        (fun y : Fin (n i) => ((b,⟨i,y⟩) : InternalVar n)) y).symm
  rw [h, AlgHom.comp_apply, substitute_mk]

 theorem wallSpecial_slopePartial (D : FormalData (k := k) n) (b : Bool) (i : Fin d) :
    wallSpecial ell b i (partialDeriv ell (.inl 0) (Ideal.Quotient.mk _ (D.P i))) =
      specialSlope ell D b i := by
  rw [partial_mk, wallSpecial_zeroSlopes]
  rfl

 def movingWall (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0) (i : Fin d) :
    Frobenius.Ring (ι := WallVar n i) (k := k) ell →ₐ[k]
      ParameterScalar (n := n) (k := k) ell :=
  (ambientSlot ell (firstSlopes s) (firstSlopes_augmentation s hs)).comp
    (substitute ell (plusCoordinates n i) (plusCoordinates_constant_zero i))

 @[simp] theorem movingWall_slope (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0) (i : Fin d) (j : Fin 3) :
    movingWall (n := n) ell s hs i (coordinate ell (.inl j)) =
      if j = 0 then @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
        inferInstance inferInstance inferInstance (s i) else 0 := by
  simp only [movingWall, AlgHom.comp_apply, substitute_coordinate, plusCoordinates]
  change ambientSlot ell _ _ (coordinate ell (.inl (i,j))) = _
  rw [ambientSlot_coordinate]
  change @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
      inferInstance inferInstance inferInstance (if j = 0 then s i else 0) = _
  split_ifs <;> simp only [map_zero]

 @[simp] theorem movingWall_internal (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0) (i : Fin d) (y : Fin (n i)) :
    movingWall (n := n) ell s hs i (coordinate ell (.inr y)) = coordinate ell (true,⟨i,y⟩) := by
  simp only [movingWall, AlgHom.comp_apply, substitute_coordinate, plusCoordinates]
  exact ambientSlot_coordinate ell _ _ _

 theorem movingWall_first_order (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0)
    (hs2 : ∀ i, s i * s i = 0) (i : Fin d)
    (x : Frobenius.Ring (ι := WallVar n i) (k := k) ell) :
    movingWall ell s hs i x =
      baseChange (k := k) (l := ThreeParameters.Ring k) ell (wallSpecial ell true i x) +
      (@algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
        inferInstance inferInstance inferInstance (s i)) *
        baseChange (k := k) (l := ThreeParameters.Ring k) ell
          (wallSpecial ell true i (partialDeriv ell (.inl 0) x)) := by
  let f := (baseChange (ι := InternalVar n) (k := k) (l := ThreeParameters.Ring k) ell).comp
    (wallSpecial ell true i)
  refine evaluation_first_order ell f (movingWall ell s hs i) (.inl 0)
    (@algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
      inferInstance inferInstance inferInstance (s i)) ?_ ?_ x
  · rw [← map_mul, hs2, map_zero]
  · intro j
    cases j with
    | inl j =>
      simp only [movingWall_slope, f, AlgHom.comp_apply, wallSpecial_slope, map_zero, zero_add,
        Sum.inl.injEq]
      simp only [eq_comm]
    | inr y =>
      simp only [movingWall_internal, f, AlgHom.comp_apply, wallSpecial_internal,
        baseChange_coordinate, Sum.inl_ne_inr, ite_false, add_zero]

 theorem ambientSlot_minus (a : SlopeVar d → ThreeParameters.Ring k)
    (ha : ∀ i, ThreeParameters.augmentation k (a i) = 0)
    (i : Fin d) (p : MvPowerSeries (WallVar n i) k) :
    ambientSlot (n := n) ell a ha
      (Ideal.Quotient.mk _ (MvPowerSeries.subst (minusCoordinates n i) p)) =
      baseChange (k := k) (l := ThreeParameters.Ring k) ell (wallSpecial ell false i (Ideal.Quotient.mk _ p)) := by
  have h : (ambientSlot (n := n) ell a ha).comp
      (substitute (k := k) ell (minusCoordinates n i) (minusCoordinates_constant_zero i)) =
      (baseChange (ι := InternalVar n) (k := k) (l := ThreeParameters.Ring k) ell).comp
        (wallSpecial (n := n) (k := k) ell false i) := by
    refine Frobenius.algHom_ext (ι := WallVar n i) (k := k)
      (S := ParameterScalar (n := n) (k := k) ell) ell _ _ ?_
    intro j
    simp only [AlgHom.comp_apply, substitute_coordinate]
    cases j with
    | inl j => simp only [minusCoordinates, map_zero, wallSpecial_slope]
    | inr y =>
      rw [wallSpecial_internal, baseChange_coordinate]
      exact ambientSlot_coordinate ell _ _ _
  simpa only [AlgHom.comp_apply, substitute_mk] using AlgHom.congr_fun h (Ideal.Quotient.mk _ p)

                                                                        
                                                                        
 theorem movingPotential_first_order (D : FormalData (k := k) n)
    (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0)
    (hs2 : ∀ i, s i * s i = 0) :
    movingPotential ell D (firstSlopes s) (firstSlopes_augmentation s hs) =
      ∑ i, (baseChange (k := k) (l := ThreeParameters.Ring k) ell
          (wallSpecial ell true i (Ideal.Quotient.mk _ (D.P i)) -
            wallSpecial ell false i (Ideal.Quotient.mk _ (D.P i))) +
        @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
          inferInstance inferInstance inferInstance (s i) *
            baseChange (k := k) (l := ThreeParameters.Ring k) ell (specialSlope ell D true i)) := by
  simp only [movingPotential, potential, map_sum, map_sub, ambientSlot_minus]
  apply Finset.sum_congr rfl
  intro i _
  have hh := movingWall_first_order (n := n) ell s hs hs2 i (Ideal.Quotient.mk _ (D.P i))
  change ambientSlot ell (firstSlopes s) (firstSlopes_augmentation s hs)
    (substitute ell (plusCoordinates n i) (plusCoordinates_constant_zero i)
      (Ideal.Quotient.mk _ (D.P i))) = _ at hh
  rw [substitute_mk, wallSpecial_slopePartial] at hh
  rw [hh]
  ring

end BoundaryOnly.FormalObstruction

end

end OAI
