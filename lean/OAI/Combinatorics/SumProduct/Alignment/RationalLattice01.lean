import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.TriangularDenominators01
import OAI.Geometry.NilpotentCharts.Coordinates
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace RationalLattice
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ}

def IsRational (c : RealCoordinates G n) (g : G) : Prop :=
  ∀ i, ∃ x : ℚ, (x : ℝ) = c.coord g i

lemma eval_rational {ι : Type*} (P : MvPolynomial ι ℚ) (x : ι → ℝ)
    (hx : ∀ i, ∃ q : ℚ, (q : ℝ) = x i) :
    ∃ q : ℚ, (q : ℝ) = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P := by
  classical
  let q : ι → ℚ := fun i => Classical.choose (hx i)
  have hq : (algebraMap ℚ ℝ) ∘ q = x := funext (fun i => Classical.choose_spec (hx i))
  refine ⟨MvPolynomial.eval q P,?_⟩
  simpa [hq] using (MvPolynomial.eval₂_comp (algebraMap ℚ ℝ) q P)

lemma rational_one (c : RealCoordinates G n) : IsRational c 1 := by
  intro i
  exact ⟨0,by simp [c.one_coord]⟩

lemma rational_mul (c : RealCoordinates G n) {g h : G}
    (hg : IsRational c g) (hh : IsRational c h) : IsRational c (g*h) := by
  intro i
  obtain ⟨a,ha⟩ := hg i
  obtain ⟨b,hb⟩ := hh i
  obtain ⟨e,he⟩ := eval_rational (c.correction i)
    (Sum.elim (fun j => c.coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => c.coord h ⟨j.val,lt_trans j.isLt i.isLt⟩))
    (by intro k; cases k with | inl j => exact hg _ | inr j => exact hh _)
  exact ⟨a+b+e,by rw [Rat.cast_add,Rat.cast_add,ha,hb,he,c.mul_coord]⟩

lemma rational_inv (c : RealCoordinates G n) {g : G} (hg : IsRational c g) :
    IsRational c g⁻¹ := by
  intro i
  have hpartial : ∀ j (hj : j < n), ∃ q : ℚ, (q : ℝ) = c.coord g⁻¹ ⟨j,hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      let i : Fin n := ⟨j,hj⟩
      obtain ⟨a,ha⟩ := hg i
      obtain ⟨e,he⟩ := eval_rational (c.correction i)
        (Sum.elim (fun k => c.coord g ⟨k.val,lt_trans k.isLt i.isLt⟩)
          (fun k => c.coord g⁻¹ ⟨k.val,lt_trans k.isLt i.isLt⟩))
        (by
          intro k
          cases k with
          | inl k => exact hg _
          | inr k => exact ih k.val k.isLt _)
      refine ⟨-(a+e),?_⟩
      have hmul := c.mul_coord g g⁻¹ i
      rw [mul_inv_cancel,c.one_coord,← ha,← he] at hmul
      rw [Rat.cast_neg,Rat.cast_add]
      change -((a : ℝ)+e) = c.coord g⁻¹ i
      linarith
  exact hpartial i.val i.isLt

def rationalSubgroup (c : RealCoordinates G n) : Subgroup G where
  carrier := IsRational c
  one_mem' := rational_one c
  mul_mem' := rational_mul c
  inv_mem' := rational_inv c

def qcoord (c : RealCoordinates G n) (g : rationalSubgroup c) (i : Fin n) : ℚ :=
  Classical.choose (g.property i)

lemma qcoord_spec (c : RealCoordinates G n) (g : rationalSubgroup c) (i : Fin n) :
    (qcoord c g i : ℝ) = c.coord g i := Classical.choose_spec (g.property i)

lemma qcoord_injective (c : RealCoordinates G n) : Function.Injective (qcoord c) := by
  intro g h heq
  apply Subtype.ext
  apply c.coord.injective
  funext i
  rw [← qcoord_spec c g i,← qcoord_spec c h i,heq]

lemma qcoord_continuous (c : RealCoordinates G n) (i : Fin n) :
    Continuous (fun g => qcoord c g i) := by
  apply Rat.isEmbedding_coe_real.isInducing.continuous_iff.mpr
  change Continuous (fun g : rationalSubgroup c => (qcoord c g i : ℝ))
  simp_rw [qcoord_spec]
  exact (continuous_apply i).comp (c.coord.continuous.comp continuous_subtype_val)

def rationalCoordinates (c : RealCoordinates G n) :
    TriangularDenominators.Coordinates (rationalSubgroup c) n where
  coord := qcoord c
  one_coord i := by
    apply Rat.cast_injective (α := ℝ)
    rw [qcoord_spec]
    exact (c.one_coord i).trans Rat.cast_zero.symm
  correction := c.correction
  mul_coord g h i := by
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add,Rat.cast_add,qcoord_spec,qcoord_spec,qcoord_spec]
    have hp := MvPolynomial.eval₂_comp (algebraMap ℚ ℝ)
      (Sum.elim (fun j => qcoord c g ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j => qcoord c h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i)
    have hcast (q : ℚ) : (algebraMap ℚ ℝ) q = (q : ℝ) := by simp
    simp only [hcast] at hp
    rw [hp]
    change c.coord ((g:G)*(h:G)) i = _
    rw [c.mul_coord]
    congr 2
    funext k
    cases k with
    | inl j => exact (qcoord_spec c g _).symm
    | inr j => exact (qcoord_spec c h _).symm

 

theorem rational_fg_discrete [IsTopologicalGroup G] (c : RealCoordinates G n)
    (H : Subgroup (rationalSubgroup c)) (hH : H.FG) : DiscreteTopology H := by
  obtain ⟨S,hS⟩ := hH
  rw [← hS]
  exact TriangularDenominators.closure_discrete (rationalCoordinates c)
    (qcoord_injective c) (qcoord_continuous c) S

end
end RationalLattice

namespace RationalLattice
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PreconnectedSpace G] [LocallyCompactSpace G] [T2Space G] {n : ℕ}

 

theorem finite_rational_extension (c : RealCoordinates G n) (Γ : Subgroup G)
    [DiscreteTopology Γ] (hΓrat : Γ ≤ rationalSubgroup c)
    (C : Set G) (hC : IsCompact C) (hreps : ∀ g : G, ∃ x ∈ C, x⁻¹*g ∈ Γ)
    (S : Finset G) (hSrat : ∀ g ∈ S, IsRational c g) :
    ∃ H : Subgroup G, Γ ≤ H ∧ (S : Set G) ⊆ H ∧ H ≤ rationalSubgroup c ∧
      DiscreteTopology H ∧ (Γ.subgroupOf H).FiniteIndex := by
  let H := Γ ⊔ Subgroup.closure (S : Set G)
  have hHrat : H ≤ rationalSubgroup c := by
    apply sup_le hΓrat
    rw [Subgroup.closure_le]
    exact hSrat
  have hH : H.FG := (CocompactLattice.fg_of_compact_reps Γ C hC hreps).sup ⟨S,rfl⟩
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let e := Subgroup.subgroupOfContinuousMulEquivOfLe hHrat
  have hqG : Group.FG (H.subgroupOf (rationalSubgroup c)) :=
    Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hq : (H.subgroupOf (rationalSubgroup c)).FG :=
    (Group.fg_iff_subgroup_fg _).mp hqG
  have hdq := rational_fg_discrete c _ hq
  have hd : DiscreteTopology H := e.discreteTopology_iff.mp hdq
  let : DiscreteTopology H := hd
  refine ⟨H,le_sup_left,?_,hHrat,hd,?_⟩
  · exact fun _ hg => Subgroup.mem_sup_right (Subgroup.subset_closure hg)
  · exact TriangularDenominators.finiteIndex_of_compact_reps Γ H le_sup_left C hC hreps

end
end RationalLattice
end
 

 
section
open scoped BigOperators
noncomputable section
namespace Polynomial
open scoped _root_.Polynomial
variable {K : Type*} [Field K] [CharZero K]

lemma exists_antidifference_monomial (i : ℕ) (a : K) :
    ∃ q : K[X], q.comp (1+_root_.Polynomial.X) - q = _root_.Polynomial.C a * _root_.Polynomial.X^i := by
  let b : K[X] := (_root_.Polynomial.bernoulli (i+1)).map (algebraMap ℚ K)
  have hb : b.comp (1+_root_.Polynomial.X) = b + _root_.Polynomial.C (i+1 : K) * _root_.Polynomial.X^i := by
    have h := congrArg (Polynomial.map (algebraMap ℚ K)) (_root_.Polynomial.bernoulli_comp_one_add_X (i+1))
    simpa [b, _root_.Polynomial.map_comp, nsmul_eq_mul] using h
  refine ⟨_root_.Polynomial.C (a / (i+1 : K)) * b,?_⟩
  rw [_root_.Polynomial.mul_comp,_root_.Polynomial.C_comp,hb]
  have hi : (i+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  calc
    _root_.Polynomial.C (a / (i+1 : K)) * (b + _root_.Polynomial.C (i+1 : K) * _root_.Polynomial.X^i) - _root_.Polynomial.C (a / (i+1 : K)) * b =
      (_root_.Polynomial.C (a / (i+1 : K)) * _root_.Polynomial.C (i+1 : K)) * _root_.Polynomial.X^i := by ring
    _ = _root_.Polynomial.C a * _root_.Polynomial.X^i := by rw [← _root_.Polynomial.C_mul,div_mul_cancel₀ _ hi]

 
theorem exists_antidifference (p : K[X]) : ∃ q : K[X],
    q.eval 0 = 0 ∧ q.comp (1+_root_.Polynomial.X) - q = p := by
  have hex : ∃ q : K[X], q.comp (1+_root_.Polynomial.X) - q = p := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      obtain ⟨q,hq⟩ := hp
      obtain ⟨s,hs⟩ := hr
      refine ⟨q+s,?_⟩
      rw [_root_.Polynomial.add_comp]
      linear_combination hq+hs
    | monomial i a =>
      simpa only [_root_.Polynomial.C_mul_X_pow_eq_monomial] using exists_antidifference_monomial i a
  obtain ⟨q,hq⟩ := hex
  exact ⟨q-_root_.Polynomial.C (q.eval 0),by simp,by simpa [_root_.Polynomial.sub_comp] using hq⟩

end Polynomial

namespace Polynomial
open scoped _root_.Polynomial
variable {A : Type*} [CommRing A] [Algebra ℚ A]

lemma exists_antidifference_monomial_algebra (i : ℕ) (a : A) :
    ∃ q : A[X], q.comp (1+_root_.Polynomial.X) - q = _root_.Polynomial.C a * _root_.Polynomial.X^i := by
  let b : A[X] := (_root_.Polynomial.bernoulli (i+1)).map (algebraMap ℚ A)
  have hb : b.comp (1+_root_.Polynomial.X) = b + _root_.Polynomial.C (i+1 : A) * _root_.Polynomial.X^i := by
    have h := congrArg (Polynomial.map (algebraMap ℚ A)) (_root_.Polynomial.bernoulli_comp_one_add_X (i+1))
    simpa [b,_root_.Polynomial.map_comp,nsmul_eq_mul] using h
  let u : A := (algebraMap ℚ A) ((i+1:ℚ)⁻¹)
  have hui : u*(i+1:A) = 1 := by
    have hi : (i+1:ℚ) ≠ 0 := by positivity
    have h := congrArg (algebraMap ℚ A) (inv_mul_cancel₀ hi)
    simpa [u] using h
  refine ⟨_root_.Polynomial.C (a*u)*b,?_⟩
  rw [_root_.Polynomial.mul_comp,_root_.Polynomial.C_comp,hb]
  calc
    _root_.Polynomial.C (a*u) * (b + _root_.Polynomial.C (i+1:A) * _root_.Polynomial.X^i) - _root_.Polynomial.C (a*u)*b =
      (_root_.Polynomial.C (a*u)*_root_.Polynomial.C (i+1:A))*_root_.Polynomial.X^i := by ring
    _ = _root_.Polynomial.C a*_root_.Polynomial.X^i := by rw [← _root_.Polynomial.C_mul,mul_assoc,hui,mul_one]

 

theorem exists_antidifference_algebra (p : A[X]) : ∃ q : A[X],
    q.eval 0 = 0 ∧ q.comp (1+_root_.Polynomial.X) - q = p := by
  have hex : ∃ q : A[X], q.comp (1+_root_.Polynomial.X) - q = p := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      obtain ⟨q,hq⟩ := hp
      obtain ⟨s,hs⟩ := hr
      refine ⟨q+s,?_⟩
      rw [_root_.Polynomial.add_comp]
      linear_combination hq+hs
    | monomial i a =>
      simpa only [_root_.Polynomial.C_mul_X_pow_eq_monomial] using exists_antidifference_monomial_algebra i a
  obtain ⟨q,hq⟩ := hex
  exact ⟨q-_root_.Polynomial.C (q.eval 0),by simp,by simpa [_root_.Polynomial.sub_comp] using hq⟩

end Polynomial

end
end
end
end
end

end OAI
