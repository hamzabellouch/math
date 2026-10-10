import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse
import OAI.Combinatorics.Chromatic.Walls.WeightedRay
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits UnitSelections LaurentPrecision
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]

structure WallUnitDatum (M : Type*) where
  degree : ℕ
  root : M
  kind : ℕ
  parameter : ℤ

variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)

def WallUnitDatum.value (u : WallUnitDatum M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω u.degree u.root
    (PowerSeries.map LaurentRay.atInfinity (indexedUnit u.kind u.parameter))

def WallUnitDatum.Allowed (V : M→Prop) (u : WallUnitDatum M) : Prop :=
  0<u.degree ∧ HasRootDegree C u.degree u.root ∧ V u.root

lemma rootDegree_nsmul {n : ℕ} {p : M} (hp : HasRootDegree C n p) (k : ℕ) :
    HasRootDegree C (k*n) (k • p) := by
  induction k with
  | zero=>simpa using rootDegree_zero C
  | succ k ih=>simpa only [Nat.succ_mul,succ_nsmul] using rootDegree_add C ih hp

lemma weightedRay_graded (n : ℕ) (p : M) (hp : HasRootDegree C n p)
    (F : PowerSeries (LaurentSeries ℚ)) :
    SeriesGraded LaurentRay.vUnit Ω C (weightedRay LaurentRay.vUnit Ω n p F) := by
  intro k m hm
  rw [coeff_weightedRay]
  split_ifs with h
  · change (Finsupp.single ((k/n) • p) (coeff (k/n) F)) m=0
    apply Finsupp.single_eq_of_ne
    intro H
    apply hm
    simpa only [Nat.div_mul_cancel h,H] using rootDegree_nsmul C hp (k/n)
  · rfl

lemma indexedUnit_constant (a : ℕ) (k : ℤ) : constantCoeff (indexedUnit a k)=1 := by
  unfold indexedUnit
  split_ifs
  · exact constant_elementary _ _
  · simp only [complete,constantCoeff_inv,constant_elementary,inv_one]

lemma WallUnitDatum.constant (u : WallUnitDatum M) : constantCoeff (u.value Ω)=1 := by
  rw [←coeff_zero_eq_constantCoeff,WallUnitDatum.value,coeff_weightedRay]
  simp only [dvd_zero,ite_eq_left,Nat.zero_div,zero_nsmul,coeff_map,coeff_zero_eq_constantCoeff,
    indexedUnit_constant,map_one]
  rfl

lemma WallUnitDatum.graded (V : M→Prop) (u : WallUnitDatum M) (hu : u.Allowed C V) :
    SeriesGraded LaurentRay.vUnit Ω C (u.value Ω) :=
  weightedRay_graded Ω C u.degree u.root hu.2.1 _

def literalRootProducts (V : M→Prop) : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List (WallUnitDatum M),(∀u∈l,u.Allowed C V) ∧ F=(l.map (WallUnitDatum.value Ω)).prod}

lemma literalRootProducts_graded (V : M→Prop) {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C V) : SeriesGraded LaurentRay.vUnit Ω C F := by
  obtain ⟨l,hl,rfl⟩:=hF
  induction l with
  | nil=>simpa using SeriesGraded.one LaurentRay.vUnit Ω C
  | cons u l ih=>
    simp only [List.map_cons,List.prod_cons]
    exact (u.graded Ω C V (hl u (by simp))).mul LaurentRay.vUnit Ω C
      (ih (fun v hv=>hl v (by simp [hv])))

lemma literalRootProducts_constant (V : M→Prop) {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C V) : constantCoeff F=1 := by
  obtain ⟨l,hl,rfl⟩:=hF
  simp only [map_list_prod,List.map_map]
  have H : l.map (constantCoeff ∘ WallUnitDatum.value Ω)=l.map (fun _=>1) := by
    apply List.map_congr_left
    intro u hu
    exact u.constant Ω
  rw [H]
  simp
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

def NatCoeff (r : ℚ) : Prop := ∃n : ℕ,r=n

def Positive (f : LaurentSeries ℚ) : Prop := ∀j,NatCoeff (f.coeff j)

lemma natCoeff_zero : NatCoeff 0 := ⟨0,rfl⟩
lemma natCoeff_one : NatCoeff 1 := ⟨1,rfl⟩
lemma NatCoeff.add {r s : ℚ} (hr : NatCoeff r) (hs : NatCoeff s) : NatCoeff (r+s) := by
  obtain ⟨n,rfl⟩:=hr
  obtain ⟨m,rfl⟩:=hs
  exact ⟨n+m,(Nat.cast_add n m).symm⟩
lemma NatCoeff.mul {r s : ℚ} (hr : NatCoeff r) (hs : NatCoeff s) : NatCoeff (r*s) := by
  obtain ⟨n,rfl⟩:=hr
  obtain ⟨m,rfl⟩:=hs
  exact ⟨n*m,(Nat.cast_mul n m).symm⟩
lemma NatCoeff.sum {A : Type*} (s : Finset A) (f : A → ℚ)
    (h : ∀a∈s,NatCoeff (f a)) : NatCoeff (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact natCoeff_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

lemma positive_zero : Positive 0 := fun _=>natCoeff_zero
lemma positive_one : Positive 1 := by
  intro j
  rw [HahnSeries.coeff_one]
  split <;> first | exact natCoeff_one | exact natCoeff_zero
lemma Positive.add {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f+g) :=
  fun j=>(hf j).add (hg j)
lemma Positive.mul {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f*g) := by
  intro j
  rw [HahnSeries.coeff_mul]
  apply NatCoeff.sum
  intro p hp
  exact (hf p.1).mul (hg p.2)
lemma Positive.sum {A : Type*} (s : Finset A) (f : A → LaurentSeries ℚ)
    (h : ∀a∈s,Positive (f a)) : Positive (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact positive_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

lemma single (k : ℤ) (r : ℚ) (hr : NatCoeff r) : Positive (HahnSeries.single k r) := by
  intro j
  rw [HahnSeries.coeff_single]
  split <;> first | exact hr | exact natCoeff_zero

lemma series {A : Type*} (e : A → ℤ) (he : EnergyLaurent.Admissible e) :
    Positive (EnergyLaurent.series e he) := by
  intro j
  rw [EnergyLaurent.series_coeff]
  exact ⟨_,rfl⟩

lemma of_converges {A : Type*} (l : Filter A) [l.NeBot]
    {f : A → LaurentSeries ℚ} {F : LaurentSeries ℚ}
    (h : Converges l f F) (hp : ∀ᶠi in l,Positive (f i)) : Positive F := by
  intro j
  obtain ⟨i,hi,hpi⟩:=Filter.Eventually.exists ((h (j+1)).and hp)
  rw [←hi j (by omega)]
  exact hpi j

end
end ElementaryPositivity.LaurentPositive

end

end OAI
