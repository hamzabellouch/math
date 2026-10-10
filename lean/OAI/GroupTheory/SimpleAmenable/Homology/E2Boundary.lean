import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TotalFiltration

namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma entry_inclusion (p q n : ℕ) (h : p+q=n) (x : (K.X p).X q) :
    projection K p q n (K.ιTotal c p q n h x)=x :=
  congrArg (fun f : (K.X p).X q ⟶ (K.X p).X q => f.hom x) (inclusion_projection K p q n h)

lemma entry_inclusion_ne (i j p q n : ℕ) (h : i+j=n) (hne : (i,j)≠(p,q)) (x : (K.X i).X j) :
    projection K p q n (K.ιTotal c i j n h x)=0 :=
  congrArg (fun f : (K.X i).X j ⟶ (K.X p).X q => f.hom x)
    (inclusion_projection_of_ne K i j p q n h hne)

lemma lower_filtration (p q : ℕ) {x : (K.total c).X (p+q)}
    (hx : x∈filtration K (p+q) ((p:ℤ)+1)) (htop : projection K p q (p+q) x=0) :
    x∈filtration K (p+q) p := by
  intro i hi
  by_cases he : i.val.1=p
  · obtain ⟨⟨i,j⟩,hij⟩ := i
    dsimp at he
    subst i
    have hj : j=q := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega
    subst j
    exact htop
  · exact hx i (by omega)

lemma lower_filtration' (p q n : ℕ) (hn : p+q=n) {x : (K.total c).X n}
    (hx : x∈filtration K n ((p:ℤ)+1)) (htop : projection K p q n x=0) :
    x∈filtration K n p := by
  subst n
  exact lower_filtration K p q hx htop

lemma linear_units_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) (a : ℤˣ) (x : A) :
    f (a • x)=a • f x := by simp [Units.smul_def]

noncomputable def lift (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    (K.total c).X (p+q+1) :=
  K.ιTotal c (p+1) q (p+q+1) (by dsimp; omega) y +
    ((-1 : ℤˣ)^p) • K.ιTotal c p (q+1) (p+q+1) (by dsimp; omega) z

lemma lift_mem (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    lift K p q y z ∈ filtration K (p+q+1) ((p:ℤ)+2) := by
  apply Submodule.add_mem
  · exact inclusion_mem K (by omega) y (by omega)
  · change ((-1 : ℤˣ)^p) • _ ∈ _
    rw [Units.smul_def]
    exact (filtration K (p+q+1) ((p:ℤ)+2)).toAddSubgroup.zsmul_mem
      (inclusion_mem K (by omega) z (by omega)) _

@[simp] lemma lift_left (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K (p+1) q (p+q+1) (lift K p q y z)=y := by
  simp only [lift,map_add,Units.smul_def,map_zsmul,entry_inclusion,
    entry_inclusion_ne K p (q+1) (p+1) q _ _ (by intro h; have := congrArg Prod.fst h; omega),
    smul_zero,add_zero]

@[simp] lemma lift_right (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K p (q+1) (p+q+1) (lift K p q y z)=((-1 : ℤˣ)^p) • z := by
  simp only [lift,map_add,Units.smul_def,map_zsmul,entry_inclusion,
    entry_inclusion_ne K (p+1) q p (q+1) _ _ (by intro h; have := congrArg Prod.fst h; omega),
    zero_add]

lemma neg_pow_smul_twice {A : Type*} [AddCommGroup A] (p : ℕ) (a : A) :
    ((-1 : ℤˣ)^p) • (((-1 : ℤˣ)^p) • a)=a := by
  rw [smul_smul,←mul_pow]
  simp

lemma d_lift_top (p q : ℕ) (y : (K.X (p+1)).X q) (z : (K.X p).X (q+1)) :
    projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) (lift K p q y z))=
      (K.d (p+1) p).f q y + (K.X p).d (q+1) q z := by
  rw [d_entry,lift_left,lift_right]
  congr 1
  change ((-1 : ℤˣ)^p) • ((K.X p).d (q+1) q).hom (((-1 : ℤˣ)^p) • z) = _
  rw [linear_units_smul,neg_pow_smul_twice]

lemma d_lift_mem (p q : ℕ) (y : ConcreteHomology.Cycles (K.X (p+1)) q)
    (z : (K.X p).X (q+1)) :
    (K.total c).d (p+q+1) (p+q) (lift K p q y.val z) ∈ filtration K (p+q) ((p:ℤ)+1) := by
  cases q with
  | zero =>
    simpa only [Nat.add_zero,filtration_top] using
      (show (K.total c).d (p+1) p (lift K p 0 y.val z)∈(⊤ : Submodule R _) from trivial)
  | succ q =>
    apply lower_filtration' K (p+1) q (p+(q+1)) (by omega)
    · exact d_filtration K (lift_mem K p (q+1) y.val z)
    · have he := d_entry' K (p+1) q (p+(q+1)+1) (p+(q+1)) (by omega) (by omega) (lift K p (q+1) y.val z)
      have hz : projection K (p+1+1) q (p+(q+1)+1) (lift K p (q+1) y.val z)=0 :=
        entry_zero K (lift_mem K p (q+1) y.val z) (by omega)
      rw [hz,map_zero,zero_add] at he
      have hy : projection K (p+1) (q+1) (p+(q+1)+1) (lift K p (q+1) y.val z)=y.val :=
        lift_left K p (q+1) y.val z
      rw [hy] at he
      have hcyc : (K.X (p+1)).d (q+1) q y.val=0 := y.property
      rw [hcyc,smul_zero] at he
      exact he

end E2Leading

end

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma lead_zero_boundary (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : lead K p q x=0) : x.val∈(filteredData K (p+q)).B₂ ((p:ℤ)+1) := by
  obtain ⟨u,hu⟩ := (ConcreteHomology.π_eq_zero (row K q) p (topRowCycle K p q x)).mp hx
  obtain ⟨y,rfl⟩ := ConcreteHomology.π_surjective (K.X (p+1)) q u
  have he : ConcreteHomology.π (K.X p) q (ConcreteHomology.cyclesMap (K.d (p+1) p) q y)=
      ConcreteHomology.π (K.X p) q (topCycle K p q x) := by
    have h := congrArg Subtype.val hu
    change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
      (ConcreteHomology.π (K.X (p+1)) q y)= _ at h
    rw [ConcreteHomology.map_π] at h
    exact h
  have hπ : ConcreteHomology.π (K.X p) q
      (topCycle K p q x - ConcreteHomology.cyclesMap (K.d (p+1) p) q y)=0 := by
    rw [map_sub,he,sub_self]
  obtain ⟨z,hz⟩ := (ConcreteHomology.π_eq_zero _ _ _).mp hπ
  have hzval : (K.X p).d (q+1) q z = projection K p q (p+q) x.val - (K.d (p+1) p).f q y.val := by
    have h := congrArg Subtype.val hz
    change (K.X p).d (q+1) q z = (topCycle K p q x).val - (ConcreteHomology.cyclesMap (K.d (p+1) p) q y).val at h
    rw [ConcreteHomology.cyclesMap_val] at h
    exact h
  let w := lift K p q y.val z
  have hw : w∈(filteredData K (p+q)).FA (((p:ℤ)+1)+1) := by
    change w∈filtration K (p+q+1) (((p:ℤ)+1)+1)
    simpa only [Int.add_assoc,Int.reduceAdd] using lift_mem K p q y.val z
  have hdw := d_lift_mem K p q y z
  have htop : projection K p q (p+q) ((K.total c).d (p+q+1) (p+q) w) =
      projection K p q (p+q) x.val := by
    calc
      _ = (K.d (p+1) p).f q y.val + (K.X p).d (q+1) q z := d_lift_top K p q y.val z
      _ = _ := by rw [hzval]; abel
  have hlower : x.val - (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) p := by
    apply lower_filtration K p q ((filtration K _ _).sub_mem x.property.1 hdw)
    rw [map_sub,htop,sub_self]
  refine Submodule.mem_sup.mpr ⟨x.val-(K.total c).d (p+q+1) (p+q) w,⟨?_,?_⟩,
    (K.total c).d (p+q+1) (p+q) w,⟨⟨w,hw,rfl⟩,hdw⟩,sub_add_cancel _ _⟩
  · change x.val-(K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (((p:ℤ)+1)-1)
    simpa using hlower
  · change (K.total c).d (p+q) (p+q-1) (x.val-(K.total c).d (p+q+1) (p+q) w)∈
      filtration K (p+q-1) (((p:ℤ)+1)-2)
    rw [map_sub]
    have hd : (K.total c).d (p+q) (p+q-1) ((K.total c).d (p+q+1) (p+q) w)=0 :=
      congrArg (fun f : (K.total c).X (p+q+1) ⟶ (K.total c).X (p+q-1) => f.hom w)
        ((K.total c).d_comp_d _ _ _)
    rw [hd,sub_zero]
    exact x.property.2

lemma finite_E₂ [IsNoetherianRing R] (p q : ℕ)
    [Module.Finite R (ConcreteHomology.H (row K q) p)] :
    Module.Finite R ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply FilteredFiniteness.finite_of_ker_le
    (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
      ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).mkQ (lead K p q)
    (Submodule.mkQ_surjective _)
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (lead_zero_boundary K p q x hx)

lemma finite_total_concrete [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R (ConcreteHomology.H (K.total c) n) := by
  change Module.Finite R (filteredData K n).H
  apply FilteredFiniteness.Data.finite_H _ n (filtration_zero K n) (filtration_top K n)
  intro p hp
  have hn : p+(n-p)=n := Nat.add_sub_of_le hp
  have := hfinite p (n-p) hn
  have h := finite_E₂ K p (n-p)
  rwa [hn] at h

lemma finite_total [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R ((K.total c).homology n) := by
  have := finite_total_concrete K n hfinite
  exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv (ConcreteHomology.iso (K.total c) n)).symm

end E2Leading

end

end

end OAI
