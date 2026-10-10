import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.UnitSelectionLaurent
import OAI.Combinatorics.Chromatic.Walls.CompleteUnitRecursion

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

lemma laurent_q_not_root (n : ℕ) : 1-(HahnSeries.single (2:ℤ) (1:ℚ))^(n+1)≠0 := by
  intro h
  have hh : LaurentRay.atInfinity (1-RationalRay.q^(n+1))=LaurentRay.atInfinity 0 := by
    rw [map_sub,map_one,map_pow,LaurentRay.atInfinity_q,map_zero]
    exact h
  exact RationalRay.q_not_root_unity n (LaurentRay.atInfinity_injective hh)

theorem weakSeries_eq_complete (n : ℕ) (k : ℤ) :
    weakSeries n k=coeff n (complete (HahnSeries.single 2 (1:ℚ)) (HahnSeries.single (-k) 1)) := by
  induction n with
  | zero => rw [weakSeries_zero,complete_coeff_zero]
  | succ n ih =>
    apply mul_right_cancel₀ (laurent_q_not_root n)
    rw [weakSeries_recursion_q,complete_coeff_recursion _ _ laurent_q_not_root,ih]

theorem complete_literal_expansion (n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (complete RationalRay.q (RationalRay.v^k)))=weakSeries n k := by
  rw [weakSeries_eq_complete,←LaurentRay.complete_atInfinity,coeff_map]
end
end ElementaryPositivity.UnitSelections
end
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

def strictEnergy (n : ℕ) (k : ℤ) (f : Strict n) : ℤ := (n:ℤ)*k-2*weight f.val

lemma strictAdmissible (n : ℕ) (k : ℤ) : Admissible (strictEnergy n k) := by
  constructor
  · refine ⟨n*k,?_⟩
    intro f
    have hh : 0≤weight f.val:=Finset.sum_nonneg (fun i _=>Int.natCast_nonneg _)
    unfold strictEnergy
    linarith
  · intro E
    let : Finite {f : Weak n // weakEnergy n k f=E}:=(weakAdmissible n k).2 E
    let F : {f : Strict n // strictEnergy n k f=E} → {f : Weak n // weakEnergy n k f=E} := fun f=>
      ⟨⟨f.val.val,f.val.property.monotone⟩,f.property⟩
    exact Finite.of_injective F (fun f g h=>Subtype.ext (Subtype.ext
      (congrArg (fun z : {f : Weak n // weakEnergy n k f=E}=>z.val.val) h)))

def strictSeries (n : ℕ) (k : ℤ) : LaurentSeries ℚ := series (strictEnergy n k) (strictAdmissible n k)

lemma strictSeries_staircase (n : ℕ) (k : ℤ) :
    strictSeries n k=weakSeries n k*HahnSeries.single ((n:ℤ)*((n:ℤ)-1)) (1:ℚ) := by
  have hh := series_equiv (admissible_shift (weakAdmissible n k) (-((n:ℤ)*((n:ℤ)-1))))
    (strictAdmissible n k) (staircaseEquiv n) (fun f=>by
      have hf:=staircase_weight n f
      unfold strictEnergy weakEnergy
      omega)
  rw [series_shift (weakAdmissible n k)] at hh
  simpa only [neg_neg,weakSeries,strictSeries] using hh.symm

lemma twice_range_staircase (n : ℕ) :
    2*((∑i∈Finset.range n,i:ℕ):ℤ)=(n:ℤ)*((n:ℤ)-1) := by
  have hh:=twice_staircase n
  rw [Fin.sum_univ_eq_sum_range] at hh
  simpa only [Nat.cast_sum] using hh

theorem elementary_literal_expansion (n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (elementary RationalRay.q (RationalRay.v^k)))=strictSeries n k := by
  rw [coeff_elementary,elementaryCoeff_eq_complete _ _ RationalRay.q_not_root_unity,
    map_mul,map_pow,LaurentRay.atInfinity_q,complete_literal_expansion,strictSeries_staircase,
    HahnSeries.single_pow,one_pow]
  have he : (∑i∈Finset.range n,i) • (2:ℤ)=(n:ℤ)*((n:ℤ)-1) := by
    rw [nsmul_eq_mul,mul_comm]
    exact twice_range_staircase n
  rw [he,mul_comm]
end
end ElementaryPositivity.UnitSelections
end
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section

lemma admissible_equiv {A B : Type*} {e : A → ℤ} {f : B → ℤ}
    (he : Admissible e) (q : A ≃ B) (hq : ∀a,f (q a)=e a) : Admissible f := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    refine ⟨K,fun b=>?_⟩
    have hh:=hK (q.symm b)
    rw [←hq (q.symm b),q.apply_symm_apply] at hh
    exact hh
  · intro E
    let := he.2 E
    exact Finite.of_equiv {a // e a=E} (q.subtypeEquiv (fun a=>by rw [hq]))

def finSuccPi (n : ℕ) (A : Fin (n+1) → Type*) :
    (∀i,A i) ≃ A 0 × (∀i:Fin n,A i.succ) where
  toFun f := (f 0,fun i=>f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _=>rfl) i
  right_inv p := rfl

lemma admissible_fin_pi (n : ℕ) (A : Fin n → Type*) (e : ∀i,A i → ℤ)
    (he : ∀i,Admissible (e i)) : Admissible (fun f : ∀i,A i=>∑i,e i (f i)) := by
  induction n with
  | zero =>
    constructor
    · exact ⟨0,fun _=>by simp⟩
    · intro E; infer_instance
  | succ n ih =>
    have hp:=admissible_prod (he 0) (ih (fun i=>A i.succ) (fun i=>e i.succ) (fun i=>he i.succ))
    exact admissible_equiv hp (finSuccPi n A).symm (fun f=>by
      change (∑i,e i (Fin.cases f.1 f.2 i))=e 0 f.1+∑i,e i.succ (f.2 i)
      rw [Fin.sum_univ_succ]
      rfl)

lemma series_fin_pi (n : ℕ) (A : Fin n → Type*) (e : ∀i,A i → ℤ)
    (he : ∀i,Admissible (e i)) :
    (∏i,series (e i) (he i))=
      series (fun f : ∀i,A i=>∑i,e i (f i)) (admissible_fin_pi n A e he) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    have hu : Unique (∀i:Fin 0,A i):=⟨⟨fun i=>Fin.elim0 i⟩,fun _=>Subsingleton.elim _ _⟩
    let := hu
    change 1=(family _ _).hsum
    rw [HahnSeries.SummableFamily.hsum_unique]
    change 1=HahnSeries.single 0 (1:ℚ)
    exact HahnSeries.single_zero_one.symm
  | succ n ih =>
    rw [Fin.prod_univ_succ,ih (fun i=>A i.succ) (fun i=>e i.succ) (fun i=>he i.succ),series_mul]
    apply series_equiv _ _ (finSuccPi n A).symm
    intro f
    change (∑i,e i (Fin.cases f.1 f.2 i))=e 0 f.1+∑i,e i.succ (f.2 i)
    rw [Fin.sum_univ_succ]
    rfl
end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
