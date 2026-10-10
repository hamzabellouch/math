import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.PreparedRadialCount

namespace OAI

section
namespace SharpLogRamsey.RadialExceptions
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α ι : Type*} [Fintype α]

theorem count_exception (s : α→ℝ) (hs : ∀ x,0 ≤ s x) (K : ℝ) :
    ((univ.filter (fun x => K < s x)).card:ℝ)*K ≤ ∑ x,s x := by
  calc
    _ = ∑ _x∈univ.filter (fun x => K < s x),K := by simp
    _ ≤ ∑ x∈univ.filter (fun x => K < s x),s x :=
      sum_le_sum (fun _ hx => (mem_filter.mp hx).2.le)
    _ ≤ ∑ x,s x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun x _ _ => hs x)

theorem radial_exceptions (I : Finset ι) (a : ι→ℝ) (ha : ∀ i∈I,0<a i)
    (r : α→ι→ℕ) (q K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hcrude : ∀ x i,i∈I → (r x i:ℝ)*a i≤q)
    (hpair : ∀ i∈I, K<q*a i^99 → (∑ x,(r x i:ℝ))*a i^2≤C) :
    ∃ D : Finset α,
      (D.card:ℝ)*K≤C*∑ i∈I,a i^98 ∧
      ∀ x,x∉D → ∀ i∈I,(r x i:ℝ)*a i^100≤K := by
  let E := fun i => univ.filter (fun x => K<(r x i:ℝ)*a i^100)
  refine ⟨I.biUnion E,?_,?_⟩
  · have hlocal (i : ι) (hi : i∈I) : ((E i).card:ℝ)*K≤C*a i^98 := by
      by_cases he : q*a i^99≤K
      · have hempty : E i=∅ := by
          apply filter_eq_empty_iff.mpr
          intro x _ hx
          have hh := mul_le_mul_of_nonneg_right (hcrude x i hi) (pow_nonneg (ha i hi).le 99)
          have hp : a i*a i^99=a i^100 := by ring
          rw [mul_assoc,hp] at hh
          exact (not_lt_of_ge (hh.trans he)) hx
        rw [hempty,card_empty,Nat.cast_zero,zero_mul]
        positivity
      · have hh := count_exception (fun x => (r x i:ℝ)*a i^100)
          (fun x => by positivity) K
        change ((E i).card:ℝ)*K≤_ at hh
        have hs : (∑ x,(r x i:ℝ)*a i^100)=
            ((∑ x,(r x i:ℝ))*a i^2)*a i^98 := by rw [←sum_mul]; ring
        rw [hs] at hh
        exact hh.trans (mul_le_mul_of_nonneg_right
          (hpair i hi (lt_of_not_ge he)) (pow_nonneg (ha i hi).le 98))
    calc
      _ ≤ (∑ i∈I,((E i).card:ℝ))*K := by
        apply mul_le_mul_of_nonneg_right _ hK
        exact_mod_cast card_biUnion_le (s:=I) (t:=E)
      _ = ∑ i∈I,((E i).card:ℝ)*K := by rw [sum_mul]
      _ ≤ ∑ i∈I,C*a i^98 := sum_le_sum hlocal
      _ = _ := by rw [mul_sum]
  · intro x hx i hi
    exact le_of_not_gt (fun he => hx (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,he⟩⟩))

theorem strong_exceptions (r : α→ℕ) (a C : ℝ)
    (hpair : (∑ x,(r x:ℝ))*a^2≤C) :
    ∃ D : Finset α,(D.card:ℝ)*a^2≤C ∧ ∀ x,x∉D → r x=0 := by
  let D := univ.filter (fun x => 0<r x)
  refine ⟨D,?_,?_⟩
  · have hh : (D.card:ℝ)≤∑ x,(r x:ℝ) := by
      calc
        _ = ∑ _x∈D,(1:ℝ) := by simp
        _ ≤ ∑ x∈D,(r x:ℝ) := sum_le_sum (by
          intro x hx; exact_mod_cast (mem_filter.mp hx).2)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intro x _ _; positivity)
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg a)).trans hpair
  · intro x hx
    have hh : ¬0<r x := by simpa only [D,mem_filter,mem_univ,true_and] using hx
    omega

end
end SharpLogRamsey.RadialExceptions

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRadialExceptions_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedRadialExceptions_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedRadialExceptions_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedRadialExceptions_4 : Fintype (Submodule K V) := Fintype.ofFinite _

theorem richRadials_mul_le (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (hc : 0≤c) : ((richRadials S x c a).card:ℝ)*a≤c*S.card := by
  calc
    _ = ∑ _W∈richRadials S x c a,a := by simp
    _ ≤ ∑ W∈richRadials S x c a,strength S x c W :=
      sum_le_sum (fun W hW => (mem_filter.mp hW).2)
    _ ≤ ∑ W,strength S x c W := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) (fun W _ _ => mul_nonneg hc (Nat.cast_nonneg _))
    _ = c*(S.filter (fun y => y≠x)).card := by
      simpa only [strength,le_top,Finset.filter_true,and_true] using
        radial_mass S x ⊤ le_top c
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_filter_le _ _)) hc

theorem sum_richRadials_le_pairs
    (X : Projectivization K V→Finset (Projectivization K V)) (c a : ℝ) (M : ℕ)
    (hM : ∀ x (W : RadialLine x),a ≤ strength (X x) x c W →
      M≤(X x∩planePoints W.1).card) :
    (∑ x,(richRadials (X x) x c a).card)≤
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card := by
  let F := (univ : Finset (Projectivization K V)).sigma
    (fun x => richRadials (X x) x c a)
  have he : F.card=∑ x,(richRadials (X x) x c a).card := by simp [F,card_sigma]
  rw [←he]
  let f : (Σ x : Projectivization K V,RadialLine x) →
      Projectivization K V × ProjectiveLine (K:=K) (V:=V) :=
    fun z => (z.1,⟨z.2.1,z.2.2.1⟩)
  apply card_le_card_of_injOn f
  · intro z hz
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_⟩
    · exact mem_planePoints.mpr z.2.2.2
    · exact hM z.1 z.2 (mem_filter.mp (mem_sigma.mp hz).2).2
  · rintro ⟨x,W⟩ _ ⟨y,U⟩ _ hh
    have hxy : x=y := congrArg Prod.fst hh
    subst y
    have hWU : W.1=U.1 := congrArg (fun z => z.2.1) hh
    have hWU' : W=U := Subtype.ext hWU
    cases hWU'
    rfl

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
