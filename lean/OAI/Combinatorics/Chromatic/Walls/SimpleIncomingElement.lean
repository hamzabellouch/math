import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SimpleBinomial
import OAI.Combinatorics.Chromatic.GradedAlgebra.PureFaceLog

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
omit [Fintype I] in
include hcoord in
lemma simpleRoot_ray_iff (i : I) : OnPositiveRay (simpleRoot C pc) (simpleRoot C i) ↔ i=pc := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    by_contra hi
    have HH:=congrArg (fun m=>coord m pc) he
    simp only [map_nsmul,Pi.smul_apply,simpleRoot_coordinates C coord hcoord] at HH
    simp only [Pi.single_eq_of_ne (Ne.symm hi),Pi.single_eq_same,nsmul_eq_mul,mul_one] at HH
    omega
  · rintro rfl
    exact ⟨1,1,by omega,by omega,rfl⟩
include hcoord in
lemma literalIncoming_simple :
    literalIncomingRay Ω (simpleIncomingList C) (simpleRoot C pc)=normalizedSimple Ω (simpleRoot C pc) := by
  classical
  unfold literalIncomingRay simpleIncomingList
  rw [List.filter_map]
  have hf : (Finset.univ.toList : List I).filter
      ((fun u : WallUnitDatum M=>decide (OnPositiveRay (simpleRoot C pc) u.root)) ∘ simpleDatum C)=[pc] := by
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) (by simp)).mpr
    intro i
    simp only [List.mem_filter,Finset.mem_toList,Finset.mem_univ,true_and,Function.comp_apply,
      simpleDatum,List.mem_singleton]
    constructor
    · intro hh; exact (simpleRoot_ray_iff C coord hcoord pc i).mp (of_decide_eq_true hh)
    · intro hh; exact decide_eq_true ((simpleRoot_ray_iff C coord hcoord pc i).mpr hh)
  rw [hf,List.map_singleton,List.map_singleton,List.prod_singleton,simpleDatum_value]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma nonp_zero_of_simple_ray {m : M} (hm : OnPositiveRay (simpleRoot C pc) m) :
    nonpDegree coord pc m=0 := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have HH:=congrArg (nonpDegree coord pc) he
  rw [map_nsmul,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,nsmul_eq_mul] at HH
  exact (mul_eq_zero.mp HH).resolve_left (by exact_mod_cast Nat.ne_of_gt ha)

lemma pureFaceSeries_eq_through (F : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (hF : ∀j≤N,∀m,coeff j F m≠0 → nonpDegree coord pc m=0) :
    ∀j≤N,coeff j (pureFaceSeries Ω coord pc F)=coeff j F := by
  intro j hj
  apply Finsupp.ext
  intro m
  rw [pureFaceSeries_apply]
  split_ifs with hh
  · rfl
  · exact (not_ne_iff.mp (fun he=>hh (hF j hj m he))).symm

include hcoord in
lemma pureFace_simpleTransport_value (hΩ : ∀m,Ω m m=0) :
    (pureFace Ω C coord pc (simpleTotalTransport Ω C)).val=normalizedSimple Ω (simpleRoot C pc) := by
  rw [pureFace_simpleTransport Ω C coord hcoord pc hΩ]
  exact literalIncoming_simple Ω C coord hcoord pc

include hcoord in
lemma pure_simple_wall (hΩ : ∀m,Ω m m=0) (N : ℕ) (h : M →+ ℝ)
    (hg : RayGeneric C N (simpleRoot C pc) h) :
    ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
      coeff j (normalizedSimple Ω (simpleRoot C pc)) := by
  let F:=chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)
  have HF:=pureFace_chartZero Ω C coord hcoord pc h hg.1 (simpleTotalTransport Ω C)
  have HR : ∀j≤N,∀m,coeff j F.val m≠0 → nonpDegree coord pc m=0:=by
    intro j hj m hm
    cases j with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply,F.property.1] at hm
      have hm0 : m=0:=by
        by_contra hh
        exact hm (Finsupp.single_eq_of_ne hh)
      rw [hm0,map_zero]
    | succ j=>
      have hmroot : HasRootDegree C (j+1) m:=by by_contra hh; exact hm (F.property.2 _ m hh)
      have hmzero : h m=0:=(chart_three_support LaurentRay.vUnit Ω C h _).2.1 j m hm
      exact nonp_zero_of_simple_ray C coord hcoord pc (hg.2 (j+1) (by omega) hj m hmroot hmzero)
  intro j hj
  rw [←pureFaceSeries_eq_through Ω coord pc F.val N HR j hj]
  change coeff j (pureFace Ω C coord pc F).val=_
  rw [HF,pureFace_simpleTransport_value Ω C coord hcoord pc hΩ]

include hcoord in
lemma pure_joint_factor (hΩ : ∀m,Ω m m=0) (N : ℕ) (k h : M →+ ℝ)
    (hk : k (simpleRoot C pc)=0) (hh : h (simpleRoot C pc)=0)
    (hRay : ∀j,j+1≤N → ∀m,
      coeff (j+1) (chartZero LaurentRay.vUnit Ω C h
        (chartZero LaurentRay.vUnit Ω C k (simpleTotalTransport Ω C))).val m≠0 →
      OnPositiveRay (simpleRoot C pc) m) :
    ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C h
      (chartZero LaurentRay.vUnit Ω C k (simpleTotalTransport Ω C))).val=
      coeff j (normalizedSimple Ω (simpleRoot C pc)) := by
  let F:=chartZero LaurentRay.vUnit Ω C h
    (chartZero LaurentRay.vUnit Ω C k (simpleTotalTransport Ω C))
  have HR : ∀j≤N,∀m,coeff j F.val m≠0 → nonpDegree coord pc m=0:=by
    intro j hj m hm
    cases j with
    | zero=>
      rw [coeff_zero_eq_constantCoeff_apply,F.property.1] at hm
      have hm0 : m=0:=by by_contra hh; exact hm (Finsupp.single_eq_of_ne hh)
      rw [hm0,map_zero]
    | succ j=>exact nonp_zero_of_simple_ray C coord hcoord pc (hRay j hj m hm)
  intro j hj
  rw [←pureFaceSeries_eq_through Ω coord pc F.val N HR j hj]
  change coeff j (pureFace Ω C coord pc F).val=_
  rw [pureFace_chartZero Ω C coord hcoord pc h hh,pureFace_chartZero Ω C coord hcoord pc k hk,
    pureFace_simpleTransport_value Ω C coord hcoord pc hΩ]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
def completedOne : CompletedPositive v Ω C :=
  ⟨1,by simp,FormalLog.graded_one _ (rootGrade_one v Ω C)⟩
def completedMul (F G : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨F.val*G.val,by simp only [map_mul,F.property.1,G.property.1,mul_one],
    FormalLog.graded_multiply _ (rootGrade_mul v Ω C) _ _ F.property.2 G.property.2⟩
def completedConjugate (F G : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  completedMul v Ω C (completedMul v Ω C F G) (completedInverse v Ω C F)
lemma chartZero_right_negative (h : M →+ ℝ) (G H : CompletedPositive v Ω C) (N : ℕ)
    (hH : ∀j,j+1≤N → ∀m,coeff (j+1) H.val m≠0 → h m<0) :
    ∀j≤N,coeff j (chartZero v Ω C h (completedMul v Ω C G H)).val=
      coeff j (chartZero v Ω C h G).val := by
  have HG:=chart_three_support v Ω C h G
  have HU:=chart_three_truncated_unique v Ω C h (completedMul v Ω C G H)
    (chartPositive v Ω C h G).val (chartZero v Ω C h G).val
    ((chartNegative v Ω C h G).val*H.val) N
    (chartPositive v Ω C h G).property.1 (chartZero v Ω C h G).property.1
    (by simp only [map_mul,(chartNegative v Ω C h G).property.1,H.property.1,mul_one])
    (by change _*(_*H.val)=G.val*H.val; rw [←mul_assoc,chart_three_factorization])
    (fun j _=>HG.1 j) (fun j _=>HG.2.1 j) (by
      intro j hj m hm
      by_contra hh
      exact hm (strict_mul_through v Ω (fun m=>h m<0)
        (fun a b ha hb=>by simpa only [map_add] using add_neg ha hb)
        (chartNegative v Ω C h G).val H.val N
        (chartNegative v Ω C h G).property.1 H.property.1
        (fun j hj m hm=>by by_contra hv; exact hm (HG.2.2 j m hv))
        (fun j hj m hm=>by by_contra hv; exact hm (hH j hj m hv)) j hj m hh))
  exact fun j hj=>(HU j hj).2.1.symm
lemma chartZero_left_positive (h : M →+ ℝ) (H G : CompletedPositive v Ω C) (N : ℕ)
    (hH : ∀j,j+1≤N → ∀m,coeff (j+1) H.val m≠0 → 0<h m) :
    ∀j≤N,coeff j (chartZero v Ω C h (completedMul v Ω C H G)).val=
      coeff j (chartZero v Ω C h G).val := by
  have HG:=chart_three_support v Ω C h G
  have HU:=chart_three_truncated_unique v Ω C h (completedMul v Ω C H G)
    (H.val*(chartPositive v Ω C h G).val) (chartZero v Ω C h G).val
    (chartNegative v Ω C h G).val N
    (by simp only [map_mul,H.property.1,(chartPositive v Ω C h G).property.1,mul_one])
    (chartZero v Ω C h G).property.1 (chartNegative v Ω C h G).property.1
    (by change _*_*_=H.val*G.val; rw [mul_assoc,mul_assoc,←mul_assoc (chartPositive _ _ _ _ _).val,
      chart_three_factorization])
    (by
      intro j hj m hm
      by_contra hh
      exact hm (strict_mul_through v Ω (fun m=>0<h m)
        (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb)
        H.val (chartPositive v Ω C h G).val N
        H.property.1 (chartPositive v Ω C h G).property.1
        (fun j hj m hm=>by by_contra hv; exact hm (hH j hj m hv))
        (fun j hj m hm=>by by_contra hv; exact hm (HG.1 j m hv)) j hj m hh))
    (fun j _=>HG.2.1 j) (fun j _=>HG.2.2 j)
  exact fun j hj=>(HU j hj).2.1.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
