import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonMonoidalData

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonComponentCompletion

open Classical CategoryTheory
namespace PolygonObject
variable {a : ℕ}

abbrev Component (a : ℕ) := Skeleton (PolygonObject a)
noncomputable abbrev component (U : PolygonObject a) : Component a := toSkeleton U

@[simp] theorem component_sum (U V : PolygonObject a) :
    component (sum U V)=component U*component V :=
  Skeleton.toSkeleton_tensorObj U V

theorem sum_standard (m n : ℕ) : sum (standard a m) (standard a n)=standard a (m+n) := by
  unfold sum standard
  congr 1
  funext i
  induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]

@[simp] theorem component_standard_zero : component (standard a 0)=1 := by
  rw [Skeleton.one_eq]
  apply congrArg toSkeleton
  change standard a 0=empty
  unfold standard empty
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem component_standard_add (m n : ℕ) :
    component (standard a (m+n))=component (standard a m)*component (standard a n) := by
  rw [←sum_standard,component_sum]

theorem component_standard_pow (n : ℕ) :
    component (standard a n)=component (standard a 1)^n := by
  induction n with
  | zero => simp
  | succ n hn => rw [component_standard_add,hn,pow_succ]

theorem component_complement (U : PolygonObject a) :
    component U * component (complement U)=component (standard a U.tracks) := by
  rw [←component_sum]
  exact congr_toSkeleton_of_iso (complementIso U)

abbrev CompletedComponent (a : ℕ) := Algebra.GrothendieckGroup (Component a)
noncomputable abbrev completedComponent (U : PolygonObject a) : CompletedComponent a :=
  Algebra.GrothendieckGroup.of (component U)

theorem completion_eq_iff (U V : PolygonObject a) :
    completedComponent U=completedComponent V ↔
      ∃ W : PolygonObject a, Nonempty (sum U W ≅ sum V W) := by
  change (Localization.monoidOf (⊤ : Submonoid (Component a))) (component U)=
    (Localization.monoidOf (⊤ : Submonoid (Component a))) (component V) ↔ _
  rw [Submonoid.LocalizationMap.eq_iff_exists]
  constructor
  · rintro ⟨c,hc⟩
    let W : PolygonObject a := (fromSkeleton (PolygonObject a)).obj c.val
    refine ⟨W,⟨Skeleton.isoOfEq ?_⟩⟩
    change component (sum U W)=component (sum V W)
    rw [component_sum,component_sum]
    have he : component W=c.val := toSkeleton_fromSkeleton_obj c.val
    rw [he,mul_comm (component U),mul_comm (component V)]
    exact hc
  · rintro ⟨W,hW⟩
    refine ⟨⟨component W,Submonoid.mem_top _⟩,?_⟩
    have hh := toSkeleton_eq_toSkeleton_iff.mpr hW
    change component (sum U W)=component (sum V W) at hh
    rw [component_sum,component_sum] at hh
    simpa [mul_comm] using hh

theorem neutral_component_eventually_standard (U : PolygonObject a) (r : ℕ)
    (hU : completedComponent U=completedComponent (standard a r)) :
    ∃ k : ℕ, Nonempty (sum U (standard a k) ≅ standard a (r+k)) := by
  obtain ⟨V,hV⟩ := (completion_eq_iff U (standard a r)).mp hU
  refine ⟨V.tracks,toSkeleton_eq_toSkeleton_iff.mp ?_⟩
  have hh := toSkeleton_eq_toSkeleton_iff.mpr hV
  change component (sum U V)=component (sum (standard a r) V) at hh
  rw [component_sum,component_sum] at hh
  have he := congrArg (fun x : Component a => x*component (complement V)) hh
  change component (sum U (standard a V.tracks))=component (standard a (r+V.tracks))
  rw [component_sum,component_standard_add]
  simpa only [mul_assoc,component_complement] using he

end PolygonObject
end PolygonComponentCompletion

end SimpleAmenable
end
end

end OAI
