import Mathlib
import OAI.Geometry.HyperbolicGroups.SquarePathFilling

namespace OAI

/-! Boundary-prescribed fillings depend continuously on parameters. This gives
literal square-prism extensions, rather than formal cellular coefficients. -/
noncomputable section

open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.SquarePathFilling
variable {X : Type*} [TopologicalSpace X] {a b c d : X}
  {p : Path a b} {q : Path a c} {r : Path b d} {s : Path c d}

lemma quotient_zero (t : I) : quotient (t,0) = (0,0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,low,high]
lemma quotient_one (t : I) : quotient (t,1) = (1,1) := by
  apply Prod.ext <;> apply Subtype.ext <;> norm_num [quotient,low,high]

/-- Recover the relative path homotopy from a genuine square having the
specified four boundary sides. -/
def unfill (f : C(I × I,X))
    (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
    (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x) :
    (p.trans r).Homotopy (q.trans s) where
  toContinuousMap := f.comp quotient
  map_zero_left x := by
    by_cases hx : (x:ℝ) ≤ 1/2
    · have hlow : low x = 0 := by unfold low; rw [max_eq_right (by linarith)]
      have hhigh : high x = 2*(x:ℝ) := by unfold high; rw [min_eq_left (by linarith)]
      have he : quotient (0,x) = (⟨2*(x:ℝ),by constructor <;> linarith [x.property.1]⟩,0) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (0,x)) = _
      rw [he,hb]
      change _ = p.trans r x
      rw [Path.trans_apply,dite_eq_left hx]
    · have hlow : low x = 2*(x:ℝ)-1 := by unfold low; rw [max_eq_left (by linarith)]
      have hhigh : high x = 1 := by unfold high; rw [min_eq_right (by linarith)]
      have he : quotient (0,x) = (1,⟨2*(x:ℝ)-1,by constructor <;> linarith [x.property.2]⟩) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (0,x)) = _
      rw [he,hr]
      change _ = p.trans r x
      rw [Path.trans_apply,dite_eq_right hx]
  map_one_left x := by
    by_cases hx : (x:ℝ) ≤ 1/2
    · have hlow : low x = 0 := by unfold low; rw [max_eq_right (by linarith)]
      have hhigh : high x = 2*(x:ℝ) := by unfold high; rw [min_eq_left (by linarith)]
      have he : quotient (1,x) = (0,⟨2*(x:ℝ),by constructor <;> linarith [x.property.1]⟩) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (1,x)) = _
      rw [he,hl]
      change _ = q.trans s x
      rw [Path.trans_apply,dite_eq_left hx]
    · have hlow : low x = 2*(x:ℝ)-1 := by unfold low; rw [max_eq_left (by linarith)]
      have hhigh : high x = 1 := by unfold high; rw [min_eq_right (by linarith)]
      have he : quotient (1,x) = (⟨2*(x:ℝ)-1,by constructor <;> linarith [x.property.2]⟩,1) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (1,x)) = _
      rw [he,ht]
      change _ = q.trans s x
      rw [Path.trans_apply,dite_eq_right hx]
  prop' t x hx := by
    rcases hx with rfl|hx
    · change f (quotient (t,0)) = _
      rw [quotient_zero,hb]; simp
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      change f (quotient (t,1)) = _
      rw [quotient_one,hr]; simp

@[simp] lemma fill_unfill (f : C(I × I,X))
    (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
    (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x) :
    fill (unfill f hb hl hr ht) = f := by
  ext z
  obtain ⟨z,rfl⟩ := quotient_surjective z
  rw [fill_quotient]; rfl

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]

/-- The product quotient is an actual compact closed quotient, ensuring
continuous families of fillings without a choice-continuity assumption. -/
def paramQuotient : C(T × (I × I),T × (I × I)) :=
  (ContinuousMap.id T).prodMap quotient
omit [CompactSpace T] [T2Space T] in
lemma paramQuotient_surjective : Function.Surjective (paramQuotient (T := T)) := by
  rintro ⟨t,z⟩
  obtain ⟨w,rfl⟩ := quotient_surjective z
  exact ⟨(t,w),rfl⟩
lemma paramQuotient_isQuotientMap : IsQuotientMap (paramQuotient (T := T)) :=
  paramQuotient.continuous.isClosedMap.isQuotientMap paramQuotient.continuous
    paramQuotient_surjective

variable (b : X)
omit [CompactSpace T] [T2Space T] in
lemma loopFamily_fiber (F : C(T × I,Path b b)) (t : T)
    {z z' : I × I} (h : quotient z = quotient z') : F (t,z.1) z.2 = F (t,z'.1) z'.2 := by
  rcases z with ⟨v,s⟩
  rcases z' with ⟨v',s'⟩
  obtain ⟨rfl,hh⟩ := quotient_fiber h
  rcases hh with rfl|rfl|rfl <;> simp

/-- A family of loop-space paths determines a family of actual square maps. -/
def paramFill (F : C(T × I,Path b b)) : C(T × (I × I),X) where
  toFun tz := F (tz.1,(quotient_surjective tz.2).choose.1)
    (quotient_surjective tz.2).choose.2
  continuous_toFun := by
    apply paramQuotient_isQuotientMap.continuous_iff.mpr
    have he : (fun tz : T × (I × I) => F (tz.1,(quotient_surjective tz.2).choose.1)
        (quotient_surjective tz.2).choose.2) ∘ paramQuotient =
        fun tz : T × (I × I) => F (tz.1,tz.2.1) tz.2.2 := by
      funext tz
      exact loopFamily_fiber b F tz.1 (quotient_surjective (quotient tz.2)).choose_spec
    rw [he]
    exact Path.continuous_uncurry_iff.mpr (F.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      |>.comp (continuous_id.prodMk (continuous_snd.comp continuous_snd))

lemma paramFill_quotient (F : C(T × I,Path b b)) (t : T) (z : I × I) :
    paramFill b F (t,quotient z) = F (t,z.1) z.2 := by
  exact loopFamily_fiber b F t (quotient_surjective (quotient z)).choose_spec

end HyperbolicObstruction.SquarePathFilling
end

end OAI
