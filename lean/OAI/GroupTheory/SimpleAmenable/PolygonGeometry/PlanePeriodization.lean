import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TorusStepFunctions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlanePeriodization

open Classical
namespace SquareStep
variable {a : ℕ}

theorem slice_finite (f : PlaneStep a) : Function.HasFiniteSupport (fun n => slice n f) := by
  obtain ⟨R,hR⟩ := PlaneStep.compactSupport f
  let N : ℤ := ⌈R+1⌉
  refine (Set.finite_Icc (-N,-N) (N,N)).subset ?_
  intro n hn
  have hp : ∃ p : GenericSquare a, (slice n f).val p ≠ 0 := by
    by_contra! h
    apply hn
    apply Subtype.ext
    exact funext h
  obtain ⟨p,hp⟩ := hp
  rw [slice_apply] at hp
  have hb : |p.val.1+(n.1:ℝ)| ≤ R ∧ |p.val.2+(n.2:ℝ)| ≤ R := by
    by_contra! h
    apply hp
    apply hR
    have hh : R < |p.val.1+(n.1:ℝ)| ∨ R < |p.val.2+(n.2:ℝ)| := by
      by_cases hx : |p.val.1+(n.1:ℝ)| ≤ R
      · exact Or.inr (h hx)
      · exact Or.inl (lt_of_not_ge hx)
    simpa only [GenericPlane.shift,intPair,Prod.fst_add,Prod.snd_add,map_intCast] using hh
  have hx : |(n.1:ℝ)| ≤ R+1 := by
    have ht := abs_add_le (p.val.1+(n.1:ℝ)) (-p.val.1)
    have he : p.val.1+(n.1:ℝ)+ -p.val.1=(n.1:ℝ) := by ring
    rw [he,abs_neg,abs_of_nonneg p.property.1.1] at ht
    linarith [p.property.1.2]
  have hy : |(n.2:ℝ)| ≤ R+1 := by
    have ht := abs_add_le (p.val.2+(n.2:ℝ)) (-p.val.2)
    have he : p.val.2+(n.2:ℝ)+ -p.val.2=(n.2:ℝ) := by ring
    rw [he,abs_neg,abs_of_nonneg p.property.2.1.1] at ht
    linarith [p.property.2.1.2]
  have hx' : -N ≤ n.1 ∧ n.1 ≤ N := by
    exact_mod_cast abs_le.mp (hx.trans (Int.le_ceil (R+1)))
  have hy' : -N ≤ n.2 ∧ n.2 ≤ N := by
    exact_mod_cast abs_le.mp (hy.trans (Int.le_ceil (R+1)))
  exact ⟨⟨hx'.1,hy'.1⟩,⟨hx'.2,hy'.2⟩⟩

noncomputable def periodize : PlaneStep a →ₗ[ℤ] SquareStep a where
  toFun f := ∑ᶠ n : ℤ×ℤ, slice n f
  map_add' f g := by
    simp only [map_add]
    exact finsum_add_distrib (slice_finite f) (slice_finite g)
  map_smul' c f := by
    simp only [map_smul]
    exact (map_finsum (DistribSMul.toAddMonoidHom (SquareStep a) c) (slice_finite f)).symm

noncomputable def eval (p : GenericSquare a) : SquareStep a →ₗ[ℤ] ℤ :=
  (LinearMap.proj p).comp (squareStepSubmodule a).subtype

theorem periodize_apply (f : PlaneStep a) (p : GenericSquare a) :
    (periodize f).val p = ∑ᶠ n : ℤ×ℤ, (slice n f).val p :=
  map_finsum (eval p) (slice_finite f)

theorem slice_extend (f : SquareStep a) (n : ℤ×ℤ) (hn : n≠0) :
    slice n (extend f)=0 := by
  apply Subtype.ext
  funext p
  rw [slice_apply,extend_apply]
  apply dite_eq_right
  intro h
  have h' : (0 ≤ p.val.1+(n.1:ℝ) ∧ p.val.1+(n.1:ℝ)<1) ∧
      (0 ≤ p.val.2+(n.2:ℝ) ∧ p.val.2+(n.2:ℝ)<1) := by
    simpa [InSquare,GenericPlane.shift,intPair] using h
  have hx : (-1:ℤ)<n.1 ∧ n.1<1 := by
    have hr : (-1:ℝ)<(n.1:ℝ) ∧ (n.1:ℝ)<1 :=
      ⟨by linarith [p.property.1.2,h'.1.1],by linarith [p.property.1.1,h'.1.2]⟩
    exact_mod_cast hr
  have hy : (-1:ℤ)<n.2 ∧ n.2<1 := by
    have hr : (-1:ℝ)<(n.2:ℝ) ∧ (n.2:ℝ)<1 :=
      ⟨by linarith [p.property.2.1.2,h'.2.1],by linarith [p.property.2.1.1,h'.2.2]⟩
    exact_mod_cast hr
  exact hn (Prod.ext (by dsimp; omega) (by dsimp; omega))

@[simp] theorem periodize_extend (f : SquareStep a) : periodize (extend f)=f := by
  change (∑ᶠ n : ℤ×ℤ, slice n (extend f))=f
  rw [finsum_eq_single _ 0 (fun n hn => slice_extend f n hn),slice_zero,restrict_extend]

theorem periodize_surjective : Function.Surjective (periodize (a := a)) :=
  fun f => ⟨extend f,periodize_extend f⟩

end SquareStep
end PlanePeriodization

end SimpleAmenable
end
end

end OAI
