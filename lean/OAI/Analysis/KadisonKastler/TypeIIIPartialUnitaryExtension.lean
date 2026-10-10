import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.SymmetricSupportTransfer

namespace OAI

/-! # Completing a proper partial isometry inside a type III factor

Nonzero complementary projections are equivalent. The completion agrees
exactly on the source projection, so its vector error is controlled by
the discarded source corner. This is the bounded step used to pass from
isometries to unitaries in state-orbit approximation.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.extend_partialIsometry (hM : TypeIIIFactor M)
    (v : PartialIsometry M) (hs : v.support.val≠1) (ht : v.target.val≠1) :
    ∃ u : unitary (Algebra M), u.val*v.support.val=v.val := by
  let p : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let q : AlgebraProjection M := ⟨1-v.target.val,v.target.property.one_sub⟩
  have hp : p.val≠0 := sub_ne_zero.mpr (Ne.symm hs)
  have hq : q.val≠0 := sub_ne_zero.mpr (Ne.symm ht)
  obtain ⟨a,ha,hap⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  obtain ⟨b,hb,hbq⟩ := hM.exists_isometry_onto_projection q.val q.property hq
  let w : PartialIsometry M := {
    support := p
    val := b*star a
    initial := by
      rw [star_mul,star_star]
      calc
        (a*star b)*(b*star a)=a*(star b*b)*star a := by simp only [mul_assoc]
        _ = p.val := by rw [hb,mul_one,hap] }
  have hwq : w.target=q := by
    apply Subtype.ext
    change (b*star a)*star (b*star a)=q.val
    rw [star_mul,star_star]
    calc
      (b*star a)*(a*star b)=b*(star a*a)*star b := by simp only [mul_assoc]
      _ = q.val := by rw [ha,mul_one,hbq]
  have hi : v.support.val*w.support.val=0 := v.support.property.mul_one_sub_self
  have hf : v.target.val*w.target.val=0 := by
    rw [hwq]
    exact v.target.property.mul_one_sub_self
  let z := v.patch w hi hf
  have hzi : star z.val*z.val=1 := by
    rw [z.initial]
    change v.support.val+(1-v.support.val)=1
    abel
  have hzt : z.val*star z.val=1 := by
    change z.target.val=1
    rw [PartialIsometry.patch_target,hwq]
    change v.target.val+(1-v.target.val)=1
    abel
  exact ⟨⟨z.val,hzi,hzt⟩,v.le_patch w hi hf⟩

omit [TopologicalSpace.SeparableSpace H] in
/-- Exact agreement on a projection controls the error on every vector. -/
theorem unitary_isometry_error_of_agree (v : Algebra M) (hv : star v*v=1)
    (u : unitary (Algebra M)) (p : AlgebraProjection M)
    (hp : u.val*p.val=v*p.val) (ξ : H) :
    ‖u.val.val ξ-v.val ξ‖ ≤ 2*‖ξ-p.val.val ξ‖ := by
  have he : u.val.val ξ-v.val ξ=
      u.val.val (ξ-p.val.val ξ)-v.val (ξ-p.val.val ξ) := by
    have h := congrArg (fun a : Algebra M => a.val ξ) hp
    change u.val.val (p.val.val ξ)=v.val (p.val.val ξ) at h
    rw [map_sub,map_sub,h]
    abel
  rw [he]
  calc
    _ ≤ ‖u.val.val (ξ-p.val.val ξ)‖+‖v.val (ξ-p.val.val ξ)‖ := norm_sub_le _ _
    _ = 2*‖ξ-p.val.val ξ‖ := by
      have hu' (x : H) : ‖u.val.val x‖=‖x‖ := Unitary.norm_map (ambientAlgebraUnitary u) x
      have hv' (x : H) : ‖v.val x‖=‖x‖ :=
        norm_apply_of_operator_isometry v.val (congrArg Subtype.val hv) x
      rw [hu',hv']
      ring

end
end KadisonKastler

end OAI
