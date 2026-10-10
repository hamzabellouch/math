import OAI.Geometry.SurfaceImmersion.Primitive.CrossingNormalPath

namespace OAI

/-! A complete local path, including its normal-plane constraint, from the
preferred normal to one having positive pairing with both crossing vectors. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma unit_not_negative_normalize {n p : Vec} (hp : 0 < p ⬝ᵥ n) :
    n ≠ -normalize p := by
  intro he
  have h := normalize_dot_pos hp
  rw [he,dotProduct_neg,normalize_unit (nonzero_of_dot_pos hp)] at h
  norm_num at h

/-- The path remains in every linear hyperplane containing the original
normal and the first pure vector.  Thus it remains in the normal plane. -/
theorem admissible_crossing_path {n p q : Vec} (hn : n ⬝ᵥ n = 1)
    (hchoice : (0 < p ⬝ᵥ n ∧ 0 < q ⬝ᵥ n) ∨
      (0 < p ⬝ᵥ q ∧ ∃ m : Vec, n ⬝ᵥ m = 0 ∧ 0 < p ⬝ᵥ m ∧ 0 < q ⬝ᵥ m)) :
    ∃ γ : ℝ → Vec, ContDiffOn ℝ ∞ γ (Icc (0 : ℝ) 1) ∧ γ 0 = n ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        γ t ⬝ᵥ γ t = 1 ∧ γ t ≠ -normalize p ∧ γ t ≠ -normalize q ∧
        ∀ v : Vec, v ⬝ᵥ n = 0 → v ⬝ᵥ p = 0 → v ⬝ᵥ γ t = 0) ∧
      0 < p ⬝ᵥ γ 1 ∧ 0 < q ⬝ᵥ γ 1 := by
  rcases hchoice with hpos | ⟨hacute,m,hnm,hpm,hqm⟩
  · refine ⟨fun _ => n,contDiffOn_const,rfl,?_,hpos.1,hpos.2⟩
    exact fun _ _ => ⟨hn,unit_not_negative_normalize hpos.1,
      unit_not_negative_normalize hpos.2,fun _ hv _ => hv⟩
  · let γ : ℝ → Vec := fun t => first n (normalize p) t
    have hγ : ContDiffOn ℝ ∞ γ (Icc (0 : ℝ) 1) := by
      intro t ht
      exact (crossing_normal_path_smoothAt
        (n := fun _ : ℝ => n) (p := fun _ : ℝ => p) (m := fun _ : ℝ => m)
        contDiffAt_const contDiffAt_const contDiffAt_id hn hnm hpm ht).contDiffWithinAt
    refine ⟨γ,hγ,first_zero hn,?_,?_⟩
    · intro t ht
      obtain ⟨hunit,hp,hq⟩ := crossing_normal_path hn hnm hpm hqm ht
      refine ⟨hunit,hp,hq,?_⟩
      intro v hvn hvp
      change v ⬝ᵥ normalize (blend n (normalize p) t) = 0
      apply dot_normalize_zero
      simp only [blend,dotProduct_add,dotProduct_smul,smul_eq_mul,hvn,
        show v ⬝ᵥ normalize p = 0 from dot_normalize_zero hvp,mul_zero,add_zero]
    · exact crossing_normal_path_endpoint hpm hacute

end ClosedSurfaceR4.VelocityFrame

end

end OAI
