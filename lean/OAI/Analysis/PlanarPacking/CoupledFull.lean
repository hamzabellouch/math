import OAI.Analysis.PlanarPacking.FiniteFull

namespace OAI

/-!
# The coupled interpolation system

The finite inverse and tail estimates solve the interpolation equations in the space of absolutely summable coefficients.
-/

namespace SharpPlanar
open Numerical

noncomputable def interpolationInverse (neg : Bool) (r : X) : X :=
  Classical.choose (interpolation_exists_unique neg r)
lemma interpolationInverse_eq (neg : Bool) (r : X) :
    interpolationInverse neg r - signedS neg (interpolationInverse neg r) = r :=
  (Classical.choose_spec (interpolation_exists_unique neg r)).1
lemma interpolationInverse_unique (neg : Bool) {x : X} {r : X}
    (hx : x-signedS neg x=r) : x=interpolationInverse neg r :=
  (Classical.choose_spec (interpolation_exists_unique neg r)).2 x hx
noncomputable def coupledLeft (g₁ g₂ : X) : X :=
  (1/2:ℝ) • (interpolationInverse false (g₁+g₂)+interpolationInverse true (g₁-g₂))
noncomputable def coupledRight (g₁ g₂ : X) : X :=
  (1/2:ℝ) • (interpolationInverse false (g₁+g₂)-interpolationInverse true (g₁-g₂))
lemma coupled_equations (g₁ g₂ : X) :
    coupledLeft g₁ g₂-S (coupledRight g₁ g₂)=g₁ ∧
    coupledRight g₁ g₂-S (coupledLeft g₁ g₂)=g₂ := by
  have hp := interpolationInverse_eq false (g₁+g₂)
  have hm := interpolationInverse_eq true (g₁-g₂)
  change interpolationInverse false (g₁+g₂)-S (interpolationInverse false (g₁+g₂))=g₁+g₂ at hp
  change interpolationInverse true (g₁-g₂)- -S (interpolationInverse true (g₁-g₂))=g₁-g₂ at hm
  constructor <;> (apply lp.ext; funext ni)
  all_goals
    have hp' := congrArg (fun x : X => x ni) hp
    have hm' := congrArg (fun x : X => x ni) hm
    simp only [coupledLeft,coupledRight,map_smul,map_add,map_sub,lp.coeFn_sub,lp.coeFn_add,
      lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,lp.coeFn_neg,Pi.neg_apply] at *
    linarith
lemma coupled_unique {g₁ g₂ x₁ x₂ : X} (h₁ : x₁-S x₂=g₁) (h₂ : x₂-S x₁=g₂) :
    x₁=coupledLeft g₁ g₂ ∧ x₂=coupledRight g₁ g₂ := by
  have hp : x₁+x₂=interpolationInverse false (g₁+g₂) := by
    apply interpolationInverse_unique
    change x₁+x₂-S (x₁+x₂)=g₁+g₂
    rw [map_add,← h₁,← h₂]; abel
  have hm : x₁-x₂=interpolationInverse true (g₁-g₂) := by
    apply interpolationInverse_unique
    change x₁-x₂- -S (x₁-x₂)=g₁-g₂
    rw [map_sub,← h₁,← h₂]; abel
  constructor <;> (apply lp.ext; funext ni)
  all_goals
    simp only [coupledLeft,coupledRight]
    rw [← hp,← hm]
    simp only [lp.coeFn_smul,lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring

theorem coupled_exists_unique (g₁ g₂ : X) :
    ∃! x : X×X, x.1-S x.2=g₁ ∧ x.2-S x.1=g₂ := by
  refine ⟨(coupledLeft g₁ g₂,coupledRight g₁ g₂),coupled_equations g₁ g₂,?_⟩
  intro x hx
  exact Prod.ext (coupled_unique hx.1 hx.2).1 (coupled_unique hx.1 hx.2).2
end SharpPlanar

end OAI
