import Mathlib
import OAI.Geometry.SplitTangent.AmbientLeafSections
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProjectiveLineFrame
import OAI.Geometry.SplitTangent.RationalCurveFrames

namespace OAI

/-! Curve Homogeneous Sections. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {e : ProjectiveEmbedding X} {g : RationalCurve X}
  (F : RationalCurveFrames e g)

lemma multiplier_holomorphicAt (z : ℂ) :
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω (F.multiplier z) (g.finite z) := by
  apply contMDiffAt_finsetSum
  intro i hi
  exact (contMDiffAt_const (I' := 𝓘(ℂ,ℂ))).mul
    (contMDiffAt_pi_space.mp (F.finite_holomorphicAt z) i)

lemma multiplier_formula (z : ℂ) (x : X.Carrier) :
    F.multiplier z x=(∑i,(F.a i).eval z*(e.map x).rep i)⁻¹ *
      (∑i,(F.b i).eval z⁻¹*(e.map x).rep i) := by
  simp only [multiplier,finite,ProjectiveEmbedding.linearFrame,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma frame_transition_eventually {z : ℂ} (hz : z≠0) :
    ∀ᶠ x in 𝓝 (g.finite z),F.finite z x=F.multiplier z x • F.infinity z⁻¹ x := by
  have hc := (F.multiplier_holomorphicAt z).continuousAt
  have hvalue : F.multiplier z (g.finite z)≠0 := by
    rw [F.multiplier_on_curve hz]
    exact pow_ne_zero _ hz
  filter_upwards [hc.eventually_ne hvalue] with x hx
  apply F.frame_transition
  rw [F.multiplier_formula] at hx
  exact (mul_ne_zero_iff.mp hx).2

 

def ambientTransition (a k : ℕ) : AmbientTransition g (a+k*F.degree) where
  multiplier q := q.1^a*(F.multiplier q.1 q.2)^k
  holomorphic z hz := by
    change ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
      ((fun _ => z^a)*(fun x => (F.multiplier z x)^k)) (g.finite z)
    exact (contMDiffAt_const (I' := 𝓘(ℂ,ℂ))).mul ((F.multiplier_holomorphicAt z).pow k)
  value z hz := by
    dsimp only
    rw [F.multiplier_on_curve hz,pow_add,←pow_mul,Nat.mul_comm F.degree k]

abbrev HomogeneousTuple (a k : ℕ) :=
  Fin (a+1) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k

 
def sections (a k : ℕ) : HomogeneousTuple (e := e) a k →ₗ[ℂ]
    ambientSectionSpace (F.ambientTransition a k) where
  toFun p := ⟨(
    fun q => ∑i : Fin (a+1),q.1^i.val*MvPolynomial.eval (F.finite q.1 q.2) (p i).val,
    fun q => ∑i : Fin (a+1),q.1^(a-i.val)*MvPolynomial.eval (F.infinity q.1 q.2) (p i).val),by
      refine ⟨?_,?_,?_⟩
      · intro z
        dsimp only [Prod.fst,Prod.snd]
        apply contMDiffAt_finsetSum
        intro i hi
        exact (contMDiffAt_fst.pow i.val).mul
          (MvPolynomial.contMDiffAt_eval_comp _ _
            (fun j => contMDiffAt_pi_space.mp (F.finite_joint_holomorphicAt z) j))
      · intro z
        dsimp only [Prod.fst,Prod.snd]
        apply contMDiffAt_finsetSum
        intro i hi
        exact (contMDiffAt_fst.pow (a-i.val)).mul
          (MvPolynomial.contMDiffAt_eval_comp _ _
            (fun j => contMDiffAt_pi_space.mp (F.infinity_joint_holomorphicAt z) j))
      · intro z hz
        filter_upwards [F.frame_transition_eventually hz] with x hx
        change (∑i : Fin (a+1),z^i.val*MvPolynomial.eval (F.finite z x) (p i).val)=
          (z^a*(F.multiplier z x)^k)*(∑i : Fin (a+1),z⁻¹^(a-i.val)*MvPolynomial.eval (F.infinity z⁻¹ x) (p i).val)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hx,_root_.OAI.MvPolynomial.IsHomogeneous.eval_scale (p i).property]
        have he : z^a*z⁻¹^(a-i.val)=z^i.val := by
          rw [inv_pow,←pow_sub₀ z hz (by omega)]
          congr 1
          omega
        calc
          _ = (z^a*z⁻¹^(a-i.val))*((F.multiplier z x)^k*MvPolynomial.eval (F.infinity z⁻¹ x) (p i).val) := by rw [he]
          _ = _ := by ring⟩
  map_add' p q := by
    apply Subtype.ext
    apply Prod.ext <;> funext x
    all_goals simp only [Pi.add_apply,Submodule.coe_add,MvPolynomial.eval_add,mul_add,Finset.sum_add_distrib,Prod.fst_add,Prod.snd_add]
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · funext x
      change (∑i : Fin (a+1),x.1^i.val*MvPolynomial.eval (F.finite x.1 x.2) (c • (p i).val))=
        c*(∑i : Fin (a+1),x.1^i.val*MvPolynomial.eval (F.finite x.1 x.2) (p i).val)
      simp only [MvPolynomial.smul_eval,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · funext x
      change (∑i : Fin (a+1),x.1^(a-i.val)*MvPolynomial.eval (F.infinity x.1 x.2) (c • (p i).val))=
        c*(∑i : Fin (a+1),x.1^(a-i.val)*MvPolynomial.eval (F.infinity x.1 x.2) (p i).val)
      simp only [MvPolynomial.smul_eval,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end SplitTangent.RationalCurveFrames

end

end OAI
