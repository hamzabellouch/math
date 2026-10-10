import Mathlib
import OAI.Analysis.Conductivity.Sobolev.WallPrimitive

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def wallAlong (d : E) (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  fderiv ℝ f p (d,0)

lemma wallAlong_smooth [ProperSpace E] (d : E) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallAlong d f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma wallDerivative_add [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q+g q) p=wallDerivative f p+wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_add (hf p) (hg p),add_apply]

lemma wallDerivative_sub [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q-g q) p=wallDerivative f p-wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_sub (hf p) (hg p),sub_apply]

lemma wallDerivative_mul [ProperSpace E] {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallDerivative (fun q => f q*g q) p=wallDerivative f p*g p+f p*wallDerivative g p := by
  simp only [wallDerivative,fderiv_fun_mul (hf p) (hg p),add_apply,
    smul_apply,smul_eq_mul]
  ring

def wallParticularNumerator (d : E) (v r₁ r₂ : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  wallPrimitive (fun q => r₂ q-wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) q) p
    -wallPrimitive r₁ p*wallAlong d v p

lemma wallParticularNumerator_smooth [ProperSpace E] (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallParticularNumerator d v r₁ r₂) := by
  exact (wallPrimitive_smooth (h₂.sub (wallAlong_smooth d
    ((wallPrimitive_smooth h₁).mul (wallDerivative_smooth hv))))).sub
      ((wallPrimitive_smooth h₁).mul (wallAlong_smooth d hv))

lemma wallParticularNumerator_zero [ProperSpace E] (d : E) (v r₁ r₂ : E × ℝ → ℝ) (x : E) :
    wallParticularNumerator d v r₁ r₂ (x,0)=0 := by
  simp only [wallParticularNumerator,wallPrimitive_zero,zero_mul,sub_zero]

theorem wall_particular_flux_equations [ProperSpace E] (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂) (p : E × ℝ) :
    wallDerivative (wallPrimitive r₁) p=r₁ p ∧
    wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) p+
      wallDerivative (fun q => wallPrimitive r₁ q*wallAlong d v q+
        wallParticularNumerator d v r₁ r₂ q) p=r₂ p := by
  refine ⟨wallDerivative_primitive h₁ p,?_⟩
  let B : E × ℝ → ℝ := fun q =>
    r₂ q-wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) q
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B := h₂.sub (wallAlong_smooth d
    ((wallPrimitive_smooth h₁).mul (wallDerivative_smooth hv)))
  have he : (fun q => wallPrimitive r₁ q*wallAlong d v q+
      wallParticularNumerator d v r₁ r₂ q)=wallPrimitive B := by
    funext q; simp only [wallParticularNumerator,B]; ring
  rw [he,wallDerivative_primitive hB]
  dsimp [B]; ring

lemma wall_ratio_multiply [ProperSpace E] {f g : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hf0 : ∀ x, f (x,0)=0) (hg0 : ∀ x, g (x,0)=0)
    (p : E × ℝ) (hq : wallQuotient g p≠0) :
    (wallQuotient f p/wallQuotient g p)*g p=f p := by
  rw [(smooth_wall_division hg hg0).2 p,(smooth_wall_division hf hf0).2 p]
  field_simp

theorem wall_particular_extension [ProperSpace E] (d : E) {v r₁ r₂ : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁)
    (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hz : ∀ x, wallDerivative v (x,0)=0) (x : E)
    (hzz : wallDerivative (wallDerivative v) (x,0)≠0) :
    let H := fun p => wallQuotient (wallParticularNumerator d v r₁ r₂) p/
      wallQuotient (wallDerivative v) p
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) H (x,0) ∧
      (∀ᶠ p in 𝓝 (x,0), H p*wallDerivative v p=wallParticularNumerator d v r₁ r₂ p) ∧
      H (x,0)=(r₂ (x,0)-r₁ (x,0)*wallAlong d v (x,0))/
        wallDerivative (wallDerivative v) (x,0) := by
  let G := wallParticularNumerator d v r₁ r₂
  have hG := wallParticularNumerator_smooth d hv h₁ h₂
  have hG0 := wallParticularNumerator_zero d v r₁ r₂
  have hvz := wallDerivative_smooth hv
  have hq : wallQuotient (wallDerivative v) (x,0)≠0 := by
    simpa only [wallQuotient_zero] using hzz
  refine ⟨(wall_ratio_extension hG hvz hG0 hz x hzz).1,?_,?_⟩
  · filter_upwards [(wallQuotient_smooth hvz).continuous.continuousAt.eventually_ne hq] with p hp
    exact wall_ratio_multiply hG hvz hG0 hz p hp
  · dsimp
    rw [wallQuotient_zero,wallQuotient_zero]
    congr 1
    let B : E × ℝ → ℝ := fun q =>
      r₂ q-wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) q
    have hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B := h₂.sub (wallAlong_smooth d
      ((wallPrimitive_smooth h₁).mul hvz))
    change wallDerivative (fun q => wallPrimitive B q-wallPrimitive r₁ q*wallAlong d v q) (x,0)=_
    rw [wallDerivative_sub ((wallPrimitive_smooth hB).differentiable (by simp))
      (((wallPrimitive_smooth h₁).mul (wallAlong_smooth d hv)).differentiable (by simp)),
      wallDerivative_primitive hB,
      wallDerivative_mul ((wallPrimitive_smooth h₁).differentiable (by simp))
        ((wallAlong_smooth d hv).differentiable (by simp)),
      wallDerivative_primitive h₁,wallPrimitive_zero,zero_mul,add_zero]
    suffices he : wallAlong d (fun q => wallPrimitive r₁ q*wallDerivative v q) (x,0)=0 by
      simp only [B,he,sub_zero]
    simp only [wallAlong,fderiv_fun_mul
      ((wallPrimitive_smooth h₁).differentiable (by simp) (x,0))
      (hvz.differentiable (by simp) (x,0)),wallPrimitive_zero,hz,
      zero_smul,add_zero,zero_apply]

end ScalarConductivity

end

end OAI
