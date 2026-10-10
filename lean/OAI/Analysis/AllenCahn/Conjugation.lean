import OAI.Analysis.AllenCahn.DefectLimits

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped ContDiff
open Filter Topology

lemma defect_conjugation {n : ℕ} {d : Space n → ℝ} (hd : ContDiff ℝ ∞ d)
    {ν : Space n} (hν : ‖ν‖=1) (q : Space n → ℝ)
    (heq : ∀ x, Laplacian.laplacian d x = -2*q x+
      2*Real.sqrt 2*profile (inner ℝ ν x)*inner ℝ ν (gradient d x)+
      2*profileWeight (inner ℝ ν x)*d x) (x : Space n) :
    -Laplacian.laplacian (fun z => profileWeight (inner ℝ ν z)*d z) x+
      (2-profileWeight (inner ℝ ν x))*(profileWeight (inner ℝ ν x)*d x) =
      2*profileWeight (inner ℝ ν x)*q x := by
  have hlin : ContDiff ℝ 2 (fun z : Space n => inner ℝ ν z) := (innerSL ℝ ν).contDiff
  have hG : ContDiff ℝ ∞ (fun z : Space n => profileWeight (inner ℝ ν z)) :=
    profileWeight_contDiff.comp (innerSL ℝ ν).contDiff
  have hL : Laplacian.laplacian (fun z : Space n => profileWeight (inner ℝ ν z)) x =
      (3*profile (inner ℝ ν x)^2-1)*profileWeight (inner ℝ ν x) := by
    rw [laplacian_comp_scalar hlin (smooth_C2 hG)
      (fun z => (profileWeight_hasDerivAt _).differentiableAt)
      (fun z => (profileWeight_hasDerivAt_twice _).differentiableAt),
      (profileWeight_hasDerivAt_twice _).deriv,gradient_inner,hν,laplacian_inner]
    ring
  rw [laplacian_fun_mul (smooth_C2 hG)
    (smooth_C2 hd),hL,gradient_comp_inner (profileWeight_contDiff.differentiable (by simp)),
    (profileWeight_hasDerivAt _).deriv,real_inner_smul_left,heq]
  dsimp [profileWeight]
  ring

theorem SmallDefectConverges.conjugated_equation {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (h0 : ∀ j, v j 0=0)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) {ν : Space n}
    (hν : ‖ν‖=1) (horient : ∀ j, gradient (inverseProfile (v j)) 0 =
      Real.sqrt (1-diffuseDefect (v j) 0) • ν) (x : Space n) :
    -Laplacian.laplacian (fun z => profileWeight (inner ℝ ν z)*g (some none) z) x+
     (2-profileWeight (inner ℝ ν x))*(profileWeight (inner ℝ ν x)*g (some none) x) =
       2*profileWeight (inner ℝ ν x)*
         (∑ i : Fin n, ∑ j : Fin n, g (some (some (i,j))) x^2) := by
  apply defect_conjugation (hg.1 (some none)) hν
  intro z
  have HH := hg.defect_equation hv he z
  rw [hg.profile_limit hv h0 he horient] at HH
  rw [← inner_gradient_eq_sum,gradient_inner] at HH
  exact HH

end DeGiorgi
end

end OAI
