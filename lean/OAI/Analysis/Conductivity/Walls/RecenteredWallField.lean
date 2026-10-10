import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly
import OAI.Analysis.Conductivity.Walls.ParametricWallOperators
import OAI.Analysis.Conductivity.Walls.FlattenedWall

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma wallDerivative_eq_of_hasDeriv {f : E×ℝ → ℝ} (hf : Differentiable ℝ f)
    {q : E} {z d : ℝ} (hd : HasDerivAt (fun t => f (q,t)) d z) :
    wallDerivative f (q,z)=d := (real_section_hasDeriv hf q z).unique hd

theorem exists_recentered_critical_wall
    {v : P×(E×ℝ) → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P) (q : E)
    (hz : ∀ y,wallDerivative (fun x => v (p,x)) (y,0)=0)
    (hne : wallDerivative (wallDerivative (fun x => v (p,x))) (q,0)≠0) :
    ∃ ρ : P×E → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧ (∀ y,ρ (p,y)=0) ∧
      ∃ w : P×(E×ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=v (p,y)) ∧
        (∀ r y,wallDerivative (fun x => w (r,x)) (y,0)=0) ∧
        ∀ᶠ a in 𝓝 (p,q),∀ z,w (a.1,(a.2,z))=v (a.1,(a.2,z+ρ a)) := by
  let d : P×(E×ℝ) → ℝ := fun a => wallDerivative (fun x => v (a.1,x)) a.2
  have hd : ContDiff ℝ (↑(⊤:ℕ∞)) d := wallDerivative_parametric_smooth hv
  let g : (P×E)×ℝ → ℝ := fun a => d (a.1.1,(a.1.2,a.2))
  have hg : ContDiff ℝ (↑(⊤:ℕ∞)) g := hd.comp (contDiff_fst.fst.prodMk
    (contDiff_fst.snd.prodMk contDiff_snd))
  have hgn : wallDerivative g ((p,q),0)≠0 := by
    have he : wallDerivative g ((p,q),0)=wallDerivative (wallDerivative (fun x => v (p,x))) (q,0) := by
      apply wallDerivative_eq_of_hasDeriv (hg.differentiable (by simp))
      exact real_section_hasDeriv ((wallDerivative_smooth
        (hv.comp (contDiff_const.prodMk contDiff_id))).differentiable (by simp)) q 0
    exact he ▸ hne
  obtain ⟨ρ,hρ,hρ0,hroot⟩ := exists_flat_parametric_root hg p q hz hgn
  let a : P×E → ℝ := fun y => g (y,ρ y)
  have ha : ContDiff ℝ (↑(⊤:ℕ∞)) a := hg.comp (contDiff_id.prodMk hρ)
  let R : P×(E×ℝ) → P×(E×ℝ) := fun y => (y.1,(y.2.1,y.2.2+ρ (y.1,y.2.1)))
  have hR : ContDiff ℝ (↑(⊤:ℕ∞)) R := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk (contDiff_snd.snd.add (hρ.comp (contDiff_fst.prodMk contDiff_snd.fst))))
  let w : P×(E×ℝ) → ℝ := fun y => v (R y)-y.2.2*a (y.1,y.2.1)
  have hw : ContDiff ℝ (↑(⊤:ℕ∞)) w :=
    (hv.comp hR).sub (contDiff_snd.snd.mul (ha.comp (contDiff_fst.prodMk contDiff_snd.fst)))
  refine ⟨ρ,hρ,hρ0,w,hw,?_,?_,?_⟩
  · intro y
    simp only [w,R,a,g,d,hρ0,add_zero,hz,mul_zero,sub_zero]
  · intro r y
    apply wallDerivative_eq_of_hasDeriv ((hw.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
    have h1 := (real_section_hasDeriv (g:=fun x : E×ℝ => v (r,x)) ((hv.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp)) y (0+ρ (r,y))).comp 0 ((hasDerivAt_id (0:ℝ)).add_const (ρ (r,y)))
    have h2 := (hasDerivAt_id (0:ℝ)).mul_const (a (r,y))
    simpa only [w,R,Function.comp_def,id_eq,Pi.sub_def,mul_one,one_mul,a,g,d,zero_add,sub_self] using h1.sub h2
  · filter_upwards [hroot] with y hy
    intro z
    simp only [w,R,a,hy,mul_zero,sub_zero]

end ScalarConductivity

end
end

end OAI
