import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyStrongSeed

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Filter Metric
open scoped Topology ContDiff

def leftParameter : Parameter := ⟨ShootingParameters.leftEnd,le_rfl,
  by norm_num [ShootingParameters.leftEnd,ShootingParameters.rightEnd]⟩
def rightParameter : Parameter := ⟨ShootingParameters.rightEnd,
  by norm_num [ShootingParameters.leftEnd,ShootingParameters.rightEnd],le_rfl⟩

theorem UniformGerm.exists_uniform_euler_seed (G : UniformGerm) :
    ∃ e : ℝ, 0<e ∧ e<1/3 ∧ |SourceEuler.changeOfVariable (1/500) e|<G.radius ∧
      Continuous (fun p => G.eulerFunction p e) ∧
      (∀ p, 0<G.eulerFunction p e ∧ G.eulerFunction p e<1-e/1000) ∧
      (∀ p ∈ ({leftParameter,rightParameter}:Set Parameter),
        (EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction p)) (-1/1000)).eval e<G.eulerFunction p e ∧
        G.eulerFunction p e<(EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction p)) (1/1000)).eval e) ∧
      ∀ p x, |x|≤|SourceEuler.changeOfVariable (1/500) e| →
        0<G.realFunction p x ∧ 1/2<(G.V p (x:ℂ)).re := by
  have hentry (p:Parameter) := EulerPolynomial.exists_barrier_entry (G.eulerFunction p)
    (G.euler_data p).1.contDiffAt (1/1000) (by norm_num)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp ((hentry leftParameter).and (hentry rightParameter))
  obtain ⟨δ,hδ,hδr,hδlim,hδsmall,hseed,hrange,hwhole⟩ := G.exists_uniform_strong_seed (ε/1000) (by positivity)
  let e : ℝ := δ/(1/500+δ)
  have hd : 0<1/500+δ := by positivity
  have he0 : 0<e := div_pos hδ hd
  have hethird : e<1/3 := by
    rw [show e=δ/(1/500+δ) from rfl,div_lt_iff₀ hd]
    linarith
  have heε : e<ε := by
    have he500 : e<500*δ := by
      rw [show e=δ/(1/500+δ) from rfl,div_lt_iff₀ hd]
      nlinarith [sq_pos_of_pos hδ]
    linarith
  have he1 : 1-e≠0 := by linarith
  have htrans : SourceEuler.changeOfVariable (1/500) e= -δ := by
    dsimp [SourceEuler.changeOfVariable,e]
    field_simp
    ring
  have hfun (p:Parameter) : G.eulerFunction p e=(G.U p ((-δ:ℝ):ℂ)).re := by
    simp only [UniformGerm.eulerFunction,Function.comp_apply,htrans,UniformGerm.realFunction]
  have hcap : e/1000<δ/2 := by
    have hmul : e<500*δ := by
      rw [show e=δ/(1/500+δ) from rfl,div_lt_iff₀ hd]
      nlinarith [sq_pos_of_pos hδ]
    linarith
  refine ⟨e,he0,hethird,?_,?_,?_,?_,?_⟩
  · rw [htrans,abs_neg,abs_of_pos hδ]
    exact hδr
  · simpa only [hfun] using hseed
  · intro p
    rw [hfun]
    exact ⟨(hrange p).1,by linarith [(hrange p).2]⟩
  · intro p hp
    have hh := hεsub (show e ∈ ball (0:ℝ) ε by
      rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos he0];exact heε)
    obtain rfl | rfl := hp
    · simpa only [neg_div] using hh.1 he0
    · simpa only [neg_div] using hh.2 he0

  · intro p x hx
    rw [htrans,abs_neg,abs_of_pos hδ] at hx
    exact hwhole p x hx

end SepticProfile.SourceFamily

end
end

end OAI
