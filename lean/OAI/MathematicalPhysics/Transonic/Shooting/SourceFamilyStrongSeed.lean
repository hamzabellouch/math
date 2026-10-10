import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyEuler

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Metric

lemma slope_gt_one (t : Parameter) : 1<slp t := by
  change 1<ShootingParameters.slope t.val
  rw [ShootingParameters.slope,lt_div_iff₀ (mul_pos (by norm_num) (ShootingParameters.a_pos t.property))]
  have ht := (ShootingParameters.rough_bounds t.property).2
  dsimp [ShootingParameters.e,ShootingParameters.a]
  nlinarith

/-- A common inward sonic starting point for every parameter in the shooting
chart. Its compact margin from the singular value1 is positive, as required
before an ordinary ODE (with a proved nonsingular denominator) can be used. -/
theorem UniformGerm.exists_uniform_strong_seed (G : UniformGerm) (limit : ℝ) (hlimit : 0<limit) :
    ∃ δ : ℝ, 0<δ ∧ δ<G.radius ∧ δ<limit ∧ δ<1/1000 ∧
      Continuous (fun a => (G.U a ((-δ:ℝ):ℂ)).re) ∧
      (∀ a, 0<(G.U a ((-δ:ℝ):ℂ)).re ∧ (G.U a ((-δ:ℝ):ℂ)).re<1-δ/2) ∧
      ∀ a x, |x|≤δ → 0<(G.U a (x:ℂ)).re ∧ 1/2<(G.V a (x:ℂ)).re := by
  let Z := ↥(closedBall (0:ℂ) G.radius)
  let z0 : Z := ⟨0,mem_closedBall_self G.radius_pos.le⟩
  let W : Set (Parameter × Z) := {p | 0<(G.U p.1 p.2).re ∧ 1/2<(G.V p.1 p.2).re}
  have hopen : IsOpen W :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp G.jointContinuous)).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp G.jointV))
  have hsub : (univ:Set Parameter) ×ˢ ({z0}:Set Z) ⊆ W := by
    rintro ⟨a,z⟩ ⟨_,hz⟩
    have hz' : z=z0 := hz
    subst z
    change 0<(G.U a 0).re ∧ 1/2<(G.V a 0).re
    rw [G.value,G.Vzero]
    exact ⟨by norm_num, by change (1/2:ℝ)<slp a;linarith [slope_gt_one a]⟩
  obtain ⟨U,T,hU,hT,hAU,h0T,hUT⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hopen hsub
  obtain ⟨ε,hε,hεT⟩ := Metric.isOpen_iff.mp hT z0 (h0T (by simp))
  let δ : ℝ := min (G.radius/2) (min (ε/2) (min (limit/2) (1/2000)))
  have hδ : 0<δ := by have := G.radius_pos;dsimp [δ];positivity
  have hδr : δ<G.radius := (min_le_left _ _).trans_lt (by linarith [G.radius_pos])
  have hδε : δ<ε := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδb : δ<limit := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδsmall : δ<1/1000 := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hnorm : ‖((-δ:ℝ):ℂ)‖=δ := by simp [Complex.norm_real,abs_of_pos hδ]
  let zδ : Z := ⟨((-δ:ℝ):ℂ),mem_closedBall_zero_iff.mpr (by rw [hnorm];exact hδr.le)⟩
  have hzδ : zδ ∈ T := by
    apply hεT
    change dist (((-δ:ℝ):ℂ)) (0:ℂ)<ε
    rw [dist_zero_right,hnorm]
    exact hδε
  have hV (a:Parameter) : 0<(G.U a ((-δ:ℝ):ℂ)).re ∧ 1/2<(G.V a ((-δ:ℝ):ℂ)).re :=
    hUT (show (a,zδ) ∈ U ×ˢ T from ⟨hAU (mem_univ a),hzδ⟩)
  have hlt (a:Parameter) : (G.U a ((-δ:ℝ):ℂ)).re<1-δ/2 := by
    rw [G.split]
    simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    nlinarith [(hV a).2]
  have hc : Continuous (fun a => (G.U a ((-δ:ℝ):ℂ)).re) :=
    Complex.continuous_re.comp (G.jointContinuous.comp (continuous_id.prodMk (continuous_const (y:=zδ))))
  refine ⟨δ,hδ,hδr,hδb,hδsmall,hc,fun a => ⟨(hV a).1,hlt a⟩,?_⟩
  intro a x hx
  have hnormx : ‖(x:ℂ)‖=|x| := by simp [Complex.norm_real,Real.norm_eq_abs]
  let zx : Z := ⟨(x:ℂ),mem_closedBall_zero_iff.mpr (by rw [hnormx];exact (hx.trans_lt hδr).le)⟩
  have hzx : zx ∈ T := by
    apply hεT
    change dist (x:ℂ) (0:ℂ)<ε
    rw [dist_zero_right,hnormx]
    exact hx.trans_lt hδε
  exact hUT (show (a,zx) ∈ U ×ˢ T from ⟨hAU (mem_univ a),hzx⟩)

end SepticProfile.SourceFamily

end
end

end OAI
