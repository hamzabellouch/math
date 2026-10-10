import OAI.MathematicalPhysics.Transonic.Shooting.AxisFamilyGerm
import OAI.MathematicalPhysics.Transonic.Shooting.ShootingBounds

namespace OAI

section
noncomputable section

namespace SepticProfile.AxisFamily
open Set Metric SourceFamily

lemma initial_slope_bounds (a : Parameter) :
    (749/1000:ℝ)<(kap a+3)/4 ∧ (kap a+3)/4<3/4 := by
  have hk := ShootingParameters.kappa_bounds a.property
  change -(1/500:ℝ)<kap a ∧ kap a<0 at hk
  constructor <;> linarith [hk.1,hk.2]

theorem UniformGerm.exists_uniform_seed (G : UniformGerm) (limit : ℝ) (hlimit : 0<limit) :
    ∃ δ : ℝ, 0<δ ∧ δ^2<G.radius ∧ δ<limit ∧ δ<1/1000 ∧
      Continuous (fun a => δ*(G.G a ((δ^2:ℝ):ℂ)).re) ∧
      (∀ a, (749/1000)*δ<δ*(G.G a ((δ^2:ℝ):ℂ)).re ∧
        δ*(G.G a ((δ^2:ℝ):ℂ)).re<(3/4)*δ) ∧
      ∀ a z, z ∈ Ioc 0 δ → (749/1000)*z<z*(G.G a ((z^2:ℝ):ℂ)).re ∧
        z*(G.G a ((z^2:ℝ):ℂ)).re<(3/4)*z := by
  let Z := ↥(closedBall (0:ℂ) G.radius)
  let z0 : Z := ⟨0,mem_closedBall_self G.radius_pos.le⟩
  let W : Set (Parameter × Z) := {p | 749/1000<(G.G p.1 p.2).re ∧ (G.G p.1 p.2).re<3/4}
  have hopen : IsOpen W :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp G.jointContinuous)).inter
    (isOpen_lt (Complex.continuous_re.comp G.jointContinuous) continuous_const)
  have hsub : (univ:Set Parameter) ×ˢ ({z0}:Set Z) ⊆ W := by
    rintro ⟨a,z⟩ ⟨_,hz⟩
    have hz' : z=z0 := hz
    subst z
    change 749/1000<(G.G a 0).re ∧ (G.G a 0).re<3/4
    rw [G.value]
    simpa using initial_slope_bounds a
  obtain ⟨U,T,hU,hT,hAU,h0T,hUT⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hopen hsub
  obtain ⟨ε,hε,hεT⟩ := Metric.isOpen_iff.mp hT z0 (h0T (by simp))
  let δ : ℝ := min (G.radius/2) (min (ε/2) (min (limit/2) (1/2000)))
  have hδ : 0<δ := by have := G.radius_pos;dsimp [δ];positivity
  have hδr : δ<G.radius := (min_le_left _ _).trans_lt (by linarith [G.radius_pos])
  have hδε : δ<ε := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδb : δ<limit := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδsmall : δ<1/1000 := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hδsq : δ^2<δ := by nlinarith
  have hnorm : ‖((δ^2:ℝ):ℂ)‖=δ^2 := by simp [Complex.norm_real]
  let zδ : Z := ⟨((δ^2:ℝ):ℂ),mem_closedBall_zero_iff.mpr (by rw [hnorm];exact (hδsq.trans hδr).le)⟩
  have hzδ : zδ ∈ T := by
    apply hεT
    change dist (((δ^2:ℝ):ℂ)) (0:ℂ)<ε
    rw [dist_zero_right,hnorm]
    exact hδsq.trans hδε
  have hV (a:Parameter) : 749/1000<(G.G a ((δ^2:ℝ):ℂ)).re ∧ (G.G a ((δ^2:ℝ):ℂ)).re<3/4 :=
    hUT (show (a,zδ) ∈ U ×ˢ T from ⟨hAU (mem_univ a),hzδ⟩)
  have hc : Continuous (fun a => δ*(G.G a ((δ^2:ℝ):ℂ)).re) :=
    continuous_const.mul (Complex.continuous_re.comp (G.jointContinuous.comp
      (continuous_id.prodMk (continuous_const (y:=zδ)))))
  refine ⟨δ,hδ,hδsq.trans hδr,hδb,hδsmall,hc,fun a =>
    ⟨by nlinarith [mul_pos hδ (sub_pos.mpr (hV a).1)],
     by nlinarith [mul_pos hδ (sub_pos.mpr (hV a).2)]⟩,?_⟩
  intro a x hx
  have hx2 : x^2≤δ^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1] : 0≤δ+x)]
  have hnormx : ‖((x^2:ℝ):ℂ)‖=x^2 := by simp [Complex.norm_real]
  let zx : Z := ⟨((x^2:ℝ):ℂ),mem_closedBall_zero_iff.mpr (by rw [hnormx];exact (hx2.trans_lt (hδsq.trans hδr)).le)⟩
  have hzx : zx ∈ T := by
    apply hεT
    change dist (((x^2:ℝ):ℂ)) (0:ℂ)<ε
    rw [dist_zero_right,hnormx]
    exact hx2.trans_lt (hδsq.trans hδε)
  have hvx : 749/1000<(G.G a ((x^2:ℝ):ℂ)).re ∧ (G.G a ((x^2:ℝ):ℂ)).re<3/4 :=
    hUT (show (a,zx) ∈ U ×ˢ T from ⟨hAU (mem_univ a),hzx⟩)
  constructor <;> nlinarith [mul_pos hx.1 (sub_pos.mpr hvx.1),mul_pos hx.1 (sub_pos.mpr hvx.2)]

end SepticProfile.AxisFamily

end
end

end OAI
