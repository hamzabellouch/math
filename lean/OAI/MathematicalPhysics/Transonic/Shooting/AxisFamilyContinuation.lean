import OAI.MathematicalPhysics.Transonic.Shooting.AxisFamilySeed
import OAI.MathematicalPhysics.Transonic.Shooting.ShootingField
import OAI.MathematicalPhysics.Transonic.Shooting.ClampedComparison

namespace OAI

section
noncomputable section

namespace SepticProfile.AxisFamily
open Set Metric SourceFamily RegularContinuation AxisBarriers

theorem exists_continuous_regular_family {δ : ℝ} (hδ : 0<δ) (hδb : δ≤9/10)
    (seed : Parameter → ℝ) (hseed : Continuous seed)
    (hseedrange : ∀ a, seed a ∈ Icc (lower δ) (upper δ)) :
    ∃ u : Parameter → ℝ → ℝ,
      Continuous (fun p : Parameter × ↥(Icc δ (9/10)) => u p.1 p.2) ∧
      (∀ a, u a δ=seed a) ∧
      (∀ a z, z ∈ Icc δ (9/10) → lower z≤u a z ∧ u a z≤upper z) ∧
      ∀ a z, z ∈ Icc δ (9/10) → HasDerivWithinAt (u a)
        (N (kap a) z (u a z)/D (sig a) z (u a z)) (Icc δ (9/10)) z := by
  obtain ⟨u,huc,hu0,hud⟩ := exists_continuous_clamped_family hδb
    (show ShootingParameters.leftEnd≤ShootingParameters.rightEnd by
      norm_num [ShootingParameters.leftEnd,ShootingParameters.rightEnd])
    (by norm_num : (0:ℝ)≤9/10)
    (ShootingField.field_contDiffOn hδ (by norm_num) (by norm_num))
    (fun a:Parameter => a.val) seed continuous_subtype_val hseed (fun a => a.property)
  have hb (a:Parameter) :
      (∀ z ∈ Icc δ (9/10), u a z ∈ Icc (lower z) (upper z)) ∧
      ∀ z ∈ Icc δ (9/10), HasDerivWithinAt (u a)
        (N (kap a) z (u a z)/D (sig a) z (u a z)) (Icc δ (9/10)) z := by
    have hc : ContinuousOn (u a) (Icc δ (9/10)) := fun z hz => (hud a z hz).continuousWithinAt
    have hder : ∀ z ∈ Icc δ (9/10), HasDerivWithinAt (u a)
        ((fun p:ℝ×ℝ => N (kap a) p.1 p.2/D (sig a) p.1 p.2)
          (z,clamp 0 (9/10) (u a z))) (Icc δ (9/10)) z := hud a
    have htz {z:ℝ} (hz:z ∈ Icc δ (9/10)) : z ∈ Icc 0 (9/10) :=
      ⟨hδ.le.trans hz.1,hz.2⟩
    have htp {z:ℝ} (hz:z ∈ Icc δ (9/10)) : z ∈ Ioc 0 (9/10) :=
      ⟨hδ.trans_le hz.1,hz.2⟩
    have hsl : 991/1000≤ sig a := (ShootingParameters.sigma_shooting_bounds a.property).1.le
    have hsu : sig a≤993/1000 := (ShootingParameters.sigma_shooting_bounds a.property).2.le
    have hkl : -(1/500:ℝ)≤kap a := (ShootingParameters.kappa_bounds a.property).1.le
    have hku : kap a≤0 := (ShootingParameters.kappa_bounds a.property).2.le
    have hlo (z:ℝ) (hz:z ∈ Icc δ (9/10)) : lower z ∈ Icc 0 (9/10) := by
      refine ⟨(barriers_in_unit (htz hz)).1,?_⟩
      dsimp [lower]
      linarith [hz.2]
    have hhi (z:ℝ) (hz:z ∈ Icc δ (9/10)) : upper z ∈ Icc 0 (9/10) :=
      ⟨(barriers_in_unit (htz hz)).2.2.1,(upper_lt_nine_tenths (htz hz)).le⟩
    apply clamped_stays_between_strict (f := fun p:ℝ×ℝ => N (kap a) p.1 p.2/D (sig a) p.1 p.2) hc hder lower upper (fun _ => 749/1000) upperDeriv
    · intro z _
      change HasDerivAt (fun x:ℝ => (749/1000)*x) (749/1000) z
      exact hasDerivAt_const_mul (749/1000:ℝ)
    · exact fun z hz => upper_hasDeriv (htz hz)
    · exact hlo
    · exact hhi
    · intro z hz
      exact (lt_div_iff₀ (D_pos hsu (htp hz) (hlo z hz))).mpr
        (by simpa [mul_comm] using lower_strict_barrier hsl hkl (htp hz))
    · intro z hz
      exact (div_lt_iff₀ (D_pos hsu (htp hz) (hhi z hz))).mpr
        (by simpa [mul_comm] using upper_strict_barrier hsu hku (htp hz))
    · rw [hu0]
      exact hseedrange a
  exact ⟨u,huc,hu0,fun a => (hb a).1,fun a => (hb a).2⟩

theorem exists_continuous_axis_shoot :
    ∃ G : UniformGerm, ∃ δ : ℝ, 0<δ ∧ δ^2<G.radius ∧ δ<1/1000 ∧
    (∀ a z, z ∈ Ioc 0 δ → (749/1000)*z<z*(G.G a ((z^2:ℝ):ℂ)).re ∧
      z*(G.G a ((z^2:ℝ):ℂ)).re<(3/4)*z) ∧
    ∃ u : Parameter → ℝ → ℝ,
      Continuous (fun p : Parameter × ↥(Icc δ (9/10)) => u p.1 p.2) ∧
      (∀ a, u a δ=δ*(G.G a ((δ^2:ℝ):ℂ)).re) ∧
      (∀ a z, z ∈ Icc δ (9/10) → lower z≤u a z ∧ u a z≤upper z) ∧
      ∀ a z, z ∈ Icc δ (9/10) → HasDerivWithinAt (u a)
        (N (kap a) z (u a z)/D (sig a) z (u a z)) (Icc δ (9/10)) z := by
  obtain ⟨G⟩ := exists_uniform_germ
  obtain ⟨δ,hδ,hδr,hδlim,hδsmall,hseed,hrange,hgerm⟩ := G.exists_uniform_seed 1 (by norm_num)
  have hδb : δ≤9/10 := by linarith
  have hseedrange (a:Parameter) : δ*(G.G a ((δ^2:ℝ):ℂ)).re ∈ Icc (lower δ) (upper δ) := by
    refine ⟨(hrange a).1.le,(hrange a).2.le.trans ?_⟩
    have hpd : 0<polyDen (δ^2) := by linarith [polyDen_pos ⟨hδ.le,hδb⟩]
    have hpu : polyDen (δ^2)≤1 := by dsimp [polyDen];nlinarith [sq_nonneg δ,sq_nonneg (δ^2)]
    unfold upper
    rw [le_div_iff₀ hpd]
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hpu)]
  obtain ⟨u,hu⟩ := exists_continuous_regular_family hδ hδb _ hseed hseedrange
  exact ⟨G,δ,hδ,hδr,hδsmall,hgerm,u,hu⟩

end SepticProfile.AxisFamily

end
end

end OAI
