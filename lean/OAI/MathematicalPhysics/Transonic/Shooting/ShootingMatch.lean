import OAI.MathematicalPhysics.Transonic.Shooting.SourceNoReturn
import OAI.MathematicalPhysics.Transonic.Shooting.AxisFamilyContinuation

namespace OAI

section
noncomputable section

namespace SepticProfile.AxisShooting
open Set SourceFamily AxisBarriers

structure Family where
  germ : AxisFamily.UniformGerm
  δ : ℝ
  δ_pos : 0<δ
  δ_radius : δ^2<germ.radius
  δ_lt : δ<1/1000
  germ_range : ∀ a z, z ∈ Ioc 0 δ → (749/1000)*z<z*(germ.G a ((z^2:ℝ):ℂ)).re ∧
    z*(germ.G a ((z^2:ℝ):ℂ)).re<(3/4)*z
  u : Parameter → ℝ → ℝ
  continuous : Continuous (fun p : Parameter × ↥(Icc δ (9/10)) => u p.1 p.2)
  start : ∀ a, u a δ=δ*(germ.G a ((δ^2:ℝ):ℂ)).re
  range : ∀ a z, z ∈ Icc δ (9/10) → lower z≤u a z ∧ u a z≤upper z
  derivative : ∀ a z, z ∈ Icc δ (9/10) → HasDerivWithinAt (u a)
    (N (kap a) z (u a z)/D (sig a) z (u a z)) (Icc δ (9/10)) z

theorem exists_family : Nonempty Family := by
  obtain ⟨G,δ,hδ,hδr,hδlt,hg,u,huc,hu0,hr,hd⟩ := AxisFamily.exists_continuous_axis_shoot
  exact ⟨⟨G,δ,hδ,hδr,hδlt,hg,u,huc,hu0,hr,hd⟩⟩

lemma Family.endpoint_range (A : Family) (p : Parameter) :
    6741/10000≤A.u p (9/10) ∧ A.u p (9/10)<858/1000 := by
  have hr := A.range p (9/10) ⟨by linarith [A.δ_lt],le_rfl⟩
  refine ⟨by norm_num [lower] at hr;exact hr.1,?_⟩
  have hu : upper (9/10:ℝ)<858/1000 := by norm_num [upper,polyDen]
  exact hr.2.trans_lt hu

lemma Family.endpoint_interior (A : Family) (p : Parameter) :
    A.u p (9/10) ∈ Ioo (0:ℝ) (999/1000) := by
  have h := A.endpoint_range p
  constructor <;> linarith [h.1,h.2]

end SepticProfile.AxisShooting

namespace SepticProfile.SonicShooting
open Set SourceFamily

theorem exists_match (F : Family) (A : AxisShooting.Family) :
    ∃ p : Parameter, F.v p (9/100)=A.u p (9/10) := by
  have hf : Continuous (fun p => F.v p (9/100)) :=
    F.v_cont.comp (continuous_id.prodMk (continuous_const (y:=(⟨9/100,by norm_num,le_rfl⟩:↥(Icc (0:ℝ) (9/100))))))
  have ha : Continuous (fun p => A.u p (9/10)) :=
    A.continuous.comp (continuous_id.prodMk (continuous_const (y:=(⟨9/10,by linarith [A.δ_lt],le_rfl⟩:↥(Icc A.δ (9/10))))))
  let : PreconnectedSpace Parameter := Subtype.preconnectedSpace isPreconnected_Icc
  apply intermediate_value_univ₂ (a:=leftParameter) (b:=rightParameter) hf ha
  · linarith [F.left_bound,(A.endpoint_range leftParameter).1]
  · linarith [F.right_bound,(A.endpoint_range rightParameter).2]

structure MatchedPair where
  sonic : Family
  axis : AxisShooting.Family
  parameter : Parameter
  match_eq : sonic.v parameter (9/100)=axis.u parameter (9/10)

theorem MatchedPair.regular_equation (M : MatchedPair) :
    (∀ t ∈ Icc (0:ℝ) (9/100), M.sonic.v M.parameter t ∈ Ioo (0:ℝ) (999/1000)) ∧
    ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt (M.sonic.v M.parameter)
      (-IntegerPolynomial.numer (kap M.parameter) (99/100-t) (M.sonic.v M.parameter t)/
        IntegerPolynomial.denom (sig M.parameter) (99/100-t) (M.sonic.v M.parameter t)) (Icc 0 (9/100)) t := by
  apply M.sonic.regular_unclamped
  rw [M.match_eq]
  exact M.axis.endpoint_interior M.parameter

theorem MatchedPair.euler_equation (M : MatchedPair) :
    (∀ t ∈ Icc M.sonic.e (5/6), M.sonic.u M.parameter t ∈ Ioo (0:ℝ) (1-M.sonic.e/1000)) ∧
    ∀ t ∈ Icc M.sonic.e (5/6), HasDerivWithinAt (M.sonic.u M.parameter)
      (EulerContinuation.N (kap M.parameter) t (M.sonic.u M.parameter t)/
        EulerContinuation.D (sig M.parameter) t (M.sonic.u M.parameter t)) (Icc M.sonic.e (5/6)) t := by
  apply M.sonic.euler_unclamped
  rw [← M.sonic.v_start M.parameter]
  have hh := M.regular_equation.1 0 (by norm_num)
  exact ⟨hh.1,hh.2.trans (by linarith [M.sonic.e_lt])⟩

end SepticProfile.SonicShooting

end
end

end OAI
