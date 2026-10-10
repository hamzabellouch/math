import OAI.Analysis.AncientFlat.Profile.ScalarShrinker

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian Topology
namespace FlatRadial
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
theorem original_potential (hm : Module.finrank ℝ V=24) (G h : ℝ → ℝ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hh : ContDiffOn ℝ ∞ h (Ici 0))
    (hid : ∀ y : ℝ, 0<y → G y=1+y*h y)
    (hpos : ∀ y : ℝ, 0≤y → 0<G y)
    (hF : ∀ t : ℝ, t<0 → ∀ y : ℝ, 0<y →
      deriv (fun r => scalarF h r y) t+(1+y*scalarF h t y)^2*T (T (scalarF h t)) y=0)
    {t : ℝ} (ht : t<0) (x : V) :
    originalB G h t x=ParabolicAnnular.profilePotential G (x,t) := by
  by_cases hx : x=0
  · subst x
    simp [originalB,ParabolicAnnular.profilePotential]
  have hy : 0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hr : 0<Real.sqrt (-t) := Real.sqrt_pos.2 (neg_pos.mpr ht)
  have hn : Real.sqrt (-t)≠0 := ne_of_gt hr
  have htn : -t≠0 := ne_of_gt (neg_pos.mpr ht)
  have hsq : (Real.sqrt (-t))^2= -t := Real.sq_sqrt (neg_nonneg.mpr ht.le)
  have hgpos := hpos (‖x‖^2/Real.sqrt (-t)) (div_pos hy hr).le
  have hgn := ne_of_gt hgpos
  have hcoef : 1+‖x‖^2*scalarF h t (‖x‖^2)=G (‖x‖^2/Real.sqrt (-t)) := by
    rw [hid _ (div_pos hy hr),scalarF]
    ring
  have htime := (scalarF_time G h hG hh hid ht hy).deriv
  have he := hF t ht (‖x‖^2) hy
  rw [htime,hcoef] at he
  rw [originalB,bilaplacian_lift_24 hm _ x (scalarF_spatial h hh ht hy),ParabolicAnnular.profilePotential]
  dsimp only
  have hT : T (T (scalarF h t)) (‖x‖^2) =
      -deriv G (‖x‖^2/Real.sqrt (-t))/(2*(Real.sqrt (-t))^3*(G (‖x‖^2/Real.sqrt (-t)))^2) := by
    apply (eq_div_iff (by positivity : 2*(Real.sqrt (-t))^3*(G (‖x‖^2/Real.sqrt (-t)))^2≠0)).mpr
    field_simp at he
    linear_combination he
  rw [hT,show (-t)⁻¹=((Real.sqrt (-t))^2)⁻¹ by rw [hsq]]
  field_simp
end FlatRadial

end

end OAI
