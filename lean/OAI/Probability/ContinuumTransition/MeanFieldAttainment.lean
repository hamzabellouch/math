import OAI.Probability.ContinuumTransition.PhysicalMeanField

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

lemma meanField_attained {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ContinuousOn Q pressureDomain) (hP : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain) {H : ℝ → ℝ}
    (hdual : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q (x.1,h)))
    {c b k : ℝ} (hc : x.1*a/2 < c)
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) :
    ∃ d, quadraticCost Q a x d = P x := by
  have hba : 0 < x.1*a := mul_pos hx ha
  have hc0 : 0 < c := lt_trans (half_pos hba) hc
  let C := x.1*a/2-(x.1*a)^2/(4*c)
  have hC : 0 < C := by
    have he : ((x.1*a)^2/(4*c))*(4*c) = (x.1*a)^2 := by field_simp
    have hp := mul_pos hba (show 0 < 2*c-x.1*a by linarith)
    dsimp [C]
    nlinarith only [he,hp,hc0]
  let A := (x.2+b)^2/(4*c)+k
  let B := |2*(x.2+b)*(x.1*a)/(4*c)|
  have hbound (d : ℝ) : quadraticCost Q a x d ≤ A+B*|d|-C*d^2 := by
    have hu := quadratic_upper_bound hc0 hdual hH (x.2+x.1*a*d)
    have hb := le_abs_self ((2*(x.2+b)*(x.1*a)/(4*c))*d)
    rw [abs_mul] at hb
    have he : (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 =
        A+(2*(x.2+b)*(x.1*a)/(4*c))*d-C*d^2 := by dsimp [A,C]; ring
    change Q (x.1,x.2+x.1*a*d)-x.1*a*d^2/2 ≤ _
    calc
      _ ≤ (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 := sub_le_sub_right hu _
      _ = _ := he
      _ ≤ _ := by dsimp [B]; linarith only [hb]
  obtain ⟨d,hd⟩ := quadratic_bound_attains (quadraticCost_continuous hQ hx) hC hbound
  refine ⟨d,le_antisymm ((hP x hx).1 (mem_range_self d)) ?_⟩
  apply (hP x hx).2
  rintro _ ⟨r,rfl⟩
  exact hd r

end ContinuumTemperature
end
end

end OAI
