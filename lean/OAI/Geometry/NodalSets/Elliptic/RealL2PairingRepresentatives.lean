import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceLimit

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_L2_inner_reps {n : ℕ} (u v : RealEuclideanL2 n)
    (a b : (Fin n → ℝ) → ℝ)
    (ha : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] a)
    (hb : (v : (Fin n → ℝ) → ℝ) =ᵐ[volume] b) :
    Integrable (fun x ↦ a x*b x) ∧ inner ℝ u v = ∫ x, a x*b x := by
  have hm : MemLp a 2 volume := (memLp_congr_ae ha).mp (Lp.memLp u)
  have hn : MemLp b 2 volume := (memLp_congr_ae hb).mp (Lp.memLp v)
  refine ⟨hm.integrable_mul hn,?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha,hb] with x h1 h2
  rw [h1,h2]
  change b x*a x=a x*b x
  ring

end
end Yau

end OAI
