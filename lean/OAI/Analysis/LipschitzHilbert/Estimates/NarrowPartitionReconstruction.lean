import OAI.Analysis.LipschitzHilbert.Estimates.FiniteNarrowPartition

namespace OAI

/-! Exact Fourier reconstruction from a finite narrow-window partition. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_list_sum (l : List (SchwartzMap (ℝ×ℝ) ℂ)) (omega : ℝ×ℝ) :
    planarFourier l.sum omega=(l.map (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarFourier f omega)).sum := by
  induction l with
  | nil => simp [planarFourier]
  | cons f fs ih => simp only [List.sum_cons,planarFourier_add,List.map_cons,ih]

theorem narrowPartition_reconstruction (l : List NarrowWindow) (K : Set ℝ)
    (hpartition : ∀ x∈K, (l.map (fun q => q.2 x)).sum=1)
    (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hsupport : ∀ omega, planarFourier f omega≠0 → W*omega.2∈K) :
    (l.map (fun q => schwartzVerticalProjection q.2 W 0 f)).sum=f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [planarFourier_list_sum]
  simp only [List.map_map,Function.comp_def,schwartzVerticalProjection_fourier,sub_zero]
  by_cases hz : planarFourier f omega=0
  · simp only [hz,mul_zero,List.map_const',List.sum_replicate,nsmul_zero]
  · have h := hpartition (W*omega.2) (hsupport omega hz)
    rw [List.sum_map_mul_right,h,one_mul]

theorem narrowProjection_absorb (q : NarrowWindow)
    (habs : ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x)
    (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection narrowBandProfile (q.1*W) 0
      (schwartzVerticalProjection q.2 W 0 f)=schwartzVerticalProjection q.2 W 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,sub_zero]
  rw [mul_assoc q.1 W omega.2,←mul_assoc,habs]

end LipschitzHilbert.PacketRepresentation

end

end OAI
