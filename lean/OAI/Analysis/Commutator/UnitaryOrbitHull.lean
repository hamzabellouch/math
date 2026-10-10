import Mathlib
import OAI.Analysis.Commutator.FiniteDimensionalAverage

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def conjugate (v : unitary M) (Y : H →L[ℂ] H) : H →L[ℂ] H :=
  ((v:M):H →L[ℂ] H)*Y*star ((v:M):H →L[ℂ] H)

def conjugateLinear (v : unitary M) : (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) where
  toFun := conjugate M v
  map_add' _ _ := by simp [conjugate,mul_add,add_mul]
  map_smul' _ _ := by simp [conjugate]

def hull (Y : H →L[ℂ] H) : Set (H →L[ℂ] H) :=
  convexHull ℝ (Set.range (fun v : unitary M => conjugate M v Y))

lemma hull_self (Y : H →L[ℂ] H) : Y∈hull M Y := by
  apply subset_convexHull
  exact ⟨1,by simp [conjugate]⟩

lemma conjugate_mul (v w : unitary M) (Y : H →L[ℂ] H) :
    conjugate M v (conjugate M w Y)=conjugate M (v*w) Y := by
  change ((v:M):H →L[ℂ] H)*(((w:M):H →L[ℂ] H)*Y*star ((w:M):H →L[ℂ] H))*
    star ((v:M):H →L[ℂ] H)=
    (((v:M):H →L[ℂ] H)*((w:M):H →L[ℂ] H))*Y*
      star (((v:M):H →L[ℂ] H)*((w:M):H →L[ℂ] H))
  simp only [star_mul,mul_assoc]

lemma conjugate_mem_hull (v : unitary M) {T Y : H →L[ℂ] H} (hT : T∈hull M Y) :
    conjugate M v T∈hull M Y := by
  have him : conjugateLinear M v '' (Set.range (fun w : unitary M => conjugate M w Y)) ⊆
      Set.range (fun w : unitary M => conjugate M w Y) := by
    rintro _ ⟨_,⟨w,rfl⟩,rfl⟩
    exact ⟨v*w,(conjugate_mul M v w Y).symm⟩
  have hc := convexHull_mono (𝕜 := ℝ) him
  rw [← LinearMap.image_convexHull] at hc
  exact hc ⟨T,hT,rfl⟩

lemma hull_distance {Y T : H →L[ℂ] H} (hT : T∈hull M Y) :
    ‖T-Y‖≤commutatorSeminorm M Y := by
  have hs : Set.range (fun v : unitary M => conjugate M v Y) ⊆
      Metric.closedBall Y (commutatorSeminorm M Y) := by
    rintro _ ⟨v,rfl⟩
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact unitary_conjugate_distance M Y v
  simpa only [Metric.mem_closedBall,dist_eq_norm] using
    (convexHull_min hs (convex_closedBall Y _) hT)

lemma hull_norm {Y T : H →L[ℂ] H} (hT : T∈hull M Y) :
    ‖T‖≤commutatorSeminorm M Y+‖Y‖ := by
  calc
    ‖T‖=‖T-Y+Y‖ := by rw [sub_add_cancel]
    _≤‖T-Y‖+‖Y‖ := norm_add_le _ _
    _≤commutatorSeminorm M Y+‖Y‖ := by linarith [hull_distance M hT]

lemma midpoint_mem {Y T V : H →L[ℂ] H} (hT : T∈hull M Y) (hV : V∈hull M Y) :
    (1/2:ℝ) • T+(1/2:ℝ) • V∈hull M Y :=
  convex_convexHull ℝ _ hT hV (by norm_num) (by norm_num) (by norm_num)

end Kadison.UnitaryOrbit

end

end
end

end OAI
