import OAI.Geometry.RuledCovering.SquareCover

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The flip and interchange relating the two physical maps. -/
def swapReflect : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 0) (-z 2)
  invFun z := vec3 (z 1) (z 0) (-z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3]; abel
  map_smul' c z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    change ‖vec3 (z 1) (z 0) (-z 2)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz,norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 0) (-z 2)
    nlinarith [norm_nonneg z,norm_nonneg (vec3 (z 1) (z 0) (-z 2))]

lemma physicalMaps_relation (h a : ℝ) (z : Space) :
    secondPhysicalMap h a z = vec3 0 0 (h*a) + swapReflect (firstPhysicalMap h z) := by
  ext i
  fin_cases i <;> simp [secondPhysicalMap,firstPhysicalMap,swapReflect,vec3]; ring

lemma firstPhysicalMap_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (firstPhysicalMap h) := by
  intro x y he
  have he0 := congrArg (fun z : Space => z 0) he
  have he1 := congrArg (fun z : Space => z 1) he
  have he2 := congrArg (fun z : Space => z 2) he
  ext i
  fin_cases i
  · exact he0
  · exact he1
  · exact (mul_left_cancel₀ hh he2)

lemma firstPhysicalMap_ruled (h : ℝ) (D : Set Plane) (G : Plane → Plane) :
    firstPhysicalMap h '' physicalRuled 1 D G 1 = physicalRuled h D G 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,s,hs,rfl⟩,rfl⟩
    exact ⟨p,hp,s,hs,by simp [firstPhysicalMap]⟩
  · rintro ⟨p,hp,s,hs,rfl⟩
    exact ⟨vec3 s (p 0+s*G p 0) (p 1+s*G p 1),
      ⟨p,hp,s,hs,by simp⟩,rfl⟩

/-- Nilpotent approximation, with finite oriented square tiles and both exact
Euclidean physical realizations. Smoothness is more than the C1 producer needs. -/
theorem nilpotent : NilpotentStatement := by
  intro D G hD hG hnil h eps hh heps
  obtain ⟨U,hU,hDU,hG⟩ := hG
  have hG1 : SmoothNear 1 D G := ⟨U,hU,hDU,hG.of_le (by norm_num)⟩
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh hD hG1 hnil (mul_pos hh heps)
  choose T g hT hCT using hC
  refine ⟨n,T,g,hT,?_,?_,?_⟩
  · intro z hz
    have hz' : firstPhysicalMap h z ∈ physicalRuled h D G 1 := by
      rw [← firstPhysicalMap_ruled]
      exact mem_image_of_mem _ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hz')
    rw [hCT i,projectedCylinder_carrier] at hi
    obtain ⟨x,hx,hx'⟩ := hi
    have he : x = z := firstPhysicalMap_injective hh.ne' hx'
    exact mem_iUnion.mpr ⟨i, he ▸ hx⟩
  · simp_rw [familyArea,hCT,projectedCylinder_area hh] at hcost
    have he : (∑ i, h * volume.real (T i) * physicalWeight h (g i)) =
        h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hcost
    nlinarith
  · intro a
    let C₁ : Fin n → Cylinder := fun i => projectedCylinder h (g i) (T i)
    let C₂ : Fin n → Cylinder := fun i =>
      ((C₁ i).rotate swapReflect).translate (vec3 0 0 (h*a))
    refine ⟨C₁,C₂,fun i => ?_⟩
    have hP : (C₁ i).parallelogram := projectedCylinder_parallelogram hh _ (hT i).parallelogram
    refine ⟨hP,Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hP swapReflect) _,
      projectedCylinder_carrier h _ _,?_,projectedCylinder_area hh _ _,?_⟩
    · dsimp only [C₂]
      rw [Cylinder.translate_carrier,Cylinder.rotate_carrier,projectedCylinder_carrier,
        ← image_comp,← image_comp]
      congr 1
      funext z
      exact (physicalMaps_relation h a z).symm
    · dsimp only [C₂]
      rw [Cylinder.translate_area,Cylinder.rotate_area]
      exact projectedCylinder_area hh _ _

end RuledApproximation

end

end OAI
