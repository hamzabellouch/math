import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothHomLieDifferential
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # Tangent projections of a product Lie group

The jointly injective projections detect nilpotence and transport a single
finite BCH identity to both factors.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

@[instance_reducible] def productSelfChartedSpace : ChartedSpace (E × F) (G × H) :=
  prodChartedSpace E G F H

attribute [local instance] productSelfChartedSpace

instance productSelfLieGroup : LieGroup (𝓘(ℝ, E × F)) ⊤ (G × H) := by
  rw [modelWithCornersSelf_prod]
  exact Prod.instLieGroup (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))

omit [CompleteSpace E] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [CompleteSpace F] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem contMDiff_product_fst :
    ContMDiff (𝓘(ℝ, E × F)) (𝓘(ℝ, E)) ∞ (Prod.fst : G × H → G) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [CompleteSpace E] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [CompleteSpace F] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem contMDiff_product_snd :
    ContMDiff (𝓘(ℝ, E × F)) (𝓘(ℝ, F)) ∞ (Prod.snd : G × H → H) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

def productFstLieHom : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) →ₗ⁅ℝ⁆
    GroupLieAlgebra (𝓘(ℝ, E)) G :=
  homLieDifferential (MonoidHom.fst G H) contMDiff_product_fst

def productSndLieHom : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) →ₗ⁅ℝ⁆
    GroupLieAlgebra (𝓘(ℝ, F)) H :=
  homLieDifferential (MonoidHom.snd G H) contMDiff_product_snd

@[simp] theorem productFstLieHom_apply (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
    productFstLieHom (E := E) (F := F) (G := G) (H := H) v = v.1 := by
  have hd : (mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (𝓘(ℝ, E))
      (Prod.fst : G × H → G) 1 : (E × F) →L[ℝ] E) = ContinuousLinearMap.fst ℝ E F :=
    mfderiv_fst
  rw [← modelWithCornersSelf_prod] at hd
  exact congrArg (fun D : (E × F) →L[ℝ] E => D v) hd

@[simp] theorem productSndLieHom_apply (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
    productSndLieHom (E := E) (F := F) (G := G) (H := H) v = v.2 := by
  have hd : (mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (𝓘(ℝ, F))
      (Prod.snd : G × H → H) 1 : (E × F) →L[ℝ] F) = ContinuousLinearMap.snd ℝ E F :=
    mfderiv_snd
  rw [← modelWithCornersSelf_prod] at hd
  exact congrArg (fun D : (E × F) →L[ℝ] F => D v) hd

theorem product_tangent_nilpotent
    (hG : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (hH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H)) :
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) := by
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hG
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hH
  apply (isNilpotent_iff ℝ _ _).mpr
  refine ⟨max c d, le_antisymm ?_ bot_le⟩
  intro x hx
  have hfst : productFstLieHom (E := E) (F := F) (G := G) (H := H) x = 0 := by
    have hm := LieIdeal.map_lowerCentralSeries_le (R := ℝ)
      (f := productFstLieHom (E := E) (F := F) (G := G) (H := H)) (max c d)
    have hle := (antitone_lowerCentralSeries ℝ
      (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G)) (Nat.le_max_left c d)
    rw [hc] at hle
    exact (hm.trans hle) (LieIdeal.mem_map hx)
  have hsnd : productSndLieHom (E := E) (F := F) (G := G) (H := H) x = 0 := by
    have hm := LieIdeal.map_lowerCentralSeries_le (R := ℝ)
      (f := productSndLieHom (E := E) (F := F) (G := G) (H := H)) (max c d)
    have hle := (antitone_lowerCentralSeries ℝ
      (GroupLieAlgebra (𝓘(ℝ, F)) H) (GroupLieAlgebra (𝓘(ℝ, F)) H)) (Nat.le_max_right c d)
    rw [hd] at hle
    exact (hm.trans hle) (LieIdeal.mem_map hx)
  change x = 0
  rw [productFstLieHom_apply] at hfst
  rw [productSndLieHom_apply] at hsnd
  exact Prod.ext hfst hsnd

end PolycyclicRecognition

end

end OAI
