import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalTraceBounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def physicalGradientComponentCLM (D : Set (Fin 3 → ℝ)) (i : Fin 3) :
    H1 →L[ℝ] Lp ℝ 2 (volume.restrict D) :=
  ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) i.succ).compLpL 2 (volume.restrict D)).comp
    (physicalRestrictedJetCLM D)

lemma physicalGradientComponent_ae {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) (i : Fin 3) :
    physicalGradientComponentCLM D i u=ᵐ[volume.restrict D] fun y => originalPiGradient u y i := by
  have he := ballWholePiJetCLM_ae_of_ae u.val (fun y => u.val (WithLp.toLp 2 y)) (by rfl)
  filter_upwards [(PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) i.succ).coeFn_compLp
      (physicalRestrictedJetCLM D u),
    lpRestrictionCLM_ae D (ballWholePiJetCLM u.val),ae_restrict_of_ae he,ae_restrict_mem hD]
    with y hp hr he hy
  change (physicalGradientComponentCLM D i u) y=_ at hp
  rw [hp]
  change (physicalRestrictedJetCLM D u) y i.succ=_
  change (physicalRestrictedJetCLM D u) y=_ at hr
  rw [hr,he,ite_eq_left (hb y hy)]
  rfl

lemma literal_matrix_energy_continuous
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j,AEStronglyMeasurable (fun y => A y i j) volume)
    (C : ℝ) (hC : 0≤C) (hB : ∀ y i j,|A y i j|≤C)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) :
    Continuous (fun v : H1 => ∫ y in D,originalPiGradient u y ⬝ᵥ (A y*ᵥoriginalPiGradient v y)) := by
  let G := physicalGradientComponentCLM D
  let M (i j : Fin 3) := boundedMultiplier (E:=ℝ) (volume.restrict D)
    (fun y => A y i j) ((hA i j).mono_measure Measure.restrict_le_self) C hC
    (ae_of_all _ (fun y => hB y i j))
  have he (i j : Fin 3) (v : H1) :
      ((innerSL ℝ (G i u)).comp ((M i j).comp (G j))) v=
        ∫ y in D,originalPiGradient u y i*(A y i j*originalPiGradient v y j) := by
    change inner ℝ (G i u) (M i j (G j v))=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalGradientComponent_ae hD hb u i,
      physicalGradientComponent_ae hD hb v j,
      boundedMultiplier_apply_ae (E:=ℝ) (volume.restrict D) (fun y => A y i j)
        ((hA i j).mono_measure Measure.restrict_le_self) C hC (ae_of_all _ (fun y => hB y i j))
        (G j v)] with y hu hv hm
    change G i u y=_ at hu
    change G j v y=_ at hv
    change (M i j (G j v)) y=_ at hm
    rw [hm,hu,hv]
    simp [smul_eq_mul,RCLike.inner_apply,mul_comm]
  have hi (i j : Fin 3) (v : H1) :
      Integrable (fun y => originalPiGradient u y i*(A y i j*originalPiGradient v y j)) (volume.restrict D) := by
    apply Integrable.congr (L2.integrable_inner (𝕜:=ℝ) (G i u) (M i j (G j v)))
    filter_upwards [physicalGradientComponent_ae hD hb u i,
      physicalGradientComponent_ae hD hb v j,
      boundedMultiplier_apply_ae (E:=ℝ) (volume.restrict D) (fun y => A y i j)
        ((hA i j).mono_measure Measure.restrict_le_self) C hC (ae_of_all _ (fun y => hB y i j))
        (G j v)] with y hu hv hm
    change G i u y=_ at hu
    change G j v y=_ at hv
    change (M i j (G j v)) y=_ at hm
    rw [hm,hu,hv]
    simp [smul_eq_mul,RCLike.inner_apply,mul_comm]
  have hcont : Continuous (fun v : H1 => ∑ i : Fin 3,∑ j : Fin 3,
      ((innerSL ℝ (G i u)).comp ((M i j).comp (G j))) v) := by fun_prop
  convert hcont using 1
  funext v
  simp_rw [he]
  change (∫ y in D,∑ i : Fin 3,originalPiGradient u y i*∑ j : Fin 3,A y i j*originalPiGradient v y j)=_
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hi i j v)
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hi i j v)

lemma physicalBlockEnergy_continuous (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (u : H1) :
    Continuous (fun v : H1 => ∫ y in physicalBlockRegion,
      originalPiGradient u y ⬝ᵥ (physicalBlockTensor s a y*ᵥoriginalPiGradient v y)) := by
  obtain ⟨B,hB,hbound⟩ := (physicalBlockTensorList_properties s a hs ha
    (Finset.univ : Finset (Fin 3)).toList).2.2.2
  apply literal_matrix_energy_continuous (physicalBlockTensor s a)
    (fun i j => (physicalBlockTensor_entry_memLp s a hs ha i j).aestronglyMeasurable)
    B hB.le (fun y i j => ?_) physicalBlockRegion_compact.measurableSet
      (fun _ => physicalBlockRegion_subset_ball) u
  have hj := norm_le_pi_norm (physicalBlockTensor s a y i) j
  have hi := norm_le_pi_norm (physicalBlockTensor s a y) i
  rw [Real.norm_eq_abs] at hj
  exact hj.trans (hi.trans (hbound y))

end ScalarConductivity

end
end

end OAI
