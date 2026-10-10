import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix
import OAI.Analysis.Commutator.CyclicSpatialImplementation
import OAI.Analysis.Commutator.FaithfulPositive

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra Topology

open Filter

namespace Kadison.CpOperations

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cp_of_weak_limit {l : Filter I} [l.NeBot] (φ : I → A →CP (H →L[ℂ] H))
    (V : A →ₗ[ℂ] (H →L[ℂ] H))
    (hlim : ∀ a x y,Tendsto (fun i => ⟪φ i a x,y⟫_ℂ) l (𝓝 ⟪V a x,y⟫_ℂ))
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) (hX : 0≤X) : 0≤X.map V := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  let R := CyclicColumns.matrixRepresentation (ι:=Fin n) (StarAlgHom.id ℂ (H →L[ℂ] H))
  have hR : Function.Injective R := CyclicSpatial.matrixRepresentation_injective (ι:=Fin n)
    (StarAlgHom.id ℂ (H →L[ℂ] H)) Function.injective_id
  have hiff := @faithfulStar_nonneg_iff
    (CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance R hR
  apply (hiff _).mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hp (i : I) : 0≤⟪R (X.map (φ i)) x,x⟫_ℂ :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (map_nonneg R ((φ i).map_cstarMatrix_nonneg X hX))).inner_nonneg_left x
  have hl : Tendsto (fun i => ⟪R (X.map (φ i)) x,x⟫_ℂ) l (𝓝 ⟪R (X.map V) x,x⟫_ℂ) := by
    simp [R,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
      PiLp.inner_apply,sum_inner,CStarMatrix.map_apply]
    apply tendsto_finsetSum
    intro k _
    apply tendsto_finsetSum
    intro j _
    exact hlim (X k j) (x j) (x k)
  have hn : 0≤⟪R (X.map V) x,x⟫_ℂ := ge_of_tendsto hl (Eventually.of_forall hp)
  exact ⟨Complex.ext (by simp) (by simpa using hn.2),hn.1⟩

theorem exists_cp_ultralimit (ω : Ultrafilter I) (φ : I → A →CP (H →L[ℂ] H))
    (C : ℝ) (hC : 0≤C) (hφ : ∀ i a,‖φ i a‖≤C*‖a‖) :
    ∃ Ψ : A →CP (H →L[ℂ] H), (∀ a,‖Ψ a‖≤C*‖a‖) ∧
      ∀ a x y,Tendsto (fun i => ⟪φ i a x,y⟫_ℂ) (ω : Filter I) (𝓝 ⟪Ψ a x,y⟫_ℂ) := by
  choose V hV hlim using fun a => WeakOperatorLimit.exists_ultralimit ω
    (fun i => φ i a) (C*‖a‖) (mul_nonneg hC (norm_nonneg _)) (fun i => hφ i a)
  have hadd (a b : A) : V (a+b)=V a+V b := by
    ext x
    apply ext_inner_right ℂ
    intro y
    apply tendsto_nhds_unique (hlim (a+b) x y)
    simpa only [map_add,add_apply,inner_add_left] using
      (hlim a x y).add (hlim b x y)
  have hsmul (c : ℂ) (a : A) : V (c • a)=c • V a := by
    ext x
    apply ext_inner_right ℂ
    intro y
    apply tendsto_nhds_unique (hlim (c • a) x y)
    simpa only [map_smul,smul_apply,inner_smul_left] using
      tendsto_const_nhds.mul (hlim a x y)
  let Vₗ : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := V
      map_add' := hadd
      map_smul' := hsmul }
  exact ⟨{ toLinearMap := Vₗ
           map_cstarMatrix_nonneg' := cp_of_weak_limit φ Vₗ hlim },hV,hlim⟩

end Kadison.CpOperations

end

end
end

end OAI
