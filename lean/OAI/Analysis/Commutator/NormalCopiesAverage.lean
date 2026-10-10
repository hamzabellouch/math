import Mathlib
import OAI.Analysis.Commutator.MainCommutantDistance
import OAI.Analysis.Commutator.NormalOriginalTower
import OAI.Analysis.Commutator.RepresentedTowerAverage

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

namespace RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma perturbation_bound (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Y Z : K →L[ℂ] K)
    {δ : ℝ} (hδ : 0≤δ) (hd : ‖Z-Y‖≤δ)
    (hY : ∀ a : A,‖Y*ρ a-ρ a*Y‖≤δ*‖a‖) (a : A) :
    ‖Z*ρ a-ρ a*Z‖≤(3*δ)*‖a‖ := by
  have he : Z*ρ a-ρ a*Z=(Z-Y)*ρ a-ρ a*(Z-Y)+(Y*ρ a-ρ a*Y) := by
    simp only [sub_mul,mul_sub]; abel
  calc
    _ ≤ ‖(Z-Y)*ρ a-ρ a*(Z-Y)‖+‖Y*ρ a-ρ a*Y‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ 2*‖Z-Y‖*‖ρ a‖+δ*‖a‖ := add_le_add (operator_commutator_norm_le _ _) (hY a)
    _ ≤ 2*δ*‖a‖+δ*‖a‖ := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le ρ a
    _ = _ := by ring

end RepresentedTower

namespace MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (F : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

include hnormal in
theorem original_copies_average (hF : Monotone (fun n => (F n).hom.range))
    (Y : OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
      OperatorAmplification.SumSpace (H:=τ.GNS) ι) {δ : ℝ} (hδ : 0≤δ)
    (hY : ∀ a : M,‖Y*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖≤δ*‖a‖) :
    ∃ Z : OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
      OperatorAmplification.SumSpace (H:=τ.GNS) ι,
      ‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      (∀ a : M,(a:H →L[ℂ] H)∈generated M F →
        Z*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)=
          OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z) ∧
      (∀ a : M,‖Z*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
        OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z‖≤(3*δ)*‖a‖) := by
  let ρ := (OperatorAmplification.diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom
  have hb (u : unitary M) : ‖Y*ρ (u:M)-ρ (u:M)*Y‖≤δ := by
    simpa only [ρ,StarAlgHom.comp_apply,CStarRing.norm_of_mem_unitary u.property,mul_one] using hY (u:M)
  have havg := RepresentedTower.exists_tower_average ρ (fun n => (F n).I)
    (fun n => (F n).hom) hF Y hδ hb
  obtain ⟨Z,hZ,hd,hc⟩ := havg
  refine ⟨Z,hZ,hd,?_,?_⟩
  · intro a ha
    exact hc _ (original_copies_generated M F τ hnormal ι a ha)
  · exact RepresentedTower.perturbation_bound ρ Y Z hδ hd hY

end MatrixTower

end Kadison

end

end
end

end OAI
