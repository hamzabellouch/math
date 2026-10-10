import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.OperatorAmplification
import OAI.Analysis.Commutator.WOTFunctionals

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def AmplifiedBound (M : VonNeumannAlgebra H) (G : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (T : SumSpace (H:=H) (Fin n) →L[ℂ] SumSpace (H:=H) (Fin n)),
    (∀ i j, entry (Fin n) T i j∈M) →
      ‖diagonal (H:=H) (Fin n) G*T-T*diagonal (H:=H) (Fin n) G‖≤c*‖T‖

theorem annihilator_bound (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
    {c : ℝ} (hc : 0≤c) (hcb : AmplifiedBound M G c)
    (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ T∈M.commutant, φ (ofCLM T)=0) :
    ‖φ (ofCLM G)‖≤c*‖φ.comp ContinuousLinearMap.WOTofCLM‖ := by
  classical
  obtain ⟨n,x,y,hxy,hn⟩ := factorization φ
  let S := M.commutant.toStarSubalgebra.map (diagonal (H:=H) (Fin n))
  let K := cyclicSubspace S x
  let Q := K.starProjection
  have hzero : ∀ z∈K, inner ℂ y z=0 := by
    apply closure_minimal (s:=(orbitSubmodule S x : Set (SumSpace (H:=H) (Fin n))))
      (t:={z | inner ℂ y z=0}) ?_ ?_
    · rintro z ⟨a,⟨b,hb,rfl⟩,rfl⟩
      change inner ℂ y (diagonal (H:=H) (Fin n) b x)=0
      simpa only [PiLp.inner_apply,diagonal_apply,←hxy b] using hφ b hb
    · exact isClosed_eq (innerSL ℂ y).continuous continuous_const
  have hQx : Q x=x :=
    Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSubspace_self S x)
  have hQmem : ∀ i j, entry (Fin n) Q i j∈M := by
    intro i j
    rw [←SetLike.mem_coe,←M.centralizer_centralizer]
    intro a ha
    apply entry_commutes (Fin n) Q a
    have ha' : a∈M.commutant := by
      rwa [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
    exact cyclic_projection_mem_commutant S x (diagonal (H:=H) (Fin n) a) ⟨a,ha',rfl⟩
  have hQnorm : ‖diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G‖≤c :=
    (hcb n Q hQmem).trans (mul_le_of_le_one_right hc K.starProjection_norm_le)
  have hid : inner ℂ y ((diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G) x)=
      φ (ofCLM G) := by
    simp only [_root_.sub_apply,mul_apply_eq_comp,inner_sub_right,hQx]
    rw [hzero _ (K.starProjection_apply_mem _),sub_zero]
    simpa only [PiLp.inner_apply,diagonal_apply] using (hxy G).symm
  rw [←hid]
  calc
    _ ≤ ‖y‖*‖(diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G) x‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖y‖*(c*‖x‖) := mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hQnorm (norm_nonneg x))) (norm_nonneg y)
    _ = c*(‖x‖*‖y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hc

end Kadison.WOTDistance

end

end
end

end OAI
