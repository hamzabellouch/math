import Mathlib
import OAI.Analysis.FreeWords.UnitaryFiniteSpectrum

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKSpectralSupport KKProjectionSupport

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance exponentialUnitaryApproxSourceNormedAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

local instance exponentialUnitaryApproxTargetNormedAlgebra : NormedAlgebra ℚ B :=
  NormedAlgebra.restrictScalars ℚ ℂ B

theorem map_expUnitary (φ : A →⋆ₐ[ℂ] B) (a : selfAdjoint A) :
    φ ((selfAdjoint.expUnitary a).val) = (selfAdjoint.expUnitary (⟨φ a.val,a.property.map φ⟩ : selfAdjoint B)).val := by
  simp only [selfAdjoint.expUnitary_coe]
  rw [NormedSpace.map_exp φ (map_continuous φ),map_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitary_exponential_approximation (M : VonNeumannAlgebra H)
    (u : unitary (ConcreteAlgebra M)) (ε : ℝ) (hε : 0<ε) :
    ∃ a : selfAdjoint (ConcreteAlgebra M), ‖u.val-(selfAdjoint.expUnitary a).val‖<ε := by
  classical
  let : NormedAlgebra ℚ (ConcreteAlgebra M) := NormedAlgebra.restrictScalars ℚ ℂ _
  obtain ⟨m,n,p,c,hp,ho,h1,hc,he⟩ := unitary_finite_spectrum_approximation M u ε hε
  let φ := partitionHom p hp ho h1
  let b : (Fin m × Fin n → ℂ) := fun i => ((c i).arg:ℂ)
  have hb : IsSelfAdjoint b := by
    funext i
    exact Complex.conj_ofReal _
  let a : selfAdjoint (ConcreteAlgebra M) := ⟨φ b,hb.map φ⟩
  refine ⟨a,?_⟩
  have hexp : NormedSpace.exp (Complex.I • b)=c := by
    funext i
    rw [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
    change Complex.exp (Complex.I*((c i).arg:ℂ))=c i
    have hh := Complex.norm_mul_exp_arg_mul_I (c i)
    simpa only [hc i,Complex.ofReal_one,one_mul,mul_comm,mul_one] using hh
  have heq : (selfAdjoint.expUnitary a).val=∑ i, c i•p i := by
    change NormedSpace.exp (Complex.I • φ b)=_
    rw [← map_smul,← NormedSpace.map_exp φ (map_continuous φ),hexp]
    rfl
  rwa [heq]

end

end KKVariableUltra
end

end OAI
