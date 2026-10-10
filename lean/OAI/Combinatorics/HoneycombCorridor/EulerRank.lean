import Mathlib

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem cell_euler_of_exact {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [Nonempty V]
    (A : Matrix V E ℚ) (B : (F → ℚ) →ₗ[ℚ] (E → ℚ))
    (hB : Function.Injective B) (hex : B.range = A.mulVecLin.ker)
    (hconst : A.transpose.mulVecLin.ker = Submodule.span ℚ {(1 : V → ℚ)}) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 1 := by
  have hF : Module.finrank ℚ A.mulVecLin.ker = Fintype.card F := by
    rw [← hex,LinearMap.finrank_range_of_inj hB,Module.finrank_fintype_fun_eq_card]
  have hV : Module.finrank ℚ A.transpose.mulVecLin.ker = 1 := by
    rw [hconst]
    exact finrank_span_singleton (by
      obtain ⟨v⟩ := ‹Nonempty V›
      intro h
      have := congrFun h v
      norm_num at this)
  have hrE := A.mulVecLin.finrank_range_add_finrank_ker
  have hrV := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr := A.rank_transpose
  change Module.finrank ℚ A.transpose.mulVecLin.range =
    Module.finrank ℚ A.mulVecLin.range at hr
  rw [hF,Module.finrank_fintype_fun_eq_card] at hrE
  rw [hV,Module.finrank_fintype_fun_eq_card] at hrV
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI
