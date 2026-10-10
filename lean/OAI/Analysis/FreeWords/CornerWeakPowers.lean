import Mathlib
import OAI.Analysis.FreeWords.ConcreteCornerFactor
import OAI.Analysis.FreeWords.ConcreteCornerTrace
import OAI.Analysis.FreeWords.PartialUnitaryAlgebra
import OAI.Analysis.FreeWords.WeakPowers

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKFactorSupport KKProjectionSupport KKMatrixQuantization KKConcreteCorner

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : Submodule ℂ H) [CompleteSpace S]

def liftCornerUnitary (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (u : unitary (ConcreteAlgebra (cornerAlgebra S M))) : PartialUnitary (ConcreteAlgebra M) where
  power k := liftLinear S M hp ((u^k).val)
  add k l := by
    rw [zpow_add]
    exact lift_mul S M hp _ _
  power_star k := by
    rw [← lift_star,← Unitary.coe_star,Unitary.star_eq_inv,← zpow_neg]

@[simp] theorem liftCornerUnitary_support (M : VonNeumannAlgebra H) (hp)
    (u : unitary (ConcreteAlgebra (cornerAlgebra S M))) :
    (liftCornerUnitary S M hp u).support=projection S M hp := by
  change liftLinear S M hp ((u^(0:ℤ)).val)=_
  rw [zpow_zero]
  exact lift_one S M hp

theorem trace_supported_restrict (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)
    (τ : FaithfulNormalTrace M) (v : ConcreteAlgebra (cornerAlgebra S M)) (x : ConcreteAlgebra M) :
    τ.map (liftLinear S M hp v*x)=τ.map (liftLinear S M hp (v*restrict S M hp x)) := by
  rw [lift_mul,lift_restrict]
  let p := projection S M hp
  have hl : p*liftLinear S M hp v=liftLinear S M hp v := (lift_supported S M hp v).1
  have hr : liftLinear S M hp v*p=liftLinear S M hp v := (lift_supported S M hp v).2
  change τ.map (liftLinear S M hp v*x)=τ.map (liftLinear S M hp v*(p*x*p))
  calc
    _ = τ.map (p*(liftLinear S M hp v*x)) := by rw [← mul_assoc,hl]
    _ = τ.map ((liftLinear S M hp v*x)*p) := τ.tracial _ _
    _ = _ := by simp only [← mul_assoc,hr]

theorem corner_weakly_small_powers {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (p : ConcreteAlgebra M) (hp : IsStarProjection p) (hp0 : p≠0)
    (x : ι → ConcreteAlgebra M) (k : ι → ℤ) (hk : ∀ i, k i ≠ 0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ v : PartialUnitary (ConcreteAlgebra M), v.support=p ∧
      ∀ i, ‖τ.map (v.power (k i)*x i)‖<ε := by
  have hpCLM : IsStarProjection (p : H →L[ℂ] H) := hp.map M.toStarSubalgebra.subtype
  let S : Submodule ℂ H := (p.val : H →ₗ[ℂ] H).range
  let : IsClosed (S : Set H) := ContinuousLinearMap.IsIdempotentElem.isClosed_range hpCLM.isIdempotentElem
  let : CompleteSpace S := IsClosed.completeSpace_coe
  have heq : S.starProjection=p.val := by
    obtain ⟨h,heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hpCLM
    exact heq.symm
  have hmem : S.starProjection∈M := heq ▸ p.property
  have hproj : projection S M hmem=p := Subtype.ext heq
  have hproj0 : projection S M hmem≠0 := hproj ▸ hp0
  let C := cornerAlgebra S M
  let σ := cornerTrace S M hmem τ hproj0
  let y (i:ι) : ConcreteAlgebra C := restrict S M hmem (x i)
  let t : ℝ := (τ.map p).re
  have ht : 0<t := trace_projection_pos τ hp hp0
  obtain ⟨u,hu⟩ := weakly_small_powers C σ
    (cornerAlgebra_factor S M hmem τ hF hproj0) (cornerAlgebra_diffuse S M hmem hD)
    y k hk (ε/t) (div_pos hε ht)
  refine ⟨liftCornerUnitary S M hmem u,(liftCornerUnitary_support S M hmem u).trans hproj,fun i => ?_⟩
  have hi := hu i
  have he (a : ConcreteAlgebra C) : σ.map a=Complex.ofReal t⁻¹*τ.map (liftLinear S M hmem a) := by
    change (cornerTrace S M hmem τ hproj0).map a=_
    rw [cornerTrace_apply,hproj]
  rw [he,← trace_supported_restrict] at hi
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)] at hi
  change ‖τ.map (liftLinear S M hmem ((u^(k i)).val)*x i)‖<ε
  have htt := mul_lt_mul_of_pos_left hi ht
  have hc (a:ℝ) : t*(t⁻¹*a)=a := by rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  rw [hc] at htt
  have hcan : t*(ε/t)=ε := by field_simp
  rwa [hcan] at htt

end

end KKLocalPatching
end

end OAI
