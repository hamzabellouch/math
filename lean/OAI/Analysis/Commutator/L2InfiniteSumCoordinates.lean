import Mathlib
import OAI.Analysis.Commutator.DecomposableOperator
import OAI.Analysis.Commutator.L2InfiniteSum

namespace OAI

noncomputable section

section

noncomputable section

local instance l2InfiniteSumCoordinatesDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open MeasureTheory Filter

open scoped InnerProductSpace Topology ENNReal

namespace Kadison.Decomposable

open InfiniteAmplification

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma infiniteSumEquiv_single (i : ι) (f : Lp H 2 μ) :
    infiniteSumEquiv μ (lp.single 2 i f)=singleL μ i f := by
  classical
  exact IsHilbertSum.linearIsometryEquiv_symm_apply_single _ _

lemma evalL_infiniteSumEquiv (i : ι) (f : Space ι (Lp H 2 μ)) :
    evalL μ i (infiniteSumEquiv μ f)=f i := by
  apply ext_inner_left ℂ
  intro g
  rw [←inner_singleL,←infiniteSumEquiv_single]
  exact ((infiniteSumEquiv (H:=H) (ι:=ι) μ).inner_map_map
    (lp.single (E:=fun _ : ι => Lp H 2 μ) 2 i g) f).trans
      (lp.inner_single_left (𝕜:=ℂ) i g f)

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

def scalarVectorMultiplier (f : C(Ω,ℂ)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  operator μ (fun x => f x • (1 : H →L[ℂ] H))
    (fun z => f.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const)
    (Eventually.of_forall (fun x => by
      calc
        ‖f x • (1 : H →L[ℂ] H)‖=‖f x‖*‖(1 : H →L[ℂ] H)‖ := norm_smul _ _
        _≤‖f x‖*1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _≤‖f‖ := by simpa using f.norm_coe_le_norm x))

lemma scalarVectorMultiplier_ae (f : C(Ω,ℂ)) (v : Lp H 2 μ) :
    scalarVectorMultiplier μ f v=ᵐ[μ] fun x => f x • v x := operator_ae ..

omit [Countable ι] in
lemma evalL_scalarMultiplier (i : ι) (f : C(Ω,ℂ)) (v : Lp (Space ι H) 2 μ) :
    evalL μ i (scalarVectorMultiplier μ f v)=scalarVectorMultiplier μ f (evalL μ i v) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
    (scalarVectorMultiplier μ f v),scalarVectorMultiplier_ae μ f v,
    scalarVectorMultiplier_ae μ f (evalL μ i v),
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) v] with x h₁ h₂ h₃ h₄
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (scalarVectorMultiplier μ f v)) x=_
  rw [h₁,h₃]
  change (scalarVectorMultiplier μ f v) x i=f x • ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp v) x
  rw [h₂,h₄]
  rfl

lemma infiniteSumEquiv_scalar (f : C(Ω,ℂ)) (v : Space ι (Lp H 2 μ)) :
    infiniteSumEquiv μ (map (scalarVectorMultiplier μ f) v)=
      scalarVectorMultiplier μ f (infiniteSumEquiv μ v) := by
  apply sub_eq_zero.mp
  apply evalL_separates μ
  intro i
  rw [map_sub,evalL_infiniteSumEquiv,evalL_scalarMultiplier,evalL_infiniteSumEquiv]
  simp only [map_apply,sub_self]

end Kadison.Decomposable

end

end
end

end OAI
