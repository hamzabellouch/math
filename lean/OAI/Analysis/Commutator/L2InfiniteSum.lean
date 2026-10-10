import Mathlib
import OAI.Analysis.Commutator.InfiniteAmplification

namespace OAI

noncomputable section

section

noncomputable section

local instance l2InfiniteSumDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open MeasureTheory Filter

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.Decomposable

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open InfiniteAmplification

def singleL (i : ι) : Lp H 2 μ →L[ℂ] Lp (Space ι H) 2 μ :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).compLpL 2 μ

def evalL (i : ι) : Lp (Space ι H) 2 μ →L[ℂ] Lp H 2 μ :=
  (lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLpL 2 μ

omit [Countable ι] [CompleteSpace H] in
lemma inner_singleL (i : ι) (f : Lp H 2 μ) (g : Lp (Space ι H) 2 μ) :
    inner ℂ (singleL μ i f) g=inner ℂ f (evalL μ i g) := by
  classical
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i) f,
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) g] with a ha hb
  change inner ℂ ((lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).compLp f a) (g a)=
    inner ℂ (f a) ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp g a)
  rw [ha,hb]
  exact lp.inner_single_left (𝕜:=ℂ) i (f a) (g a)

omit [Countable ι] [CompleteSpace H] in
lemma evalL_singleL (i j : ι) (f : Lp H 2 μ) :
    evalL μ i (singleL μ j f)=if i=j then f else 0 := by
  classical
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    (lp.evalCLM ℂ (fun _ : ι => H) 2 i) (singleL μ j f),
    ContinuousLinearMap.coeFn_compLp (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j) f,
    Lp.coeFn_zero H 2 μ] with a ha hb hz
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (singleL μ j f)) a=_
  rw [ha]
  change singleL μ j f a i=_
  change ((lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j).compLp f) a i=_
  rw [hb]
  change lp.single (E:=fun _ : ι => H) 2 j (f a) i=_
  by_cases hij : i=j
  · subst j
    simp [lp.single_apply]
  · rw [ite_eq_right hij,hz]
    simp [lp.single_apply,hij]

def singleLI (i : ι) : Lp H 2 μ →ₗᵢ[ℂ] Lp (Space ι H) 2 μ :=
  (singleL μ i).toLinearMap.isometryOfInner (fun f g => by
    change inner ℂ (singleL μ i f) (singleL μ i g)=inner ℂ f g
    rw [inner_singleL,evalL_singleL,ite_eq_left rfl])

omit [Countable ι] [CompleteSpace H] in
lemma singleLI_orthogonal : OrthogonalFamily ℂ (fun _ : ι => Lp H 2 μ) (singleLI μ) := by
  intro i j hij f g
  change inner ℂ (singleL μ i f) (singleL μ j g)=0
  rw [inner_singleL,evalL_singleL,ite_eq_right hij,inner_zero_right]

omit [CompleteSpace H] in
lemma evalL_separates (f : Lp (Space ι H) 2 μ) (hf : ∀ i,evalL μ i f=0) : f=0 := by
  classical
  apply Lp.ext
  have hcoord : ∀ᵐ a ∂μ,∀ i : ι,f a i=0 := ae_all_iff.mpr (fun i => by
    filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) f,
      Lp.coeFn_zero H 2 μ] with a ha hz
    have he : (evalL μ i f) a=0 := by rw [hf]; exact hz
    change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp f) a=0 at he
    rw [ha] at he
    exact he)
  filter_upwards [hcoord,Lp.coeFn_zero (Space ι H) 2 μ] with a ha hz
  rw [hz]
  ext i
  exact ha i

lemma singleLI_total :
    ⊤≤(⨆ i,LinearMap.range (singleLI (H:=H) (ι:=ι) μ i).toLinearMap).topologicalClosure := by
  let K : Submodule ℂ (Lp (Space ι H) 2 μ) :=
    (⨆ i,LinearMap.range (singleLI μ i).toLinearMap).topologicalClosure
  have hclosed : IsClosed (K : Set (Lp (Space ι H) 2 μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hclosed.completeSpace_coe
  have hbot : Kᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro f hf
    rw [Submodule.mem_bot]
    apply evalL_separates μ f
    intro i
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    rw [←inner_singleL]
    exact Submodule.inner_right_of_mem_orthogonal
      ((Submodule.le_topologicalClosure _)
        ((le_iSup (fun i => LinearMap.range (singleLI μ i).toLinearMap) i)
          ⟨evalL μ i f,rfl⟩)) hf
  exact le_of_eq ((Submodule.orthogonal_eq_bot_iff).mp hbot).symm

def infiniteSumEquiv : Space ι (Lp H 2 μ) ≃ₗᵢ[ℂ] Lp (Space ι H) 2 μ :=
  (IsHilbertSum.mk (singleLI_orthogonal (ι:=ι) μ) (singleLI_total μ)).linearIsometryEquiv.symm

end Kadison.Decomposable

end

end
end

end OAI
