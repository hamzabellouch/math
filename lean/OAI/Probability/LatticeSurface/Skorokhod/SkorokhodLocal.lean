import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodMeasure

namespace OAI

namespace ConvexSkorokhod

open Set Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem local_reflected_equation (B : Body E) (x₀ c : E) (r : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2) :
    ∃u k : ℝ → E,∃μ : VectorMeasure unitInterval E,
      ContinuousOn u (Icc 0 1) ∧ ContinuousOn k (Icc 0 1) ∧
      u 0=x₀ ∧ k 0=0 ∧
      (∀t∈Icc (0:ℝ) 1,u t∈B.carrier ∧ u t=x₀+(w t-w 0)+k t) ∧
      TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      eVariationOn k (Icc (0:ℝ) 1) ≤ ENNReal.ofReal (‖x₀-c‖^2/r) ∧
      NormalPartitionCondition B u k ∧ IsFiniteMeasure μ.variation ∧
      μ ({0}:Set unitInterval)=0 ∧
      (∀a b : unitInterval,a ≤ b → μ (Ioc a b)=k b-k a) ∧
      ∀y : unitInterval → E,Continuous y → (∀t,y t∈B.carrier) →
        μ.integral (fun t => u t-y t) (innerSL ℝ) ≤ 0 := by
  obtain ⟨u,hu,hconv,hBu,hBV,hn⟩ := projection_mesh_normal_limit B x₀ c r hx₀ hr hball w hw hosc
  let k : ℝ → E := fun t => u t-x₀-(w t-w 0)
  have hk : ContinuousOn k (Icc 0 1) := (hu.sub continuousOn_const).sub (hw.sub continuousOn_const)
  have hkBV : BoundedVariationOn k (Icc (0:ℝ) 1) := by
    exact (hBV.trans_lt ENNReal.ofReal_lt_top).ne
  have hu₀ : u 0=x₀ := by
    have h₀ := hconv.tendsto_at (show (0:ℝ)∈Icc 0 1 from ⟨le_rfl,zero_le_one⟩)
    have he : (fun n : ℕ => mesh B x₀ w (n+1) 0)=fun _ => x₀ := by
      ext n
      simp [mesh,walk]
    rw [he] at h₀
    exact tendsto_nhds_unique h₀ tendsto_const_nhds
  have hk₀ : k 0=0 := by simp [k,hu₀]
  obtain ⟨μ,hμfin,hμ₀,hμinc,hμnormal⟩ := normal_partition_measure B u k hu hk hBu hkBV hn
  refine ⟨u,k,μ,hu,hk,hu₀,hk₀,?_,hconv,hBV,hn,hμfin,hμ₀,hμinc,hμnormal⟩
  intro t ht
  exact ⟨hBu t ht,by dsimp [k];abel⟩

end ConvexSkorokhod

end OAI
