import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates3
import OAI.Analysis.BiholderTransport.Coordinates.LocalMetricCharts

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [MetricSpace M] [ChartedSpace F M]
  [IsManifold 𝓘(ℝ,F) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsContinuousRiemannianBundle F (fun x : M => TangentSpace 𝓘(ℝ,F) x)]
  [IsRiemannianManifold 𝓘(ℝ,F) M]

lemma contMDiffAt_exists_lipschitzOn {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith C f U := by
  let χ := extChartAt 𝓘(ℝ,F) (f x)
  have hχ : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) 1 χ (f x) :=
    contMDiffAt_extChartAt
  obtain ⟨D,V,hV,hD⟩ := (((hχ.comp x hf).contDiffAt)).exists_lipschitzOnWith
  obtain ⟨C,r,hr,hsub,hC⟩ := exists_lipschitzOn_inverse_chart (E := F) (f x)
  let U := V ∩ f ⁻¹' (χ.source ∩ χ ⁻¹' ball (χ (f x)) r)
  have hU : U ∈ 𝓝 x := by
    apply inter_mem hV
    apply hf.continuousAt.preimage_mem_nhds
    exact inter_mem (extChartAt_source_mem_nhds (f x))
      (hχ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr))
  refine ⟨C*D,U,hU,?_⟩
  have hmaps : MapsTo (χ ∘ f) U (ball (χ (f x)) r) := fun _ hy => hy.2.2
  have hcomp := hC.comp (hD.mono inter_subset_left) hmaps
  intro y hy z hz
  have hh := hcomp hy hz
  change edist (χ.symm (χ (f y))) (χ.symm (χ (f z))) ≤ _ at hh
  rwa [χ.left_inv hy.2.1,χ.left_inv hz.2.1] at hh

lemma contMDiffOn_exists_lipschitzOn_compact {f : E → M} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x∈K, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ∃ C : ℝ≥0, LipschitzOnWith C f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨C,U,hU,hC⟩ := contMDiffAt_exists_lipschitzOn (hf x hx)
  exact ⟨C,U,mem_nhdsWithin_of_mem_nhds hU,hC⟩

end

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma movingNormal_trivialization_exp {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)
      = riemannianExp x p := by
  rw [movingNormal_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hx),
    (extChartAt 𝓘(ℝ,Model n) a).left_inv hx,
    Trivialization.symmL_continuousLinearMapAt]
  change x∈(chartAt (Model n) a).source
  simpa only [extChartAt_source] using hx

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_lipschitz_near_base (R : ℝ) (a : M) :
    ∃ L : ℝ≥0, ∃ K ∈ 𝓝 a, ∀ x∈K, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤R → ‖q‖≤R → dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖ := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  let Bnn : ℝ≥0 := ⟨B,hBpos.le⟩
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let P := (χ '' K) ×ˢ closedBall (0 : Model n) (B*R)
  have hPc : IsCompact P :=
    (hKc.image_of_continuousOn ((continuousOn_extChartAt a).mono (fun x hx => (hKs hx).1))).prod
      (isCompact_closedBall _ _)
  obtain ⟨C,hC⟩ := contMDiffOn_exists_lipschitzOn_compact hPc
    (f := movingNormal a) (fun z hz => (movingNormal_contMDiffAt (by
      obtain ⟨x,hx,hxz⟩ := hz.1
      rw [←hxz]
      exact χ.map_source (hKs hx).1)).of_le (by simp))
  refine ⟨C*Bnn,K,hKn,?_⟩
  intro x hx p q hp hq
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm p).trans (mul_le_mul (hKs hx).2.le hp (norm_nonneg _) hBpos.le)
  have hqP : (χ x,A q)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm q).trans (mul_le_mul (hKs hx).2.le hq (norm_nonneg _) hBpos.le)
  have hd := hC.dist_le_mul _ hpP _ hqP
  rw [movingNormal_trivialization_exp (hKs hx).1,movingNormal_trivialization_exp (hKs hx).1] at hd
  have hdist : dist (χ x,A p) (χ x,A q)≤B*‖p-q‖ := by
    rw [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,dist_eq_norm,←map_sub]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  calc
    _≤(C:ℝ)*dist (χ x,A p) (χ x,A q) := hd
    _≤(C:ℝ)*(B*‖p-q‖) := mul_le_mul_of_nonneg_left hdist C.coe_nonneg
    _=↑(C*Bnn : ℝ≥0)*‖p-q‖ := by change (C:ℝ)*(B*‖p-q‖)=(C:ℝ)*B*‖p-q‖; ring

lemma exists_uniform_exp_lipschitz (R : ℝ) :
    ∃ L : ℝ≥0, ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤R → ‖q‖≤R → dist (riemannianExp x p) (riemannianExp x q)≤L*‖p-q‖ := by
  classical
  choose L K hKn hK using exp_lipschitz_near_base (n := n) (M := M) R
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  let C : ℝ≥0 := s.sup L
  refine ⟨C,?_⟩
  intro x p q hp hq
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  apply (hK a x hxa p q hp hq).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast (Finset.le_sup (f := L) ha)

end WeakMTWTransport

end

end OAI
