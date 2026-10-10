import Mathlib
import OAI.Geometry.WeakMTW.Potentials.ReverseGeodesic
import OAI.Geometry.WeakMTW.Potentials.IntermediateCoordinates
import OAI.Geometry.WeakMTW.Potentials.DiagonalEnvelope
import OAI.Geometry.WeakMTW.Potentials.CompactFamilyControl
import OAI.Geometry.WeakMTW.Potentials.ParametricEnvelopeBounds

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
open QuadraticEnvelope RiemannianLocal

 omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem cost_family_bounds {A : Type*} [TopologicalSpace A] {e : A → M} {d : A → ℝ}
     {a : A} (he : ContinuousAt e a) (hd : ContinuousAt d a) (hd0 : d a ≠ 0)
     (z : M) (σ : ℝ)
     (hc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (z,e a)) :
     ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
       ∀ a' ∈ U, ∀ X ∈ Metric.ball (chartAt (Model n) z z) r,
         DiagonalBound (fun Y => σ*cost ((chartAt (Model n) z).symm Y) (e a')/d a') X C := by
   let c := chartAt (Model n) z
   let b := chartAt (Model n) (e a)
   let P (a' : A) := (d a', b (e a'))
   let g : Model n×(ℝ×Model n) → ℝ := fun W => σ*cost (c.symm W.1) (b.symm W.2.2)/W.2.1
   have hP : ContinuousAt P a := hd.prodMk ((b.continuousAt (mem_chart_source (Model n) (e a))).comp he)
   have hcg := cost_coords_smooth hc
   have hcs : ContDiffAt ℝ ∞ (fun W : Model n×(ℝ×Model n) => cost (c.symm W.1) (b.symm W.2.2))
       (c z,P a) := hcg.comp (c z,P a) (contDiffAt_fst.prodMk (contDiffAt_snd.snd))
   have hg : ContDiffAt ℝ ∞ g (c z,P a) :=
     (contDiffAt_const.mul hcs).div (contDiffAt_snd.fst) hd0
   apply family_local_bounds hP hg
   have hnear : ∀ᶠ a' in 𝓝 a, e a' ∈ b.source :=
     he.preimage_mem_nhds (b.open_source.mem_nhds (mem_chart_source (Model n) (e a)))
   filter_upwards [hnear] with a' ha' Y
   dsimp only [g,P]
   rw [b.left_inv ha']

 def intermediateCenter (a : ℝ×TangentBundle (model n) M) : M := exp a.2.1 (a.1•a.2.2)
 def intermediateUpperCost (z : M) (a : ℝ×TangentBundle (model n) M) (X : Model n) : ℝ :=
   cost ((chartAt (Model n) z).symm X) a.2.1/a.1
 def intermediateLowerCost (z : M) (a : ℝ×TangentBundle (model n) M) (X : Model n) : ℝ :=
   -cost ((chartAt (Model n) z).symm X) (exp a.2.1 a.2.2)/(1-a.1)

 theorem intermediateCenter_continuous : Continuous (intermediateCenter (n := n) (M := M)) := by
   have h : Continuous (fun a : ℝ×TangentBundle (model n) M => (geodesicFlow a.1 a.2).1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.comp
       geodesicFlow_smooth.continuous
   convert h using 1
   funext a
   exact exp_mul_eq_geodesic a.2 a.1

 theorem intermediate_local_support_bounds {a : ℝ×TangentBundle (model n) M}
     (ht : 0 < a.1) (ht1 : a.1 < 1) (ha : a.2 ∈ totalMinimizingSet) (z : M)
     (hz : intermediateCenter a = z) :
     ∃ U : Set (ℝ×TangentBundle (model n) M), IsOpen U ∧ a ∈ U ∧
       ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
       ∀ a' ∈ U, ∀ X ∈ Metric.ball (chartAt (Model n) z z) r,
         DiagonalBound (intermediateUpperCost z a') X C ∧
         DiagonalBound (intermediateLowerCost z a') X C := by
   have hcost := cost_smooth_shortened ha ht ht1
   change exp a.2.1 (a.1•a.2.2) = z at hz
   rw [hz] at hcost
   have hp : Continuous (fun a' : ℝ×TangentBundle (model n) M => a'.2.1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.comp continuous_snd
   have he : Continuous (fun a' : ℝ×TangentBundle (model n) M => exp a'.2.1 a'.2.2) :=
     exp_total_smooth.continuous.comp continuous_snd
   obtain ⟨U,hU,haU,r,C,hr,hC,hup⟩ := cost_family_bounds hp.continuousAt
     continuous_fst.continuousAt ht.ne' z 1 (cost_smooth_swap hcost.1)
   obtain ⟨V,hV,haV,s,D,hs,hD,hlo⟩ := cost_family_bounds he.continuousAt
     (continuous_const.sub continuous_fst).continuousAt (sub_pos.mpr ht1).ne' z (-1) hcost.2
   refine ⟨U∩V,hU.inter hV,⟨haU,haV⟩,min r s,C+D,lt_min hr hs,add_nonneg hC hD,?_⟩
   intro a' ha' X hX
   have hXr := (Metric.ball_subset_ball (min_le_left r s)) hX
   have hXs := (Metric.ball_subset_ball (min_le_right r s)) hX
   constructor
   · have hh := (hup a' ha'.1 X hXr).mono (le_add_of_nonneg_right hD)
     have heq : intermediateUpperCost z a' = (fun Y => 1*cost ((chartAt (Model n) z).symm Y) a'.2.1/a'.1) := by
       funext Y; simp only [intermediateUpperCost,one_mul]
     rw [heq]
     exact hh
   · have hh := (hlo a' ha'.2 X hXs).mono (le_add_of_nonneg_left hC)
     have heq : intermediateLowerCost z a' = (fun Y => (-1)*cost ((chartAt (Model n) z).symm Y) (exp a'.2.1 a'.2.2)/(1-a'.1)) := by
       funext Y; simp only [intermediateLowerCost,neg_one_mul]
     rw [heq]
     exact hh

 theorem intermediate_uniform_support_bounds {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hb : b < 1) (z : M) :
     ∃ V ∈ 𝓝 z, ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
       ∀ t ∈ Icc a b, ∀ q ∈ totalMinimizingSet (n := n) (M := M), intermediateCenter (t,q) ∈ V →
         ∀ X ∈ Metric.ball (chartAt (Model n) z z) r,
         DiagonalBound (intermediateUpperCost z (t,q)) X C ∧
         DiagonalBound (intermediateLowerCost z (t,q)) X C := by
   have hK : IsCompact ((Icc a b) ×ˢ totalMinimizingSet (n := n) (M := M)) :=
     isCompact_Icc.prod totalMinimizingSet_compact
   let P (α : ℝ×TangentBundle (model n) M) (X : Model n) (C : ℝ) :=
     DiagonalBound (intermediateUpperCost z α) X C ∧ DiagonalBound (intermediateLowerCost z α) X C
   obtain ⟨V,hV,r,C,hr,hC,hbound⟩ := CompactFamilyControl.uniform_near_fiber hK
     intermediateCenter_continuous z (chartAt (Model n) z z) P
     (fun α X C D hCD h => ⟨h.1.mono hCD,h.2.mono hCD⟩)
     (fun α hα hαz => intermediate_local_support_bounds (ha.trans_le hα.1.1)
       (hα.1.2.trans_lt hb) hα.2 z hαz)
   exact ⟨V,hV,r,C,hr,hC,fun t ht q hq hqV X hX => hbound (t,q) ⟨ht,hq⟩ hqV X hX⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
