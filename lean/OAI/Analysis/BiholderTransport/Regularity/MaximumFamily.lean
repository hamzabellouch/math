import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.InteriorMaximum
import OAI.Analysis.BiholderTransport.Regularity.MaximumRow

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure MaximumFamily (v : M → ℝ) (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) where
  t : ℕ → ℝ
  b : ℕ → ℝ
  z : ℕ → M
  prefixTime : ∀ k,0<t k ∧ t k<1
  parameter : ∀ k,b k∈Ioo bminus bplus
  time : Tendsto t atTop (𝓝 1)
  positive : ∀ k,0<regularizedComparison v α D bplus (t k) Bc Bo (b k,z k)
  maximum : ∀ k,∀ w:ℝ×M,w.1∈Icc bminus bplus →
    regularizedComparison v α D bplus (t k) Bc Bo w≤
      regularizedComparison v α D bplus (t k) Bc Bo (b k,z k)
  row : ∀ k,MaximumRow (n := n) v α D (b k) bplus (t k) Bc Bo (z k)

lemma WeakMTW.exists_maximum_family (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (hc : Continuous Bc) (ho : Continuous Bo) {H : ℝ}
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (hp : 0<bplus) (hm : 0≤bminus)
    (hsmall : bminus≤bplus/(64*1024^2))
    (hupper : ∀ b∈Icc bminus bplus,∀ z,modifiedExcess v α D b Bc Bo z≤b)
    (hlower : ∃ y,bplus/(8*1024^2)≤ modifiedExcess v α D (bplus/(8*1024)) Bc Bo y)
    {L : ℝ≥0} (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
    {δ : ℝ} (hδ : 0<δ)
    (hreg : ∀ b∈Icc bminus bplus,∀ τ:ℝ,0<τ → τ<δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum v α D b Bc))) :
    Nonempty (MaximumFamily (n := n) v α D bminus bplus Bc Bo) := by
  let r : ℕ → ℝ := fun k=>1/((k:ℝ)+2)
  let t : ℕ → ℝ := fun k=>1-r k
  have hr : Tendsto r atTop (𝓝 0) := by
    have Hr : Tendsto (fun k:ℕ=>(1:ℝ)/((k:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have H := Hr.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k:ℕ=>(1:ℝ)/(((k+1:ℕ):ℝ)+1)) atTop (𝓝 0) at H
    simpa only [r,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using H
  have ht : Tendsto t atTop (𝓝 1) := by simpa only [sub_zero] using tendsto_const_nhds.sub hr
  have ht01 : ∀ k,0<t k ∧ t k<1 := by
    intro k
    have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
    have hden : 0<(k:ℝ)+2 := by linarith
    have hp' : 0<r k := one_div_pos.mpr hden
    have hlt : r k<1 := (div_lt_one hden).mpr (by linarith)
    exact ⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩
  let C := (Metric.diam (univ:Set M))^2/2
  have hC : ∀ x y:M,cost x y≤C := by
    intro x y
    have Hd := Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
    have Hsq := sq_le_sq₀ dist_nonneg Metric.diam_nonneg |>.mpr Hd
    exact div_le_div_of_nonneg_right Hsq (by norm_num)
  let err : ℕ → ℝ := fun k=>C*|1/t k-1|+(L:ℝ)^2*(1-t k)/2
  have he : Tendsto err atTop (𝓝 0) := by
    have h1 : Tendsto (fun k=>(1:ℝ)/t k-1) atTop (𝓝 (1/1-1)) :=
      (tendsto_const_nhds.div ht (by norm_num : (1:ℝ)≠0)).sub tendsto_const_nhds
    have h2 : Tendsto err atTop (𝓝 (C*|1/1-1|+(L:ℝ)^2*(1-1)/2)) :=
      (tendsto_const_nhds.mul h1.abs).add
        ((tendsto_const_nhds.mul (tendsto_const_nhds.sub ht)).div_const 2)
    simpa only [one_div_one,sub_self,abs_zero,mul_zero,zero_div,add_zero] using h2
  have hε : 0<bplus/(128*1024^2) := by positivity
  have hevent : ∀ᶠ k in atTop,err k≤bplus/(128*1024^2) ∧ 1-t k<δ :=
    ((he.eventually (gt_mem_nhds hε)).mono (fun k hk=>hk.le)).and
      (((tendsto_const_nhds.sub ht : Tendsto (fun k=>1-t k) atTop (𝓝 (1-1))).eventually
        (by simpa using (gt_mem_nhds hδ : Iio δ∈𝓝 (0:ℝ)))))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have Hmax : ∀ k,∃ q:ℝ×M,q.1∈Ioo bminus bplus ∧
      0<regularizedComparison v α D bplus (t (k+N)) Bc Bo q ∧
      ∀ w:ℝ×M,w.1∈Icc bminus bplus →
        regularizedComparison v α D bplus (t (k+N)) Bc Bo w≤
          regularizedComparison v α D bplus (t (k+N)) Bc Bo q := by
    intro k
    apply regularized_interior_maximum hv hc ho (ht01 _).1 (ht01 _).2 hp hm hsmall
      (hN (k+N) (Nat.le_add_left _ _)).1 hupper hlower
    intro b hb z
    exact regularizedComparison_error hv ho (hLip b hb) hC (ht01 _).1 (ht01 _).2 z
  choose q hq hpq hmax using Hmax
  have Hrow : ∀ k,Nonempty (MaximumRow (n := n) v α D (q k).1 bplus (t (k+N)) Bc Bo (q k).2) := by
    intro k
    apply hmtw.exists_maximum_row hv hc ho hbound (ht01 _).1 (ht01 _).2
      (hm.trans (hq k).1.le) hp (hreg (q k).1 (Ioo_subset_Icc_self (hq k)) (1-t (k+N))
        (sub_pos.mpr (ht01 _).2) (hN (k+N) (Nat.le_add_left _ _)).2 (q k).2)
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (hq k).1 (hq k).2)] with w hw
    exact hmax k w (Ioo_subset_Icc_self hw)
  let R := fun k=>Classical.choice (Hrow k)
  exact ⟨⟨fun k=>t (k+N),fun k=>(q k).1,fun k=>(q k).2,fun k=>ht01 _,hq,
    ht.comp (tendsto_add_atTop_nat N),hpq,hmax,R⟩⟩
end WeakMTWTransport

end

end OAI
