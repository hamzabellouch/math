import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.BranchJets

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.branch_transverse_slack_strict (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hTs : T<s) (hs : s<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {ξ : TangentSpace 𝓘(ℝ,Model n) x} (hξ : ξ≠0)
    (hortho : ∀ i, inner ℝ ξ (p i-∑ j, w j • p j)=0) {A : ℝ}
    (hlim : Tendsto (fun t => hessianValue x (t • (∑ j, w j • p j)) ξ) (𝓝[<] T) (𝓝 A)) :
    (∑ i, w i*(hessianValue x (s • p i) ξ/s)) < A/T := by
  obtain ⟨a,hTa,has⟩ := exists_between hTs
  have hlim' := hlim.div (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hT.ne'
  have hle : (∑ i, w i*(hessianValue x (a • p i) ξ/a)) ≤ A/T := by
    apply ge_of_tendsto hlim'
    filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htT
    exact (hmtw.finite_transverse_slack_strict p w hw hsum hmin ht (htT.trans hTa)
      (has.trans hs) (hID t ⟨ht,htT⟩) hξ hortho).le
  apply lt_of_lt_of_le _ hle
  apply Finset.sum_lt_sum
  · intro i _
    exact (mul_lt_mul_of_pos_left
      (divided_hessian_strict_decrease (hmin i) (hT.trans hTa) has hs hξ) (hw i)).le
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left
      (divided_hessian_strict_decrease (hmin i) (hT.trans hTa) has hs hξ) (hw i)⟩

lemma finite_normal_branch_envelope_growth
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hs0 : 0<s) (hs : s<1)
    (g : TangentSpace 𝓘(ℝ,Model n) x → ℝ) (hg : ContDiffAt ℝ 2 g 0)
    (hgfirst : HasFDerivAt g (innerSL ℝ (-(T • (∑ j, w j • p j)))) 0)
    (hslack : ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x, ξ≠0 →
      (∀ i, inner ℝ ξ (p i-∑ j, w j • p j)=0) →
      (∑ i, w i*(hessianValue x (s • p i) ξ/s)) < fderiv ℝ (fderiv ℝ g) 0 ξ ξ/T) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤ (g h-g 0)/T-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ j, w j • p j
  have hsi : ∀ i, s • p i ∈ injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) hs0 hs
  let f := fun i (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    T⁻¹*(g h-g 0)-s⁻¹*(normalCost x (s • p i) h-normalCost x (s • p i) 0)
  have hleft : ContDiffAt ℝ 2 g 0 := hg
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (s • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hsi i)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (p i-r) := by
    intro i
    have H := ((hgfirst.sub_const (g 0)).const_smul T⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hsi i)).sub_const (normalCost x (s • p i) 0)).const_smul s⁻¹)
    have H' : HasFDerivAt (f i) (innerSL ℝ (p i-r)) 0 := by
      apply H.congr_fderiv
      ext v
      simp only [_root_.sub_apply,_root_.smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [hT.ne', hs0.ne']
      ring
    exact H'.fderiv
  have hsecond : ∀ i v, fderiv ℝ (fderiv ℝ (f i)) 0 v v=
      fderiv ℝ (fderiv ℝ g) 0 v v/T-hessianValue x (s • p i) v/s := by
    intro i v
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian (hsi i)]
    simp only [normalHessian,div_eq_mul_inv]
    ring
  have hmean : ∀ v, ∑ i, w i*fderiv ℝ (f i) 0 v=0 := by
    intro v
    simp only [hfirst,innerSL_apply_apply,inner_sub_left,mul_sub,Finset.sum_sub_distrib,
      ←Finset.sum_mul,hsum,one_mul]
    have heq : (∑ i, w i*inner ℝ (p i) v)=inner ℝ r v := by
      simp only [r,sum_inner,real_inner_smul_left]
    rw [heq,sub_self]
  have hpos : ∀ v, v≠0 → (∀ i, fderiv ℝ (f i) 0 v=0) →
      0<∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v := by
    intro v hv hl
    have hortho : ∀ i, inner ℝ v (p i-r)=0 := by
      intro i
      rw [real_inner_comm]
      simpa only [hfirst,innerSL_apply_apply] using hl i
    have H := hslack v hv hortho
    simp only [hsecond,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
    exact sub_pos.mpr H
  obtain ⟨b,hb,H⟩ := finite_smooth_transverse_growth f hf (fun i => by simp [f]) w hw hsum hmean hpos
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  refine ⟨i,?_⟩
  simpa only [f,r,div_eq_mul_inv,mul_comm] using hi

lemma WeakMTW.finite_branch_cost_growth (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hTs : T<s) (hs : s<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • (∑ i, w i • p i))))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • (∑ i, w i • p i)⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤
        (G (riemannianExp x h,riemannianExp x (T • (∑ j, w j • p j)))-
          G (x,riemannianExp x (T • (∑ j, w j • p j))))/T-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let r := ∑ j, w j • p j
  let g := fun h : TangentSpace 𝓘(ℝ,Model n) x => G (riemannianExp x h,riemannianExp x (T • r))
  have hrh : r ∈ convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  obtain ⟨hg,hgfirst,hglim⟩ := cost_branch_normal_jets hT hG hagree (fun t ht => hID t ht r hrh)
  have hg2 : ContDiffAt ℝ 2 g 0 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := finite_normal_branch_envelope_growth p w hw hsum hmin hT (hT.trans hTs) hs g hg2 hgfirst
    (fun ξ hξ ho => hmtw.branch_transverse_slack_strict p w hw hsum hmin hT hTs hs hID hξ ho (hglim ξ))
  simpa only [g,r,riemannianExp_zero] using H

end WeakMTWTransport

end

end OAI
