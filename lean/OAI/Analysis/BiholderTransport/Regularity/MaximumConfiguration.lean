import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.Alignment
import OAI.Analysis.BiholderTransport.Regularity.ActualParameter

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.modified_maximum_configuration
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ} {z : M}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H)
    (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (hopfLax (1-t) (modifiedDatum v a D b Bc)) z)
    (hmax : ∀ᶠ q in 𝓝 (b,z),regularizedComparison v a D bplus t Bc Bo q≤
      regularizedComparison v a D bplus t Bc Bo (b,z)) :
    ∃ x y : M,∃ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x) ∧
      p∈minimizingVectors x ∧ z=riemannianExp x (t • p) ∧ y=riemannianExp x p ∧
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) z=
        cTransform (modifiedDatum v a D b Bo) x+cost x z/t ∧
      (∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
        modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y) ∧
      regularizedComparison v a D bplus t Bc Bo (b,z)=
        modifiedExcess v a D b Bc Bo y-parameterPenalty bplus b ∧
      ∀ (ι : Type) [Fintype ι] [Nonempty ι]
        (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (weights : ι → ℝ),
        (∀ i,(0:ℝ)<weights i) → (∑ i,weights i=1) → (∑ i,weights i • pj i=p) →
        (∀ i,pj i∈activeLogs (modifiedDatum v a D b Bo) x) →
        1/4096+4*b/bplus ≤ Bc ((v y-a)/D)-∑ i,weights i*Bo ((v (riemannianExp x (pj i))-a)/D) := by
  have hc' := continuous_modifiedDatum hv a D b hc
  have ho' := continuous_modifiedDatum hv a D b ho
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer (continuous_cTransform ho') t z
  obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hc' (1-t) z
  have hmaxz : ∀ᶠ w in 𝓝 z,
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) w+
        hopfLax (1-t) (modifiedDatum v a D b Bc) w≤
      hopfLax t (cTransform (modifiedDatum v a D b Bo)) z+
        hopfLax (1-t) (modifiedDatum v a D b Bc) z := by
    have hh := (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually hmax
    filter_upwards [hh] with w hw
    dsimp only [regularizedComparison,id_eq] at hw
    linarith only [hw]
  obtain ⟨p,hps,hp,hpz,hpy,hsum⟩ :=
    hmtw.hopf_maximum_aligned ho' hc' ht ht1 hx hy hdy hmaxz
  have hcenter : ∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
      modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y := by
    intro w
    constructor
    · intro hw
      exact (hopfLax_backward_minimizer hc' (sub_pos.mpr ht1) hw hdy).symm.trans
        (hopfLax_backward_minimizer hc' (sub_pos.mpr ht1) hy hdy)
    · rintro rfl
      exact hy
  have hbar : p∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x) :=
    normalSubdifferential_subset_active_hull ho' x hps
  refine ⟨x,y,p,hbar,hp,hpz,hpy,hx,hcenter,?_,?_⟩
  · dsimp only [regularizedComparison,modifiedExcess]
    rw [hsum]
  · intro ι _ _ pj m hm hm1 hmp hactive
    apply (hmtw.modified_parameter_inequality hv hc ho hbound pj m hm hm1
      (fun i=>(hactive i).1) (fun i=>(hactive i).2) ht ht1 hb hbp ?_ ?_).1
    · dsimp only
      rw [hmp,←hpz]
      exact hcenter
    · dsimp only
      rw [hmp,←hpz]
      exact (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hmax

end WeakMTWTransport

end

end OAI
