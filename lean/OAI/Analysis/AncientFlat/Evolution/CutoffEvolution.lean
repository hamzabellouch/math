import OAI.Analysis.AncientFlat.Regularity.CutoffRegularity
import OAI.Analysis.AncientFlat.Regularity.HolderC0Extension
import OAI.Analysis.AncientFlat.Evolution.BCFTimeDerivative
import OAI.Analysis.AncientFlat.Regularity.FrozenLongSchauder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicSchauder ParametrixEvolution ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def cutoffResidual (c : ℝ) (u ut : ℝ → V → ℂ) (t : ℝ) (x : V) : ℂ :=
  cutoffDerivative u ut t x+c • Δ (Δ (cutoffValue u t)) x
lemma cutoffResidual_compact (c : ℝ) (u ut : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) : HasCompactSupport (cutoffResidual c u ut t) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:V) 2)
  intro x hx
  by_contra h
  have hn : 2<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using h
  have hz : cutoffResidual c u ut t x=0 := by
    rw [cutoffResidual,cutoffDerivative_zero u ut t x (by linarith)]
    have he := bilaplacian_eq_traceFour (cutoffValue u t) (cutoffValue_contDiff u t (hs t)) x
    have hj : iteratedFDeriv ℝ 4 (cutoffValue u t) x=0 := cutoff_product_jet_zero 4 t (u t) x (by linarith)
    rw [hj,map_zero] at he
    rw [he,smul_zero,add_zero]
  exact hx hz
lemma cutoffResidual_holder (c α A M : ℝ) (hα : 0≤α) (hα1 : α≤1) (hA : 0≤A) (hM : 0≤M)
    (ha : ∀ n : ℕ, n≤4 → HolderBound α univ
      (fun p : V × ℝ => iteratedFDeriv ℝ n (cutoff p.2) p.1) A)
    (hat : HolderBound α univ (fun p : V × ℝ => cutoffTime p.2 p.1) A)
    (u ut : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hj : JetBound α (cylinder 2) u ut M) :
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0} (fun p => cutoffResidual c u ut p.2 p.1)
      (160*A*M+‖(c • traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*(160*A*M)) := by
  obtain ⟨_,Ht,Hj⟩ := cutoff_regular_holder α A M hα hα1 hA hM ha hat u ut hs hj.1 hj.2
  have H := Ht.add (Hj.clm (c • traceFour))
  have he (p : V × ℝ) : cutoffResidual c u ut p.2 p.1 =
      cutoffDerivative u ut p.2 p.1+(c • traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)
        (iteratedFDeriv ℝ 4 (cutoffValue u p.2) p.1) := by
    simp only [cutoffResidual,bilaplacian_eq_traceFour _ (cutoffValue_contDiff u p.2 (hs p.2)),smul_apply]
  simpa only [he] using H

theorem cutoff_source_evolves (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (c : ℝ) (u ut : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hd : ∀ p∈cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2)
    (hj : ∃ M : ℝ, 0≤M ∧ JetBound α (cylinder 2) u ut M) :
    ∃ f : ℝ →ᵇ C₀(V,ℂ),
      (∀ t∈Icc 0 2, ∀ x, f t x=cutoffResidual c u ut (t-2) x) ∧
      SourceEvolves (coefficientLine c) 0 f 0 2 0 (fun t => cutoffC0 u hs (t-2)) := by
  obtain ⟨M,hM,hj⟩ := hj
  obtain ⟨A,hA,ha,hat⟩ := cutoff_uniform_holder (V := V) α hα hα1
  obtain ⟨H0,Ht,H4⟩ := cutoff_regular_holder α A M hα.le hα1 hA.le hM ha hat u ut hs hj.1 hj.2
  obtain ⟨w,hw,_⟩ := holder_c0_extension hα (by positivity : 0≤160*A*M) (by norm_num : (-2:ℝ)≤0)
    (fun p => cutoffValue u p.2 p.1) H0 (fun t _ => cutoff_product_compact t _)
  obtain ⟨v,hv,_⟩ := holder_c0_extension hα (by positivity : 0≤160*A*M) (by norm_num : (-2:ℝ)≤0)
    (fun p => cutoffDerivative u ut p.2 p.1) Ht (fun t _ => cutoffDerivative_compact u ut t)
  have Hr := cutoffResidual_holder c α A M hα.le hα1 hA.le hM ha hat u ut hs hj
  obtain ⟨q,hq,_⟩ := holder_c0_extension hα (by positivity) (by norm_num : (-2:ℝ)≤0)
    (fun p => cutoffResidual c u ut p.2 p.1) Hr (fun t _ => cutoffResidual_compact c u ut hs t)
  let f : ℝ →ᵇ C₀(V,ℂ) := q.compContinuous ⟨fun t => t-2,continuous_id.sub continuous_const⟩
  have hm (t : ℝ) (ht : t∈Icc 0 2) : t-2∈Icc (-2) 0 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hwe (t : ℝ) (ht : t∈Icc 0 2) : cutoffC0 u hs (t-2)=w (t-2) := by
    ext x; exact (hw (t-2) (hm t ht) x).symm
  refine ⟨f,fun t ht x => hq (t-2) (hm t ht) x,?_,?_,?_,?_,?_⟩
  · ext x
    simp only [sub_eq_add_neg,zero_add,cutoffC0_apply,ZeroAtInftyContinuousMap.zero_apply]
    change cutoff (-2) x • u (-2) x=0
    rw [cutoff_zero_time (by norm_num : (3:ℝ)/2≤|(-2:ℝ)|),zero_smul]
  · exact ((w.continuous.comp (continuous_id.sub continuous_const)).continuousOn).congr
      (fun t ht => hwe t ht)
  · intro t _; exact cutoffValue_contDiff u (t-2) (hs (t-2))
  · intro t _ n hn
    exact (cutoff_product_compact (t-2) (u (t-2))).iteratedFDeriv n |>.exists_bound_of_continuous
      ((cutoffValue_contDiff u (t-2) (hs (t-2))).continuous_iteratedFDeriv (by exact_mod_cast hn))
  · intro t ht
    let v' : ℝ → (V →ᵇ ℂ) := fun s => (v (s-2)).toBCF
    have hv' : Continuous v' := ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
      (v.continuous.comp (continuous_id.sub continuous_const))
    have hpoint (s : ℝ) (hsi : s∈Ioo 0 2) (x : V) :
        HasDerivAt (fun r => (cutoffC0 u hs (r-2)).toBCF x) (v' s x) s := by
      have hsi' : s-2∈Ioo (-2) 0 := ⟨by linarith [hsi.1],by linarith [hsi.2]⟩
      have hh := (cutoffValue_pointwise_derivative u ut hd (s-2) hsi' x).scomp s
        ((hasDerivAt_id s).sub_const 2)
      have he := hv (s-2) (hm s ⟨hsi.1.le,hsi.2.le⟩) x
      change HasDerivAt (fun r => cutoffValue u (r-2) x) (v (s-2) x) s
      rw [he]
      simpa only [Function.comp_def,id_eq,one_smul] using hh
    refine ⟨v' t,hasDerivAt_bcf_of_pointwise _ v' hv' 0 2 t ht hpoint,fun x => ?_⟩
    have hti := hm t ⟨ht.1.le,ht.2.le⟩
    change v (t-2) x=f t x-(c:ℂ)*Δ (Δ (cutoffValue u (t-2))) x-0*cutoffValue u (t-2) x
    change v (t-2) x=q (t-2) x-(c:ℂ)*Δ (Δ (cutoffValue u (t-2))) x-0*cutoffValue u (t-2) x
    rw [hv (t-2) hti x,hq (t-2) hti x]
    simp only [cutoffResidual,Complex.real_smul,zero_mul,sub_zero,add_sub_cancel_right]
end ParabolicLocalization

end

end OAI
