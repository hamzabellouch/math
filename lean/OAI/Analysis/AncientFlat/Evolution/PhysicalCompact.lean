import OAI.Analysis.AncientFlat.Evolution.PhysicalFourthLocal

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
def slab (R l b : ℝ) : Set (V × ℝ) := Metric.closedBall 0 R ×ˢ Icc l b
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma slab_mem (R l b : ℝ) (p : V × ℝ) : p∈slab R l b ↔ ‖p.1‖≤R ∧ l≤p.2 ∧ p.2≤b := by
  simp only [slab,mem_prod,Metric.mem_closedBall,dist_zero_right,mem_Icc]
lemma slab_compact (R l b : ℝ) : IsCompact (slab (V := V) R l b) :=
  (isCompact_closedBall (0:V) R).prod isCompact_Icc
lemma physical_coeff_holder (α R l b : ℝ) (hα : 0<α) (hα1 : α≤1) (hb : b<0)
    (Af Bf : V → ℝ) (hA : ContDiff ℝ 1 Af) (hB : ContDiff ℝ 1 Bf) :
    ∃ K : ℝ, 0<K ∧
      HolderBound α (slab R l b) (fun p => physicalPrincipal Af p.2 p.1) K ∧
      HolderBound α (slab R l b) (fun p => (physicalPotential Bf p.2 p.1 : ℂ)) K := by
  have ht : ContDiffOn ℝ 1 (fun p : V × ℝ => similarityTime p.2) (slab R l b) := by
    exact (contDiff_snd.contDiffOn.neg.log (fun p hp =>
      (neg_pos.mpr (((slab_mem R l b p).mp hp).2.2.trans_lt hb)).ne')).neg
  have hm : ContDiffOn ℝ 1 (fun p : V × ℝ => Real.exp (similarityTime p.2/4) • p.1) (slab R l b) :=
    (ht.div_const 4).exp.smul contDiff_fst.contDiffOn
  have ha : ContDiffOn ℝ 1 (fun p : V × ℝ => physicalPrincipal Af p.2 p.1) (slab R l b) :=
    (hA.comp_contDiffOn hm).div_const 16
  have hbb : ContDiffOn ℝ 1 (fun p : V × ℝ => physicalPotential Bf p.2 p.1) (slab R l b) :=
    ht.exp.mul (hB.comp_contDiffOn hm)
  have hc : Convex ℝ (slab (V := V) R l b) := (convex_closedBall 0 R).prod (convex_Icc l b)
  obtain ⟨A,hA',ha'⟩ := compact_smooth_holder α hα hα1 _ (slab_compact R l b) hc _ ha
  obtain ⟨B,hB',hb'⟩ := compact_smooth_holder α hα hα1 _ (slab_compact R l b) hc _ hbb
  refine ⟨A+B,by positivity,ha'.mono (by linarith),?_⟩
  have hh : HolderBound α (slab R l b) (fun p : V × ℝ => (physicalPotential Bf p.2 p.1 : ℂ)) B := by
    refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
    · simpa only [Complex.norm_real] using hb'.1 p hp
    · simpa only [←Complex.ofReal_sub,Complex.norm_real] using hb'.2 p hp q hq
  exact hh.mono (by linarith)
omit [FiniteDimensional ℝ V] in
lemma physical_slab_bound (γ l b : ℝ) (hb : b<0) (v : ℝ →ᵇ C₀(V,ℂ)) :
    ∃ U : ℝ, 0≤U ∧ ∀ t∈Icc l b, ∀ x : V, ‖physical γ v t x‖≤U := by
  have ht : ContinuousOn (fun t => Real.exp ((1/2-γ)*similarityTime t)) (Icc l b) := by
    have hh : ContDiffOn ℝ 1 similarityTime (Icc l b) := by
      exact (contDiffOn_id.neg.log (fun t ht => (neg_pos.mpr (ht.2.trans_lt hb)).ne')).neg
    exact (contDiffOn_const.mul hh).exp.continuousOn
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ht
  refine ⟨max B 0*‖v‖,by positivity,fun t ht x => ?_⟩
  rw [physical_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp ((1/2-γ)*similarityTime t)≤ max B 0 := by
    have hh := hB t ht
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hh
    exact hh.trans (le_max_left _ _)
  have hv : ‖v (similarityTime t) (Real.exp (similarityTime t/4) • x)‖≤‖v‖ :=
    ((v (similarityTime t)).toBCF.norm_coe_le_norm _).trans (v.norm_coe_le_norm _)
  exact mul_le_mul he hv (norm_nonneg _) (le_max_right _ _)
end FlatSimilarity

end

end OAI
