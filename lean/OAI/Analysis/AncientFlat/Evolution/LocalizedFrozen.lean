import OAI.Analysis.AncientFlat.Evolution.CutoffEvolution

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicSchauder ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma cutoff_jet_eq (n : ℕ) (u : ℝ → V → ℂ) (p : V × ℝ) (hp : p∈cylinder 1) :
    iteratedFDeriv ℝ n (cutoffValue u p.2) p.1=iteratedFDeriv ℝ n (u p.2) p.1 := by
  have ht : |p.2|≤1 := by
    have ht := hp.2; norm_num at ht
    rw [abs_of_nonpos ht.2]; linarith [ht.1]
  have he : cutoffValue u p.2 =ᶠ[𝓝 p.1] u p.2 := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hp.1] with x hx
    change cutoff p.2 x • u p.2 x=u p.2 x
    rw [cutoff_eq_one ht hx.le,one_smul]
  exact (he.iteratedFDeriv ℝ n).eq_of_nhds
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma pdist_time_translate (a : ℝ) (p q : V × ℝ) :
    pdist (p.1,p.2+a) (q.1,q.2+a)=pdist p q := by
  simp only [pdist,add_sub_add_right_eq_sub]

theorem localized_fourth_estimate (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, κ≤c → c≤K → ∀ (u ut : ℝ → V → ℂ),
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M : ℝ, 0≤M ∧ JetBound α (cylinder 2) u ut M) →
      ∀ F : ℝ, 0≤F → HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0}
        (fun p => cutoffResidual c u ut p.2 p.1) F →
      HolderBound α (cylinder 1) (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) (C*F) := by
  obtain ⟨C,hC,hest⟩ := frozen_fourth_estimate_two (V := V) α κ K hα hα1 hκ hK
  refine ⟨C,hC,?_⟩
  intro c hκc hcK u ut hs hd hj F hF hres
  obtain ⟨f,hf,he⟩ := cutoff_source_evolves α hα hα1.le c u ut hs hd hj
  have hh : ∀ t∈Icc 0 2, ∀ x y, ‖f t x-f t y‖≤F*‖x-y‖^α := by
    intro t ht x y
    have hti : t-2∈Icc (-2) 0 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [hf t ht x,hf t ht y]
    simpa only [pdist,Prod.fst,Prod.snd,sub_self,abs_zero,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero] using
      hres.2 (x,t-2) hti (y,t-2) hti
  have H := hest c 2 hκc hcK (by norm_num) le_rfl f F hF hh
    (fun t => cutoffC0 u hs (t-2)) (fun t _ => cutoffValue_contDiff u (t-2) (hs (t-2))) he
  have hm (p : V × ℝ) (hp : p∈cylinder 1) : p.2+2∈Icc 0 2 := by
    have ht := hp.2; norm_num at ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hj' (p : V × ℝ) (hp : p∈cylinder 1) :
      iteratedFDeriv ℝ 4 (fun x => cutoffC0 u hs ((p.2+2)-2) x) p.1=
      iteratedFDeriv ℝ 4 (u p.2) p.1 := by
    simp only [add_sub_cancel_right,cutoffC0_apply]
    exact cutoff_jet_eq 4 u p hp
  refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
  · simpa only [Prod.fst,Prod.snd,hj' p hp] using H.1 (p.1,p.2+2) (hm p hp)
  · have hh := H.2 (p.1,p.2+2) (hm p hp) (q.1,q.2+2) (hm q hq)
    simpa only [Prod.fst,Prod.snd,hj' p hp,hj' q hq,pdist_time_translate] using hh
end ParabolicLocalization

end

end OAI
