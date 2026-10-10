import OAI.Analysis.AncientFlat.Evolution.PhysicalCompact
import OAI.Analysis.AncientFlat.Weighted.WeightedSourceHolder
import OAI.Analysis.AncientFlat.Regularity.FiniteLocalJets

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatWeighted
open ParabolicInterior FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma YBound.slab_holder {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (hα : 0≤α) (hw : w≤4) (ha : 0<a) (hM : 0≤M)
    (R l b : ℝ) (hb : b<0) :
    ∃ K : ℝ, 0≤K ∧ HolderBound α (slab R l b) f K := by
  let d := Real.sqrt (Real.sqrt (-b))
  have hd : 0<d := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hb))
  refine ⟨(d^(w-4)+d^(w-4)*d^(-α)+2*d^(w-4)/(a*d)^α)*M,by positivity,?_⟩
  apply h.holder_on hα hw ha hM hd
  · intro p hp
    exact ((slab_mem R l b p).mp hp).2.2.trans_lt hb
  · intro p hp
    unfold sigma d
    apply Real.sqrt_le_sqrt
    exact (Real.sqrt_le_sqrt (neg_le_neg ((slab_mem R l b p).mp hp).2.2)).trans
      (le_add_of_nonneg_left (sq_nonneg _))
end FlatWeighted
namespace FlatSimilarity
open ParabolicInterior FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma physical_locally_finite (α γ w a M : ℝ)
    (hα : 0<α) (hα1 : α<1) (hw : w≤4) (ha : 0<a) (hM : 0≤M)
    (Af Bf : V → ℝ) (hA : ContDiff ℝ 1 Af) (hB : ContDiff ℝ 1 Bf)
    (v : ℝ →ᵇ C₀(V,ℂ)) (ut : ℝ → V → ℂ) (f : V × ℝ → ℂ)
    (hf : YBound α w a M f)
    (hs : ∀ t : ℝ, t<0 → ContDiff ℝ 4 (fun x => physical γ v t x))
    (hd : ∀ t : ℝ, t<0 → ∀ x : V, HasDerivAt (fun r => physical γ v r x) (ut t x) t)
    (he : ∀ t : ℝ, t<0 → ∀ x : V,
        ut t x+(physicalPrincipal Af t x : ℂ)*Δ (Δ (fun y => physical γ v t y)) x+
          (physicalPotential Bf t x : ℂ)*physical γ v t x=f (x,t))
    (h4 : ∀ p : V × ℝ, p.2<0 → ∃ U : Set (V × ℝ), IsOpen U ∧ p∈U ∧
      ∃ C : ℝ, 0≤C ∧ HolderBound α U
        (fun q => iteratedFDeriv ℝ 4 (fun y => physical γ v q.2 y) q.1) C) :
    LocallyFiniteJets α (fun t x => physical γ v t x) ut := by
  intro R hR b hb
  obtain ⟨A,hA',ha',hb'⟩ := physical_coeff_holder α (R+13) (-R) b hα hα1.le hb Af Bf hA hB
  obtain ⟨F,hF,hf'⟩ := hf.slab_holder hα.le hw ha hM (R+13) (-R) b hb
  obtain ⟨U,hU,hu⟩ := physical_slab_bound γ (-R) b hb v
  obtain ⟨H,hH,hh⟩ := compact_local_holder α hα.le (slab (R+13) (-R) b)
    (slab_compact (R+13) (-R) b)
    (fun q => iteratedFDeriv ℝ 4 (fun y => physical γ v q.2 y) q.1)
    (fun p hp => h4 p (((slab_mem (R+13) (-R) b p).mp hp).2.2.trans_lt hb))
  have hsub : {p : V × ℝ | ‖p.1‖<R+1+12 ∧ p.2∈Icc (-R) b}⊆slab (R+13) (-R) b := by
    intro p hp
    exact (slab_mem (R+13) (-R) b p).mpr ⟨by linarith [hp.1],hp.2⟩
  obtain ⟨N,hN,hn⟩ := finite_jet_of_fourth_local α (A+F) U H (R+1) hα hα1
    (by positivity) hU hH (Icc (-R) b) (ordConnected_Icc)
    (fun p => physicalPrincipal Af p.2 p.1) (fun p => (physicalPotential Bf p.2 p.1 : ℂ))
    (fun t x => physical γ v t x) ut (fun t x => f (x,t))
    ((ha'.restrict hsub).mono (by linarith)) ((hb'.restrict hsub).mono (by linarith))
    ((hf'.restrict hsub).mono (by linarith))
    (fun t ht x _ => hu t ht x) (hh.restrict hsub)
    (fun t ht => hs t (ht.2.trans_lt hb))
    (fun t ht x => hd t (ht.2.trans_lt hb) x)
    (fun t ht x => he t (ht.2.trans_lt hb) x)
  have hm : {p : V × ℝ | ‖p.1‖≤R ∧ -R≤p.2 ∧ p.2≤b}⊆
      {p : V × ℝ | ‖p.1‖<R+1 ∧ p.2∈Icc (-R) b} := by
    intro p hp
    exact ⟨by linarith [hp.1],hp.2⟩
  exact ⟨N,hN,fun n hn' => (hn.1 n hn').restrict hm,hn.2.restrict hm⟩
end FlatSimilarity

end

end OAI
