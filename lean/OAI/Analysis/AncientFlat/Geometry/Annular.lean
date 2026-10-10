import OAI.Analysis.AncientFlat.Geometry.AnnularL2

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace ParabolicAnnular
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem annular_schauder (α κ K δ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α outer a K → HolderBound α outer b K →
      (∀ p∈outer, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F M : ℝ), 0≤F → 0≤M →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p∈outer, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∀ b : ℝ, b<0 → ∃ N : ℝ, 0≤N ∧ JetBound α (outer ∩ {p | p.2≤b}) u ut N) →
      HolderBound α outer (fun p => f p.2 p.1) F →
      (∀ p∈outer, ‖u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2)) →
      (∀ p∈outer, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      JetBound α inner u ut (C*(F+M)) := by

  obtain ⟨C0,hC0,Hlocal⟩ := interior_schauder_l2 (V := V) α κ K hα hα1 hκ hK
  obtain ⟨Cg,hCg,Hgrowth⟩ := annular_growth_l2 (V := V) δ hδ hδ1
  let q : ℝ := 1/32
  have hq : 0<q := by norm_num [q]
  have hq1 : q≤1 := by norm_num [q]
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  refine ⟨2*C0*(1+Cg)/(q^4*q^α),by positivity,?_⟩
  intro a b ha hb hell u ut f F M hF hM hs hd hj hf hu he
  let J := C0*(1+Cg)*(F+M)
  have hJ : 0≤J := by dsimp [J]; positivity
  have hCJ : C0*(F+Cg*M)≤J := by dsimp [J]; nlinarith [mul_nonneg hCg.le hF]
  have Hw (p0 : V × ℝ) (hp0 : p0∈inner) :
      JetBound α (cylinder 1) (windowValue p0 q u) (windowTime p0 q ut) J := by
    have hm := annular_window_maps p0 hp0
    have hm0 : MapsTo (window p0 q) (cylinder 2) outer := fun p hp => (hm hp).1
    obtain ⟨N,hN,hjN⟩ := hj p0.2 hp0.2.2.2
    have hwindow := window_jet_bound hα.le hN hq hq1 p0 u ut hs hjN hm
    have hcyl : MeasurableSet (cylinder 2 : Set (V × ℝ)) :=
      (measurableSet_lt measurable_fst.norm measurable_const).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const))
    have hmeas : AEStronglyMeasurable
        (fun p : V × ℝ => windowValue p0 q u p.2 p.1)
        ((volume.prod volume).restrict (cylinder 2)) :=
      ((HolderBound.of_jet_zero (windowValue p0 q u)
        (hwindow.1 0 (by norm_num))).continuousOn hα).aestronglyMeasurable hcyl
    have hl2 : eLpNorm (fun p : V × ℝ => windowValue p0 q u p.2 p.1) 2
        ((volume.prod volume).restrict (cylinder 2)) ≤ ENNReal.ofReal (Cg*M) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas]
      simpa [q] using Hgrowth u M hM hu p0 hp0
    have Hloc := Hlocal (fun p => a (window p0 q p)) (fun p => q^4 • b (window p0 q p))
      (holder_window hα.le hq hq1 p0 ha hm0) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm0)
      (fun p hp => hell _ (hm0 hp))
      (windowValue p0 q u) (windowTime p0 q ut) (windowTime p0 q f) F (Cg*M) hF (by positivity)
      (windowValue_contDiff p0 q u hs) (fun p hp => window_hasDerivAt p0 q u ut p (hd _ (hm0 hp)))
      ⟨N,hN,hwindow⟩
      (holder_window_smul hα.le hF hq hq1 p0 4 hf hm0) hl2
      (fun p hp => window_equation p0 q a b u ut f hs p (he _ (hm0 hp)))
    exact ⟨fun n hn => (Hloc.1 n hn).mono hCJ,Hloc.2.mono hCJ⟩
  have hconst : 2*J/(q^4*q^α)=(2*C0*(1+Cg)/(q^4*q^α))*(F+M) := by dsimp [J]; ring
  rw [←hconst]
  constructor
  · intro n hn
    apply holder_of_annular_windows hα.le hq hq1 hJ n hn
    intro p0 hp0
    have hh := (Hw p0 hp0).1 n hn
    have heq : (fun p : V × ℝ => iteratedFDeriv ℝ n (windowValue p0 q u p.2) p.1)=
        (fun p => q^n • iteratedFDeriv ℝ n (u (window p0 q p).2) (window p0 q p).1) :=
      funext (window_jet p0 q u hs n hn)
    rwa [heq] at hh
  · exact holder_of_annular_windows hα.le hq hq1 hJ 4 le_rfl (fun p => ut p.2 p.1)
      (fun p0 hp0 => (Hw p0 hp0).2)
end ParabolicAnnular

end

end OAI
