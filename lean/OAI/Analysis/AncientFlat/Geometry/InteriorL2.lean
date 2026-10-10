import OAI.Analysis.AncientFlat.Geometry.InteriorL2Sup
import OAI.Analysis.AncientFlat.Geometry.WindowHolderCover

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace ParabolicInterior
open ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem interior_schauder_l2 (α κ K : ℝ) (hα : 0<α) (hα1 : α<1) (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder 2) a K → HolderBound α (cylinder 2) b K →
      (∀ p ∈ cylinder 2, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F N : ℝ), 0≤F → 0≤N →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p ∈ cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M : ℝ, 0≤M ∧ JetBound α (cylinder 2) u ut M) →
      HolderBound α (cylinder 2) (fun p => f p.2 p.1) F →
      eLpNorm (fun p : V × ℝ => u p.2 p.1) 2
        ((volume.prod volume).restrict (cylinder 2))≤ENNReal.ofReal N →
      (∀ p ∈ cylinder 2, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      JetBound α (cylinder 1) u ut (C*(F+N)) := by
  obtain ⟨C0,hC0,Hsup⟩ := interior_sup_l2 (V := V) α κ K hα hα1 hκ hK
  obtain ⟨C1,hC1,Hlocal⟩ := interior_schauder (V := V) α κ K hα hα1 hκ hK
  let q : ℝ := 1/16
  have hq : 0<q := by norm_num [q]
  have hq1 : q≤1 := by norm_num [q]
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  refine ⟨2*C1*(1+C0)/(q^4*q^α),by positivity,?_⟩
  intro a b ha hb hell u ut f F N hF hN hs hd hj hf hLp he
  have hu := Hsup a b ha hb hell u ut f F N hF hN hs hd hj hf hLp he
  obtain ⟨M,hM,hj⟩ := hj
  let U := C0*(F+N)
  have hU : 0≤U := by dsimp [U]; positivity
  let J := C1*(1+C0)*(F+N)
  have hJ : 0≤J := by dsimp [J]; positivity
  have hCJ : C1*(F+U)≤J := by dsimp [U,J]; nlinarith
  have Hw (p0 : V × ℝ) (hp0 : p0∈cylinder 1) :
      JetBound α (cylinder 1) (windowValue p0 q u) (windowTime p0 q ut) J := by
    have hm4 := small_window_maps (by norm_num : (0:ℝ)≤1) hq
      (by norm_num [q] : 4*q≤5/4-1) p0 hp0
    have hm0 : MapsTo (window p0 q) (cylinder 2) (cylinder (5/4)) :=
      fun p hp => hm4 (cylinder_mono (by norm_num) (by norm_num : (2:ℝ)≤4) hp)
    have hm : MapsTo (window p0 q) (cylinder 2) (cylinder 2) :=
      fun p hp => cylinder_mono (by norm_num) (by norm_num : (5/4:ℝ)≤2) (hm0 hp)
    have Hloc := Hlocal (fun p => a (window p0 q p)) (fun p => q^4 • b (window p0 q p))
      (holder_window hα.le hq hq1 p0 ha hm) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm)
      (fun p hp => hell _ (hm hp))
      (windowValue p0 q u) (windowTime p0 q ut) (windowTime p0 q f) F U hF hU
      (windowValue_contDiff p0 q u hs) (fun p hp => window_hasDerivAt p0 q u ut p (hd _ (hm hp)))
      ⟨M,hM,window_jet_bound hα.le hM hq hq1 p0 u ut hs hj hm⟩
      (holder_window_smul hα.le hF hq hq1 p0 4 hf hm) (fun p hp => hu _ (hm0 hp))
      (fun p hp => window_equation p0 q a b u ut f hs p (he _ (hm hp)))
    exact ⟨fun n hn => (Hloc.1 n hn).mono hCJ,Hloc.2.mono hCJ⟩
  have hconst : 2*J/(q^4*q^α)=(2*C1*(1+C0)/(q^4*q^α))*(F+N) := by dsimp [J]; ring
  rw [←hconst]
  constructor
  · intro n hn
    apply holder_of_windows hα.le hq hq1 hJ n hn
    intro p0 hp0
    have hh := (Hw p0 hp0).1 n hn
    have heq : (fun p : V × ℝ => iteratedFDeriv ℝ n (windowValue p0 q u p.2) p.1)=
        (fun p => q^n • iteratedFDeriv ℝ n (u (window p0 q p).2) (window p0 q p).1) :=
      funext (window_jet p0 q u hs n hn)
    rwa [heq] at hh
  · exact holder_of_windows hα.le hq hq1 hJ 4 le_rfl (fun p => ut p.2 p.1)
      (fun p0 hp0 => (Hw p0 hp0).2)
end ParabolicInterior

end

end OAI
