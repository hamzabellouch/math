import OAI.Analysis.AncientFlat.Evolution.InitialWindows
import OAI.Analysis.AncientFlat.Evolution.InitialClosure
import OAI.Analysis.AncientFlat.Geometry.InteriorSchauder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicInitial
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem initial_schauder (α κ K : ℝ) (hα : 0<α) (hα1 : α<1) (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ h : ℝ, 0<h → h≤1 → ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (slab 2 h) a K → HolderBound α (slab 2 h) b K →
      (∀ p∈slab 2 h, κ≤a p) → ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p∈slab 2 h, HasDerivWithinAt (fun t => u t p.1) (ut p.2 p.1) (Icc 0 h) p.2) →
      (∀ x : V, ‖x‖<2 → u 0 x=0) →
      (∃ M : ℝ, 0≤M ∧ JetBound α (slab 2 h) u ut M) →
      HolderBound α (slab 2 h) (fun p => f p.2 p.1) F →
      (∀ p∈slab 2 h, ‖u p.2 p.1‖≤U) →
      (∀ p∈slab 2 h, ut p.2 p.1+(a p:ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      JetBound α (slab 1 h) u ut (C*(F+U)) := by
  obtain ⟨Ce,hCe,HE⟩ := initial_continuation (V := V) α K hα hα1 hK
  obtain ⟨Ci,hCi,HI⟩ := interior_schauder (V := V) α κ (2*K) hα hα1 hκ (by positivity)
  let q : ℝ := 1/4
  let A := Ci*(1+2*Ce)
  let C := 2*A/(q^4*q^α)
  have hq : 0<q := by norm_num [q]
  have hq1 : q≤1 := by norm_num [q]
  have hA : 0<A := by dsimp [A]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro h hh hh1 a b ha hb hell u ut f F U hF hU hs hd hu0 hj hf hu he
  obtain ⟨v,vt,g,hvu,hvs,hvd,hvj,hgf,hvuB,hve⟩ := HE h hh a b ha hb u ut f F U hF hU hs hd hu0 hj hf hu he
  have hsub : (initialStrip h : Set (V × ℝ))⊆initialClosedStrip h := initialStrip_subset_closed h
  have hcoeffSub : (initialClosedStrip h : Set (V × ℝ))⊆{p : V × ℝ | ‖p.1‖<2 ∧ p.2∈Icc (-1/2:ℝ) h} :=
    fun p hp => ⟨by linarith [hp.1],hp.2⟩
  have ha' : HolderBound α (initialClosedStrip h) (initialCoeff a) (2*K) :=
    (holder_initialCoeff hα.le hK hh.le (by norm_num : (-1/2:ℝ)≤0) ha).restrict hcoeffSub
  have hb' : HolderBound α (initialClosedStrip h) (initialCoeff b) (2*K) :=
    (holder_initialCoeff hα.le hK hh.le (by norm_num : (-1/2:ℝ)≤0) hb).restrict hcoeffSub
  have hell' (p : V × ℝ) (hp : p∈initialStrip h) : κ ≤ initialCoeff a p := by
    by_cases ht : p.2<0
    · rw [initialCoeff_neg a p ht]
      exact hell (p.1,0) ⟨by linarith [hp.1],le_rfl,hh.le⟩
    · rw [initialCoeff_pos a p (le_of_not_gt ht)]
      exact hell p ⟨by linarith [hp.1],le_of_not_gt ht,hp.2.2.le⟩
  have hCF : 0≤Ce*F := mul_nonneg hCe.le hF
  have hSum : 0≤F+U := add_nonneg hF hU
  have hlocal (p0 : V × ℝ) (hp0 : p0∈openSlab 1 h) :
      JetBound α (cylinder 1) (windowValue p0 q v) (windowTime p0 q vt) (A*(F+U)) := by
    have hm : MapsTo (window p0 q) (cylinder 2) (initialStrip h) := initial_window_maps p0 hp0
    have hmc : MapsTo (window p0 q) (cylinder 2) (initialClosedStrip h) := fun p hp => hsub (hm hp)
    have H := HI (fun p => initialCoeff a (window p0 q p)) (fun p => q^4 • initialCoeff b (window p0 q p))
      (holder_window hα.le hq hq1 p0 ha' hmc)
      (holder_window_smul hα.le (by positivity : 0≤2*K) hq hq1 p0 4 hb' hmc)
      (fun p hp => hell' _ (hm hp))
      (windowValue p0 q v) (windowTime p0 q vt) (windowTime p0 q g) (Ce*F) (U+Ce*F) hCF (by positivity)
      (windowValue_contDiff p0 q v hvs)
      (fun p hp => window_hasDerivAt p0 q v vt p (hvd _ (hm hp)))
      (by
        obtain ⟨M,hM,HJ⟩ := hvj
        exact ⟨M,hM,window_jet_bound hα.le hM hq hq1 p0 v vt hvs HJ hmc⟩)
      (holder_window_smul hα.le hCF hq hq1 p0 4 hgf hmc)
      (fun p hp => hvuB _ (hm hp))
      (fun p hp => window_equation p0 q (initialCoeff a) (initialCoeff b) v vt g hvs p (hve _ (hm hp)))
    have hbnd : Ci*(Ce*F+(U+Ce*F))≤A*(F+U) := by
      dsimp [A]
      nlinarith [mul_nonneg hCi.le hF,mul_nonneg (mul_nonneg hCi.le hCe.le) hU]
    exact ⟨fun n hn => (H.1 n hn).mono hbnd,H.2.mono hbnd⟩
  have hopenV : JetBound α (openSlab 1 h) v vt (C*(F+U)) := by
    have hEq : 2*(A*(F+U))/(q^4*q^α)=C*(F+U) := by dsimp [C]; ring
    constructor
    · intro n hn
      rw [←hEq]
      apply holder_of_initial_windows hα.le hq hq1 (mul_nonneg hA.le hSum) n hn
      intro p0 hp0
      have H := (hlocal p0 hp0).1 n hn
      have heq : (fun p : V × ℝ => iteratedFDeriv ℝ n (windowValue p0 q v p.2) p.1)=
          (fun p => q^n • iteratedFDeriv ℝ n (v (window p0 q p).2) (window p0 q p).1) :=
        funext (window_jet p0 q v hvs n hn)
      rwa [heq] at H
    · rw [←hEq]
      exact holder_of_initial_windows hα.le hq hq1 (mul_nonneg hA.le hSum) 4 le_rfl _ (fun p0 hp0 => (hlocal p0 hp0).2)
  have hopen : JetBound α (openSlab 1 h) u ut (C*(F+U)) := by
    constructor
    · intro n hn
      refine ⟨fun p hp => ?_,fun p hp s hs => ?_⟩
      · simpa only [(hvu p.2 hp.2.1).1] using (hopenV.1 n hn).1 p hp
      · simpa only [(hvu p.2 hp.2.1).1,(hvu s.2 hs.2.1).1] using (hopenV.1 n hn).2 p hp s hs
    · refine ⟨fun p hp => ?_,fun p hp s hs => ?_⟩
      · simpa only [(hvu p.2 hp.2.1).2] using hopenV.2.1 p hp
      · simpa only [(hvu p.2 hp.2.1).2,(hvu s.2 hs.2.1).2] using hopenV.2.2 p hp s hs
  obtain ⟨M,hM,HJ⟩ := hj
  have hsmall : (slab 1 h : Set (V × ℝ))⊆slab 2 h := fun p hp => ⟨by linarith [hp.1],hp.2⟩
  exact ⟨fun n hn => holder_close_initial hα hh _ ((HJ.1 n hn).restrict hsmall) (hopen.1 n hn),
    holder_close_initial hα hh _ (HJ.2.restrict hsmall) hopen.2⟩
end ParabolicInitial

end

end OAI
