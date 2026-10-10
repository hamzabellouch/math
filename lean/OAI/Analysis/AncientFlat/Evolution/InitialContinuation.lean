import OAI.Analysis.AncientFlat.Evolution.CutoffCore
import OAI.Analysis.AncientFlat.Evolution.InitialSource
import OAI.Analysis.AncientFlat.Evolution.BackwardModel
import OAI.Analysis.AncientFlat.Evolution.InitialPaste
import OAI.Analysis.AncientFlat.Evolution.InitialCoefficients

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicInitial
open ParabolicInterior ParabolicLocalization ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def initialStrip (h : ℝ) : Set (V × ℝ) := {p | ‖p.1‖<3/2 ∧ p.2∈Ioo (-1/4:ℝ) h}
def initialClosedStrip (h : ℝ) : Set (V × ℝ) := {p | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) h}

theorem initial_continuation (α K : ℝ) (hα : 0<α) (hα1 : α<1) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ h : ℝ, 0<h → ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (slab 2 h) a K → HolderBound α (slab 2 h) b K →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈slab 2 h, HasDerivWithinAt (fun t => u t p.1) (ut p.2 p.1) (Icc 0 h) p.2) →
      (∀ x, ‖x‖<2 → u 0 x=0) →
      (∃ M, 0≤M ∧ JetBound α (slab 2 h) u ut M) →
      HolderBound α (slab 2 h) (fun p => f p.2 p.1) F →
      (∀ p∈slab 2 h, ‖u p.2 p.1‖≤U) →
      (∀ p∈slab 2 h, ut p.2 p.1+(a p:ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∃ v vt g : ℝ → V → ℂ,
        (∀ t, 0≤t → v t=u t ∧ vt t=ut t) ∧
        (∀ t, ContDiff ℝ 4 (v t)) ∧
        (∀ p∈initialStrip h, HasDerivAt (fun t => v t p.1) (vt p.2 p.1) p.2) ∧
        (∃ M, 0≤M ∧ JetBound α (initialClosedStrip h) v vt M) ∧
        HolderBound α (initialClosedStrip h) (fun p => g p.2 p.1) (C*F) ∧
        (∀ p∈initialStrip h, ‖v p.2 p.1‖≤U+C*F) ∧
        (∀ p∈initialStrip h, vt p.2 p.1+((initialCoeff a p : ℝ):ℂ)*Δ (Δ (v p.2)) p.1+
          initialCoeff b p*v p.2 p.1=g p.2 p.1) := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  obtain ⟨A,hA,HA⟩ := exists_initial_source (V := V) α hα hα1
  obtain ⟨B,hB,HB⟩ := exists_backward_model (V := V) α hα hα1
  let T := (traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)
  let N := B*A
  let D := N+2*K*‖T‖*N+2*K*N
  let C := 2*(1+D)+N
  have hN : 0<N := mul_pos hB hA
  have hD : 0≤D := by dsimp [D]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro h hh a b ha hb u ut f F U hF hU hs hd hu0 hj hf hu he
  obtain ⟨g0,hg0,hgh,hge⟩ := HA h hh.le (fun p => f p.2 p.1) F hF hf
  obtain ⟨w,wt,hw0,hwt0,hws,hwj,hwd⟩ := HB g0 (A*F) (by positivity) hg0 hgh
  have hNF : B*(A*F)=N*F := by dsimp [N]; ring
  rw [hNF] at hwj
  have hsub : (slab (3/2) h : Set (V × ℝ))⊆slab 2 h := fun p hp => ⟨by linarith [hp.1],hp.2⟩
  have hz (n : ℕ) (x : V) (hx : ‖x‖<2) : iteratedFDeriv ℝ n (u 0) x=0 := initial_jet_zero (u 0) hu0 n x hx
  have hbi (x : V) (hx : ‖x‖<2) : Δ (Δ (u 0)) x=0 := by
    rw [bilaplacian_eq_traceFour _ (hs 0),hz 4 x hx,map_zero]
  have hw0' : w 0=fun _ => (0:ℂ) := funext hw0
  have hwb : Δ (Δ (w 0))=0 := by
    rw [hw0',InnerProductSpace.laplacian_const]
    exact InnerProductSpace.laplacian_const (c := (0:ℂ))
  have htrace (x : V) (hx : ‖x‖<3/2) : wt 0 x=ut 0 x := by
    have hx2 : ‖x‖<2 := by linarith
    have H := he (x,0) ⟨hx2,le_rfl,hh.le⟩
    dsimp only at H
    rw [hbi x hx2,hu0 x hx2] at H
    simp only [mul_zero,add_zero] at H
    rw [hwt0,hge x hx.le]
    exact H.symm
  let v := initialJoin u w
  let vt := initialJoin ut wt
  let fm : V × ℝ → ℂ := fun p => wt p.2 p.1+(a (p.1,0):ℂ)*Δ (Δ (w p.2)) p.1+b (p.1,0)*w p.2 p.1
  let g : ℝ → V → ℂ := fun t x => timeJoin fm (fun p => f p.2 p.1) (x,t)
  have hN0 : 0≤N*F := mul_nonneg hN.le hF
  have hwjs : JetBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) 0} w wt (N*F) :=
    ⟨fun j hj => (hwj.1 j hj).restrict (fun p hp => ⟨by linarith [hp.1],hp.2⟩),
      hwj.2.restrict (fun p hp => ⟨by linarith [hp.1],hp.2⟩)⟩
  have hWT : HolderBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) 0}
      (fun p => Δ (Δ (w p.2)) p.1) (‖T‖*(N*F)) := by
    have H := (hwjs.1 4 le_rfl).clm T
    refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
    · simpa only [bilaplacian_eq_traceFour _ (hws p.2 hp.2)] using H.1 p hp
    · simpa only [bilaplacian_eq_traceFour _ (hws p.2 hp.2),
        bilaplacian_eq_traceFour _ (hws q.2 hq.2)] using H.2 p hp q hq
  have hWA := (holder_initial_trace hα.le hK hh.le (ha.restrict hsub)).smul hWT hK (by positivity)
  have hWB := (holder_initial_trace hα.le hK hh.le (hb.restrict hsub)).mul
    (HolderBound.of_jet_zero w (hwjs.1 0 (by omega))) hK hN0
  have hFM : HolderBound α {p : V × ℝ | ‖p.1‖<3/2 ∧ p.2∈Icc (-1/2:ℝ) 0} fm (D*F) := by
    have H := (hwjs.2.add hWA).add hWB
    convert H using 1
    dsimp [D]
    ring
  have hFM0 (x : V) (hx : ‖x‖<3/2) : fm (x,0)=f 0 x := by
    dsimp [fm]
    rw [hwb,hw0,hwt0,hge x hx.le]
    simp
  have hG0 := holder_timeJoin α (F+D*F) (-1/2) h hα.le (by positivity) (by norm_num) hh.le
    {x : V | ‖x‖<3/2} fm (fun p => f p.2 p.1)
    (hFM.mono (by linarith)) ((hf.restrict hsub).mono (by nlinarith [mul_nonneg hD hF])) hFM0
  have hG : HolderBound α (initialClosedStrip h) (fun p => g p.2 p.1) (C*F) := by
    apply hG0.mono
    dsimp [C]; nlinarith
  refine ⟨v,vt,g,?_,?_,?_,?_,hG,?_,?_⟩
  · intro t ht; exact ⟨initialJoin_pos u w ht,initialJoin_pos ut wt ht⟩
  · exact initialJoin_contDiff u w hs hws
  · intro p hp
    exact initialJoin_hasDerivAt h hh u ut w wt p.1
      (fun t ht => hd (p.1,t) ⟨by linarith [hp.1],ht⟩)
      (fun t ht => hwd t ht p.1)
      (by rw [hw0,hu0 p.1 (by linarith [hp.1])]) (htrace p.1 hp.1) p.2 hp.2
  · obtain ⟨M,hM,HJ⟩ := hj
    refine ⟨2*(M+N*F),by positivity,?_⟩
    apply initialJoin_holder_jet α h M (N*F) hα.le hh.le hM hN0 u ut w wt
      ⟨fun j hj => (HJ.1 j hj).restrict hsub,HJ.2.restrict hsub⟩ hwjs _ htrace
    intro j hj x hx
    rw [hw0',hz j x (by linarith)]
    simp
  · intro p hp
    by_cases ht : p.2<0
    · rw [show v p.2=w p.2 from initialJoin_neg u w ht (by linarith [hp.2.1])]
      have H := (HolderBound.of_jet_zero w (hwjs.1 0 (by omega))).1 p
        ⟨hp.1,by linarith [hp.2.1],ht.le⟩
      exact H.trans (by dsimp [C]; nlinarith [mul_nonneg hD hF])
    · rw [show v p.2=u p.2 from initialJoin_pos u w (le_of_not_gt ht)]
      exact (hu p ⟨by linarith [hp.1],le_of_not_gt ht,hp.2.2.le⟩).trans
        (le_add_of_nonneg_right (mul_nonneg hC.le hF))
  · intro p hp
    by_cases ht : p.2<0
    · rw [show v p.2=w p.2 from initialJoin_neg u w ht (by linarith [hp.2.1]),
        show vt p.2=wt p.2 from initialJoin_neg ut wt ht (by linarith [hp.2.1]),
        initialCoeff_neg a p ht,initialCoeff_neg b p ht]
      simp only [g,timeJoin,ite_eq_left ht,fm]
    · rw [show v p.2=u p.2 from initialJoin_pos u w (le_of_not_gt ht),
        show vt p.2=ut p.2 from initialJoin_pos ut wt (le_of_not_gt ht),
        initialCoeff_pos a p (le_of_not_gt ht),initialCoeff_pos b p (le_of_not_gt ht)]
      simpa only [g,timeJoin,Prod.snd,ite_eq_right ht,Prod.fst] using
        he p ⟨by linarith [hp.1],le_of_not_gt ht,hp.2.2.le⟩
end ParabolicInitial

end

end OAI
