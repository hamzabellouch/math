import OAI.Analysis.AncientFlat.Evolution.LocalizedFrozen
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicCommutator ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma bilaplacian_cutoff (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) (x : V) :
    Δ (Δ (cutoffValue u t)) x=cutoff t x • Δ (Δ (u t)) x+
      traceFour (ParabolicCommutator.commutator (cutoff t) (u t) x) := by
  rw [bilaplacian_eq_traceFour _ (cutoffValue_contDiff u t (hs t)),
    bilaplacian_eq_traceFour _ (hs t),ParabolicCommutator.commutator,map_sub,map_smul]
  abel
lemma cutoffResidual_eq (c : ℝ) (a : V × ℝ → ℝ) (b : V × ℝ → ℂ)
    (u ut f : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ)
    (he : ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) :
    cutoffResidual c u ut p.2 p.1=
      cutoff p.2 p.1 • f p.2 p.1+
      cutoff p.2 p.1 • ((c-a p) • Δ (Δ (u p.2)) p.1)+
      -(cutoff p.2 p.1 • (b p*u p.2 p.1))+
      cutoffTime p.2 p.1 • u p.2 p.1+
      c • traceFour (ParabolicCommutator.commutator (cutoff p.2) (u p.2) p.1) := by
  rw [cutoffResidual,bilaplacian_cutoff u hs,←he]
  simp only [cutoffDerivative,Complex.real_smul,Complex.ofReal_sub]
  ring
lemma cutoffResidual_zero (c : ℝ) (u ut : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (p : V × ℝ) (hx : 7/4≤‖p.1‖) : cutoffResidual c u ut p.2 p.1=0 := by
  rw [cutoffResidual,cutoffDerivative_zero u ut p.2 p.1 (by linarith)]
  rw [bilaplacian_eq_traceFour _ (cutoffValue_contDiff u p.2 (hs p.2))]
  have h : iteratedFDeriv ℝ 4 (cutoffValue u p.2) p.1=0 := cutoff_product_jet_zero 4 p.2 (u p.2) p.1 hx
  rw [h,map_zero,smul_zero,add_zero]
def residualBudget (A δ K F H N L : ℝ) : ℝ :=
  5*(2*A*F+2*A*(δ*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*H+
      K*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*N+
      δ*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*N)+
      4*A*K*L+2*A*L+30*K*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*A*L)
lemma cutoffResidual_bound (α A δ K F H N L : ℝ) (hα : 0≤α) (hα1 : α≤1)
    (hA : 0≤A) (hδ : 0≤δ) (hK : 0≤K) (hF : 0≤F) (hH : 0≤H) (hN : 0≤N) (hL : 0≤L)
    (haχ : ∀ n : ℕ, n≤4 → HolderBound α univ
      (fun p : V × ℝ => iteratedFDeriv ℝ n (cutoff p.2) p.1) A)
    (hat : HolderBound α univ (fun p : V × ℝ => cutoffTime p.2 p.1) A)
    (c : ℝ) (hc : 0≤c) (hcK : c≤K) (a : V × ℝ → ℝ) (b : V × ℝ → ℂ)
    (ha : HolderBound α (cylinder 2) a K) (hb : HolderBound α (cylinder 2) b K)
    (hδa : ∀ p∈cylinder 2, ‖c-a p‖≤δ)
    (u ut f : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hf : HolderBound α (cylinder 2) (fun p => f p.2 p.1) F)
    (hu : ∀ n : ℕ, n≤3 → HolderBound α (cylinder 2) (fun p => iteratedFDeriv ℝ n (u p.2) p.1) L)
    (hn : ∀ p∈cylinder 2, ‖iteratedFDeriv ℝ 4 (u p.2) p.1‖≤N)
    (hh : ∀ p∈cylinder 2, ∀ q∈cylinder 2,
      ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u q.2) q.1‖≤H*pdist p q^α)
    (he : ∀ p∈cylinder 2,
      ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) :
    HolderBound α {p : V × ℝ | p.2∈Icc (-2) 0}
      (fun p => cutoffResidual c u ut p.2 p.1) (residualBudget (V := V) A δ K F H N L) := by
  let T : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ := traceFour
  have Hχ := (HolderBound.of_jet_zero cutoff (haχ 0 (by omega))).restrict (subset_univ (cylinder 2))
  have Hu := HolderBound.of_jet_zero u (hu 0 (by omega))
  have Hq : HolderBound α (cylinder 2) (fun p => (c-a p) • Δ (Δ (u p.2)) p.1)
      (δ*(‖T‖*H)+K*(‖T‖*N)+δ*(‖T‖*N)) := by
    apply scalar_product_separated α δ K (‖T‖*N) (‖T‖*H) (cylinder 2)
      (fun p => c-a p) (fun p => Δ (Δ (u p.2)) p.1) hδ hK (by positivity) (by positivity) hδa
    · intro p hp q hq
      simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using ha.2 p hp q hq
    · intro p hp
      rw [bilaplacian_eq_traceFour _ (hs p.2)]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hn p hp) (norm_nonneg T))
    · intro p hp q hq
      rw [bilaplacian_eq_traceFour _ (hs p.2),bilaplacian_eq_traceFour _ (hs q.2)]
      change ‖T _-T _‖≤_
      rw [←map_sub]
      exact (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hh p hp q hq) (norm_nonneg T)).trans_eq (by ring))
  have Hc := commutator_holder α (cylinder 2) cutoff u A L hA hL
    (fun p _ => (cutoff_contDiff p.2).of_le (by change ((4:ℕ∞):WithTop ℕ∞)≤((⊤:ℕ∞):WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    (fun p _ => hs p.2) (fun n _ hn => (haχ n hn).restrict (subset_univ _)) hu
  have Hc' := ((Hc.clm T).const_smul c).mono
    (show |c| *(‖T‖*(30*A*L))≤30*K*‖T‖*A*L by rw [abs_of_nonneg hc]; nlinarith [mul_nonneg hA hL, norm_nonneg T, mul_le_mul_of_nonneg_right hcK (show 0≤‖T‖*(30*A*L) by positivity)])
  have Hsum := ((((Hχ.smul hf hA hF).add (Hχ.smul Hq hA (by positivity))).add
    ((Hχ.smul (hb.mul Hu hK hL) hA (by positivity)).neg)).add
    ((hat.restrict (subset_univ (cylinder 2))).smul Hu hA hL)).add Hc'
  have Hlocal : HolderBound α (cylinder 2) (fun p => cutoffResidual c u ut p.2 p.1)
      (residualBudget (V := V) A δ K F H N L/5) := by
    have hcst : (2*A*F+2*A*(δ*(‖T‖*H)+K*(‖T‖*N)+δ*(‖T‖*N))+2*A*(2*K*L)+2*A*L)+30*K*‖T‖*A*L=
        residualBudget (V := V) A δ K F H N L/5 := by dsimp [residualBudget,T]; ring
    rw [←hcst]
    refine ⟨fun p hp => ?_,fun p hp q hq => ?_⟩
    · dsimp only
      rw [cutoffResidual_eq c a b u ut f hs p (he p hp)]
      exact Hsum.1 p hp
    · dsimp only
      rw [cutoffResidual_eq c a b u ut f hs p (he p hp),cutoffResidual_eq c a b u ut f hs q (he q hq)]
      exact Hsum.2 p hp q hq
  convert cylinder_two_globalize hα hα1 (by dsimp [residualBudget]; positivity) _ Hlocal
    (fun p hx => cutoffResidual_zero c u ut hs p hx) using 1; ring
end ParabolicLocalization

end

end OAI
