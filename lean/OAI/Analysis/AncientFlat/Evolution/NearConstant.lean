import OAI.Analysis.AncientFlat.Regularity.UnitInterpolation
import OAI.Analysis.AncientFlat.Regularity.ResidualBudget

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem near_constant_fourth (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ δ C : ℝ, 0<δ ∧ δ≤1 ∧ 0<C ∧ ∀ (c : ℝ), κ≤c → c≤K →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder 4) a K → HolderBound α (cylinder 4) b K →
      (∀ p∈cylinder 2, ‖c-a p‖≤δ) →
      ∀ (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 4, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder 4) u ut M) →
      HolderBound α (cylinder 4) (fun p => f p.2 p.1) F →
      (∀ p∈cylinder 4, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder 4, ∀ q∈cylinder 4,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u q.2) q.1‖≤H*pdist p q^α) →
      (∀ p∈cylinder 4, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      HolderBound α (cylinder 1) (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) (θ*H+C*(F+U)) := by
  obtain ⟨A,hA,hχ,hχt⟩ := cutoff_uniform_holder (V := V) α hα hα1.le
  obtain ⟨C0,hC0,hest⟩ := localized_fourth_estimate (V := V) α κ K hα hα1 hκ hK
  let P := budgetFactor (V := V) A K
  have hP : 0<P := budgetFactor_pos hA.le hK
  let B := 1+K*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖
  have hB : 0<B := by dsimp [B]; positivity
  let δ := min 1 (θ/(4*C0*P))
  let ε := θ/(4*C0*P*(1+B))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := min_le_left _ _
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨C1,D,hC1,hD,hint⟩ := unit_interpolation (V := V) α K ε hα hα1 hK hε
  let C := C0*P*(2+C1+D)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro c hκc hcK a b ha hb hosc u ut f F U H hF hU hH hs hd hj hf hu hh he
  have h24 : (cylinder 2 : Set (V × ℝ))⊆cylinder 4 := cylinder_mono (by norm_num) (by norm_num)
  obtain ⟨hN,hL⟩ := hint a b u ut f F U H hF hU hH hs hd ha.1 hb.1 hf.1 hu hh he
  let N := ε*H+C1*U
  let L := F+B*ε*H+D*U
  have hN0 : 0≤N := by dsimp [N]; positivity
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hres := cutoffResidual_bound α A δ K F H N L hα.le hα1.le hA.le hδ.le hK hF hH hN0 hL0
    hχ hχt c (hκ.le.trans hκc) hcK a b (ha.restrict h24) (hb.restrict h24) hosc
    u ut f hs (hf.restrict h24) hL hN (fun p hp q hq => hh p (h24 hp) q (h24 hq))
    (fun p hp => he p (h24 hp))
  have hj2 : ∃ M, 0≤M ∧ JetBound α (cylinder 2) u ut M := by
    obtain ⟨M,hM,hm,ht⟩ := hj
    exact ⟨M,hM,(fun n hn => (hm n hn).restrict h24),ht.restrict h24⟩
  have Hest := hest c hκc hcK u ut hs (fun p hp => hd p (h24 hp)) hj2
    (residualBudget (V := V) A δ K F H N L) (by unfold residualBudget; positivity) hres
  apply Hest.mono
  have hr := residualBudget_le (V := V) hA.le hδ.le hδ1 hK hF hH hN0 hL0
  have hsmall : C0*P*(δ+(1+B)*ε)≤θ := by
    have hδle := min_le_right (1:ℝ) (θ/(4*C0*P))
    change δ≤θ/(4*C0*P) at hδle
    have hd' := (le_div_iff₀ (show 0<4*C0*P by positivity)).mp hδle
    have he' : 4*C0*P*(1+B)*ε=θ := by
      dsimp [ε]; field_simp
    nlinarith
  have hcf : 2*(C0*P)≤C := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg hC0.le hP.le) (add_nonneg hC1.le hD.le)]
  have hcu : C0*P*(C1+D)≤C := by dsimp [C]; nlinarith [mul_pos hC0 hP]
  calc
    _≤C0*(P*(F+δ*H+N+L)) := mul_le_mul_of_nonneg_left hr hC0.le
    _=(C0*P*(δ+(1+B)*ε))*H+(2*(C0*P))*F+(C0*P*(C1+D))*U := by dsimp [N,L]; ring
    _≤θ*H+C*F+C*U := by gcongr
    _=_ := by ring
end ParabolicLocalization

end

end OAI
