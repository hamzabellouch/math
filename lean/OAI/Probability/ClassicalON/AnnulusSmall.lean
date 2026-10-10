import OAI.Probability.ClassicalON.AnnulusResponse

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace ClassicalON
namespace LatticeGraph

def rotationCostConstant (β C : ℝ) : ℝ :=
  4*((6*β^2+4*β*Real.sqrt β+β)*(48*(2*modeBlockConstant C)^4)+
        β*(576*C^2*(2*modeBlockConstant C)^2))

def transferCostConstant (β L D : ℝ) : ℝ :=
  β*(512*D*(2*L+D))+2*(β*512*D)*Real.sqrt (β*(512*L^2))+(β*512*D)^2

theorem theta_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0<k) (hG : G.WithinDyadicBox k)
    (β : ℝ) (hβ : 0 ≤ β) (b : G.edges → ℝ) (hb : ∀ e,0 ≤ b e ∧ b e ≤ β)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P)
    (C L D : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    -(G.spinSystem 3 b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤
      rotationCostConstant β C/(k:ℝ)+transferCostConstant β L D/(2:ℝ)^k := by
  let S := G.spinSystem 3 b P
  let a := rotationCostConstant β C/(k:ℝ)
  let N : ℝ := (2:ℝ)^k
  have hN : 0<N := by dsimp [N]; positivity
  have hN1 : 1≤N := one_le_pow₀ (by norm_num)
  have ha : 0≤a := by dsimp [a,rotationCostConstant]; positivity
  have hr : -(S.complexSecondResponse (fun e => (G.profileEdge k e:ℂ))
      (fun e => conj (G.profileEdge k e:ℂ))).re ≤ a := by
    simp only [Complex.conj_ofReal,S.complexSecondResponse_ofReal,Complex.ofReal_re]
    exact G.profile_response_bound k hk hG β hβ b hb P hP C hC hv hLip
  have ht := S.response_transfer β a hβ ha hb
    (fun e => (G.thetaEdge k e:ℂ)) (fun e => (G.profileEdge k e:ℂ)) hr
  simp only [Complex.conj_ofReal,S.complexSecondResponse_ofReal,Complex.ofReal_re,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at ht
  obtain ⟨hs1,hs2,hs3⟩ := G.theta_sum_bounds k hG L D hL hD he
  have hsq : Real.sqrt (β*∑ e, |G.thetaEdge k e|^2) ≤ Real.sqrt (β*(512*L^2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs2 hβ)
  have h1n : 0 ≤ β*∑ e, |G.thetaEdge k e-G.profileEdge k e| := by positivity
  have hh : -(S.secondAxisResponse (G.thetaEdge k) (G.thetaEdge k)) ≤ a+
      β*(512*D*(2*L+D)/N^2)+2*(β*(512*D/N))*Real.sqrt (β*(512*L^2))+(β*(512*D/N))^2 := by
    exact ht.trans (add_le_add (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hs3 hβ))
      (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs1 hβ) (by norm_num))
        hsq (Real.sqrt_nonneg _) (by positivity)))
      (pow_le_pow_left₀ h1n (mul_le_mul_of_nonneg_left hs1 hβ) 2))
  apply hh.trans
  change a+β*(512*D*(2*L+D)/N^2)+2*(β*(512*D/N))*Real.sqrt (β*(512*L^2))+(β*(512*D/N))^2 ≤ a+transferCostConstant β L D/N
  rw [add_assoc a,add_assoc a]
  apply add_le_add le_rfl
  have hN2 : N ≤ N^2 := by nlinarith
  have hQ : 0 ≤ β*(512*D*(2*L+D))+(β*512*D)^2 := by positivity
  calc _ = (β*(512*D*(2*L+D))+(β*512*D)^2)/N^2+
        (2*(β*512*D)*Real.sqrt (β*(512*L^2)))/N := by ring
       _ ≤ (β*(512*D*(2*L+D))+(β*512*D)^2)/N+
        (2*(β*512*D)*Real.sqrt (β*(512*L^2)))/N :=
        add_le_add (div_le_div_of_nonneg_left hQ hN hN2) le_rfl
       _ = _ := by unfold transferCostConstant; ring

theorem annulus_response_small (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 4 ≤ k ∧ ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e,0 ≤ b e ∧ b e ≤ β) →
      ∀ (P : G.vertices → Option (Spin 3)), G.BoundaryPins k 3 P →
      -(G.spinSystem 3 b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤ ε := by
  obtain ⟨C,hC,hv,hLip⟩ := profiles_uniform_bound
  obtain ⟨L,D,hL,hD,he⟩ := theta_edge_bounds
  have ht1 : Tendsto (fun k : ℕ => rotationCostConstant β C/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun k : ℕ => transferCostConstant β L D/(2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have ht : Tendsto (fun k : ℕ => rotationCostConstant β C/(k:ℝ)+transferCostConstant β L D/(2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [add_zero] using ht1.add ht2
  obtain ⟨k,hk,hkε⟩ := ((eventually_ge_atTop 4).and (ht.eventually_lt_const hε)).exists
  refine ⟨k,hk,?_⟩
  intro G hG b hb P hP
  exact (G.theta_response_bound k (by omega) hG β hβ b hb P hP C L D (by linarith) hL hD hv hLip
    (he G k hk)).trans hkε.le

end LatticeGraph
end ClassicalON

end

end OAI
