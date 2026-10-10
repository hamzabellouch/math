import OAI.Analysis.AncientFlat.Regularity.LowerOrderHolder
import OAI.Analysis.AncientFlat.Regularity.UnitInterpolation

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicInterpolation ParabolicLocalization ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma unit_lower_interpolation (α K ε : ℝ) (hα : 0<α) (hα1 : α<1) (hK : 0≤K) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ) (c : Coefficients V)
      (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 8, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∀ p∈cylinder 8, ‖a p‖≤K) → (∀ p∈cylinder 8, ‖b p‖≤K) →
      (∀ j, ∀ p∈cylinder 8, ‖c j p‖≤K) →
      (∀ p∈cylinder 8, ‖f p.2 p.1‖≤F) → (∀ p∈cylinder 8, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder 8, ∀ q∈cylinder 8,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u q.2) q.1‖≤H*pdist p q^α) →
      (∀ p∈cylinder 8, ut p.2 p.1+(a p:ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1+spatialLower c u p=f p.2 p.1) →
      ∀ j : ℕ, j≤3 → HolderBound α (cylinder 4)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (ε*H+C*(F+U)) := by
  obtain ⟨C0,hC0,Htop⟩ := fourth_sup_epsilon (V := V) (E := ℂ) α 1 6 8 hα (by norm_num) (by norm_num)
  let T : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ := traceFour
  let B := 1+K*‖T‖+66*K
  have hB : 0<B := by dsimp [B]; positivity
  let ε' := ε/B
  have hε' : 0<ε' := div_pos hε hB
  obtain ⟨L,hL,HL⟩ := lower_jet_interpolation (V := V) (E := ℂ) α ε' 4 5 hα hα1 hε' (by norm_num)
  let D := B*C0+270337*K
  have hD : 0≤D := by dsimp [D]; positivity
  let C := ε'+ε'*D+L
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a b c u ut f F U H hF hU hH hs hd ha hb hc hf hu hh he j hj
  let N := H+C0*U
  have hN : 0≤N := by dsimp [N]; positivity
  let M := F+B*N+270337*K*U
  have hM : 0≤M := by dsimp [M]; positivity
  have hmem (t : ℝ) (ht : t∈Ioc (-256) 0) (x : V) (hx : ‖x‖<8) : (x,t)∈cylinder 8 :=
    ⟨hx,by norm_num; linarith [ht.1],ht.2⟩
  have HN (t : ℝ) (ht : t∈Ioc (-256) 0) (x : V) (hx : ‖x‖<6) :
      ‖iteratedFDeriv ℝ 4 (u t) x‖≤N := by
    change ‖iteratedFDeriv ℝ 4 (u t) x‖≤H+C0*U
    rw [←one_mul H]
    apply Htop (u t) (hs t) U H hU hH (fun y hy => hu (y,t) (hmem t ht y hy))
    · intro y hy z hz
      simpa only [pdist,sub_self,abs_zero,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero] using
        hh (y,t) (hmem t ht y hy) (z,t) (hmem t ht z hz)
    · exact hx
  have Hlow (t : ℝ) (ht : t∈Ioc (-256) 0) (x : V) (hx : ‖x‖<5) (k : ℕ) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k (u t) x‖≤22*(4096*U+N) := by
    have H := lower_jet_bound k hk (u t) (hs t) x 6 (1/16) U N (by norm_num) hU hN
      (by linarith) (fun y hy => hu (y,t) (hmem t ht y (by linarith))) (HN t ht)
    have hp : (1/16:ℝ)^3≤(1/16:ℝ)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have hdiv : U/(1/16:ℝ)^k≤4096*U := by
      have hd := div_le_div_of_nonneg_left hU (by norm_num : (0:ℝ)<(1/16)^3) hp
      norm_num at hd
      exact hd.trans_eq (by ring)
    have hpow : (1/16:ℝ)^(4-k)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hpow hN]
  have Htime (t : ℝ) (ht : t∈Ioc (-256) 0) (x : V) (hx : ‖x‖<5) : ‖ut t x‖≤M := by
    have hp := hmem t ht x (by linarith)
    have heq : ut t x=f t x-(a (x,t):ℂ)*Δ (Δ (u t)) x-b (x,t)*u t x-spatialLower c u (x,t) := by
      have h := he (x,t) hp; dsimp only at h; linear_combination h
    have hbi : ‖Δ (Δ (u t)) x‖≤‖T‖*N := by
      rw [bilaplacian_eq_traceFour _ (hs t)]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (HN t ht x (by linarith)) (norm_nonneg T))
    have hl : ‖spatialLower c u (x,t)‖≤3*K*(22*(4096*U+N)) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ k : Fin 3, K*(22*(4096*U+N)) := Finset.sum_le_sum (fun k _ =>
          ((c k (x,t)).le_opNorm _).trans (mul_le_mul (hc k (x,t) hp) (Hlow t ht x hx (k.val+1) (by omega)) (norm_nonneg _) hK))
        _ = _ := by simp; ring
    rw [heq]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    apply (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have h1 := mul_le_mul (ha (x,t) hp) hbi (norm_nonneg _) hK
    have h2 := mul_le_mul (hb (x,t) hp) (hu (x,t) hp) (norm_nonneg _) hK
    dsimp [M,B]
    simp only [Real.norm_eq_abs] at h1
    nlinarith [hf (x,t) hp]
  have hNM : N≤M := by
    dsimp [M,B]
    nlinarith [mul_nonneg (mul_nonneg hK (norm_nonneg T)) hN, mul_nonneg hK hN, mul_nonneg hK hU]
  have Hout := HL u ut (Ioc (-256) 0) ordConnected_Ioc U M hU hM
    (fun t _ => hs t) (fun t ht x hx => hd (x,t) (hmem t ht x (by linarith))) Htime
    (fun t ht x hx => hu (x,t) (hmem t ht x (by linarith)))
    (fun t ht x hx => (HN t ht x (by linarith)).trans hNM) j hj
  have hdom : {p : V × ℝ | ‖p.1‖<4 ∧ p.2∈Ioc (-256) 0}=cylinder 4 := by ext p; norm_num [cylinder]
  rw [hdom] at Hout
  apply Hout.mono
  have hεB : ε'*B=ε := by dsimp [ε']; field_simp
  have hME : M=F+B*H+D*U := by dsimp [M,N,D]; ring
  rw [hME]
  have h0 : 0≤ε'*D := mul_nonneg hε'.le hD
  dsimp [C]
  nlinarith [mul_nonneg h0 hF,mul_nonneg hL.le hF,mul_nonneg hε'.le hU]
end ParabolicLowerOrder

end

end OAI
