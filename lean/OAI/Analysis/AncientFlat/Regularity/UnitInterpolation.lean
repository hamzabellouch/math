import OAI.Analysis.AncientFlat.Regularity.FreezingResidual
import OAI.Analysis.AncientFlat.Regularity.FourthInterpolation

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicInterpolation ClassicalIBP
variable {V : Type} [NormedAddCommGroup V]
lemma cylinder_mono [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {r R : ℝ} (hr : 0≤r) (h : r≤R) :
    (cylinder r : Set (V × ℝ))⊆cylinder R := by
  intro p hp
  exact ⟨hp.1.trans_le h,lt_of_le_of_lt (neg_le_neg (pow_le_pow_left₀ hr h 4)) hp.2.1,hp.2.2⟩

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma unit_interpolation (α K ε : ℝ) (hα : 0<α) (hα1 : α<1) (hK : 0≤K) (hε : 0<ε) :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ)
      (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 4, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∀ p∈cylinder 4, ‖a p‖≤K) → (∀ p∈cylinder 4, ‖b p‖≤K) →
      (∀ p∈cylinder 4, ‖f p.2 p.1‖≤F) → (∀ p∈cylinder 4, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder 4, ∀ q∈cylinder 4,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u q.2) q.1‖≤H*pdist p q^α) →
      (∀ p∈cylinder 4, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      (∀ p∈cylinder 2, ‖iteratedFDeriv ℝ 4 (u p.2) p.1‖≤ε*H+C*U) ∧
      (∀ n : ℕ, n≤3 → HolderBound α (cylinder 2)
        (fun p => iteratedFDeriv ℝ n (u p.2) p.1)
        (F+(1+K*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖)*ε*H+D*U)) := by
  obtain ⟨C,hC,hN⟩ := fourth_sup_epsilon (V := V) (E := ℂ) α ε 3 4 hα hε (by norm_num)
  obtain ⟨L,hL,hLow⟩ := lower_jet_interpolation (V := V) (E := ℂ) α 1 2 3 hα hα1 (by norm_num) (by norm_num)
  let T : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ := traceFour
  let B := 1+K*‖T‖
  refine ⟨C,B*C+K+L,hC,by dsimp [B]; positivity,?_⟩
  intro a b u ut f F U H hF hU hH hs hd ha hb hf hu hh he
  let N := ε*H+C*U
  have hN0 : 0≤N := by dsimp [N]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hmem (t : ℝ) (ht : t∈Ioc (-16) 0) (x : V) (hx : ‖x‖<4) :
      (x,t)∈cylinder 4 := ⟨hx,by norm_num; linarith [ht.1],ht.2⟩
  have HN (t : ℝ) (ht : t∈Ioc (-16) 0) (x : V) (hx : ‖x‖<3) :
      ‖iteratedFDeriv ℝ 4 (u t) x‖≤N := by
    apply hN (u t) (hs t) U H hU hH (fun y hy => hu (y,t) (hmem t ht y hy))
    · intro y hy z hz
      simpa only [pdist,Prod.fst,Prod.snd,sub_self,abs_zero,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero] using
        hh (y,t) (hmem t ht y hy) (z,t) (hmem t ht z hz)
    · exact hx
  have Ht (t : ℝ) (ht : t∈Ioc (-16) 0) (x : V) (hx : ‖x‖<3) :
      ‖ut t x‖≤F+B*N+K*U := by
    have hp := hmem t ht x (by linarith)
    have heq : ut t x=f t x-(a (x,t) : ℂ)*Δ (Δ (u t)) x-b (x,t)*u t x := by
      have he := he (x,t) hp; dsimp only at he; linear_combination he
    have hbila : ‖Δ (Δ (u t)) x‖≤‖T‖*N := by
      rw [bilaplacian_eq_traceFour _ (hs t)]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (HN t ht x hx) (norm_nonneg T))
    rw [heq]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have h1 : |a (x,t)| *‖Δ (Δ (u t)) x‖≤K*(‖T‖*N) :=
      mul_le_mul (ha (x,t) hp) hbila (norm_nonneg _) hK
    have h2 := mul_le_mul (hb (x,t) hp) (hu (x,t) hp) (norm_nonneg _) hK
    dsimp [B]; nlinarith [hf (x,t) hp]
  have HM : N≤F+B*N+K*U := by dsimp [B]; nlinarith [mul_nonneg hK (norm_nonneg T),mul_nonneg hK hU]
  constructor
  · intro p hp
    exact HN p.2 (by simpa only [cylinder,mem_ofPred_eq,mem_Ioc,show (2:ℝ)^4=16 by norm_num] using hp.2) p.1 (by linarith [hp.1])
  · intro n hn
    have HL := hLow u ut (Ioc (-16) 0) (ordConnected_Ioc) U (F+B*N+K*U) hU (by positivity)
      (fun t _ => hs t) (fun t ht x hx => hd (x,t) (hmem t ht x (by linarith)))
      Ht (fun t ht x hx => hu (x,t) (hmem t ht x (by linarith)))
      (fun t ht x hx => (HN t ht x hx).trans HM) n hn
    convert HL using 1
    · ext p; simp only [cylinder,mem_ofPred_eq,mem_Ioc,show (2:ℝ)^4=16 by norm_num]
    · dsimp [N,B,T]; ring
end ParabolicLocalization

end

end OAI
