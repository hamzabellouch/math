import Mathlib
import OAI.Probability.SKGap.Terminal.ResidualPairMoments

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n d : ℕ}

lemma finite_pair_chebyshev (w : Spin n→ℝ) (hw : ∀x,0≤w x)
    (F : Fin d→Spin n→ℝ) {ε : ℝ} (hε : 0<ε) (b : Fin d→ℝ)
    (hb : ∀k,∑x,w x*(F k x)^2≤b k) :
    (∑x,if ∃k,ε < |F k x| then w x else 0)≤(∑k,b k)/ε^2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hp (x : Spin n) : (if ∃k,ε < |F k x| then w x else 0)*ε^2≤∑k,w x*(F k x)^2 := by
    split_ifs with h
    · obtain ⟨k,hk⟩:=h
      have hs : ε^2≤(F k x)^2 := by nlinarith [sq_abs (F k x)]
      exact (mul_le_mul_of_nonneg_left hs (hw x)).trans
        (Finset.single_le_sum (f:=fun k:Fin d=>w x*(F k x)^2)
          (fun k _=>mul_nonneg (hw x) (sq_nonneg _)) (Finset.mem_univ k))
    · simp only [zero_mul]
      exact Finset.sum_nonneg (fun k _=>mul_nonneg (hw x) (sq_nonneg _))
  calc
    _ = ∑x,(if ∃k,ε < |F k x| then w x else 0)*ε^2 := Finset.sum_mul ..
    _ ≤ ∑x,∑k,w x*(F k x)^2 := Finset.sum_le_sum (fun x _=>hp x)
    _ = ∑k,∑x,w x*(F k x)^2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun k _=>hb k)

lemma squared_sqrt_scale (w F : Spin n→ℝ) :
    (∑x,w x*(F x/Real.sqrt (n:ℝ))^2)=(∑x,w x*(F x)^2)/(n:ℝ) := by
  simp only [div_pow,Real.sq_sqrt (Nat.cast_nonneg n),mul_div_assoc,Finset.sum_div]

lemma RecipeMatrixEvent.mono {j R A A' B W C : ℝ} {M N N' : ℕ} {J : Interaction n}
    (he : RecipeMatrixEvent j R A B W C M N J) (hA : A'≤A) (hN : N'≤N) :
    RecipeMatrixEvent j R A' B W C M N' J := by
  refine ⟨he.1,he.2.1,?_,?_⟩
  · intro w hl hw; exact he.2.2.1 w (hl.trans (by omega)) (wordBounded_mono hw hA)
  · intro w hl hw; exact he.2.2.2 w (hl.trans (by omega)) (wordBounded_mono hw hA)

lemma residualCoefficientBudget_depth_mono (j : ℝ) {k d : ℕ} (hk : k≤d) :
    residualCoefficientBudget j 2 k 0≤residualCoefficientBudget j 2 d 0 := by
  simp only [residualCoefficientBudget,Nat.sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) hk

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_pairing_tail (d : ℕ) {ε : ℝ} (hε : 0<ε)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a)) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀a,
      (∑x,if ∃k:Fin d,ε < |primaryPair j (J a) (h a) k x|/Real.sqrt (N a:ℝ)
        then fieldGibbs (J a) (h a) x else 0)≤C₁/(N a:ℝ) ∧
      ∀f : Observables (N a),
      (∑x,if ∃k:Fin d,ε < |primaryPair j (J a) (h a) k x|/Real.sqrt (N a:ℝ)
        then fieldGibbs (J a) (h a) x*(f x)^2 else 0)≤
        C₂/Real.sqrt (N a:ℝ)*starSquared (fieldGibbs (J a) (h a)) f := by
  classical
  have hm (k : Fin d) := gibbs_primary_pair_moments (h:=h) k.val (by omega : k.val+1<d+1)
    hR hB hW hC hn hJ hdiag
    (fun a=>(hevent a).mono (residualCoefficientBudget_depth_mono j k.isLt.le) (by omega))
  choose C₁ C₂ hC₁ hC₂ hm using hm
  refine ⟨(∑k,C₁ k)/ε^2,(∑k,C₂ k)/ε^2,div_nonneg (Finset.sum_nonneg (fun k _=>hC₁ k)) (sq_nonneg _),
    div_nonneg (Finset.sum_nonneg (fun k _=>hC₂ k)) (sq_nonneg _),fun a=>⟨?_,?_⟩⟩
  · have ht := finite_pair_chebyshev (fun x=>fieldGibbs (J a) (h a) x)
      (fun x=>(fieldGibbs_pos _ _ _).le)
      (fun k:Fin d=>fun x=>primaryPair j (J a) (h a) k x/Real.sqrt (N a:ℝ)) hε
      (fun k=>C₁ k/(N a:ℝ)) (fun k=>by
        rw [squared_sqrt_scale]
        exact div_le_div_of_nonneg_right (hm k a).1 (Nat.cast_nonneg _))
    simpa only [abs_div,abs_of_nonneg (Real.sqrt_nonneg _),←Finset.sum_div,div_right_comm] using ht
  · intro f
    have ht := finite_pair_chebyshev (fun x=>fieldGibbs (J a) (h a) x*(f x)^2)
      (fun x=>mul_nonneg (fieldGibbs_pos _ _ _).le (sq_nonneg _))
      (fun k:Fin d=>fun x=>primaryPair j (J a) (h a) k x/Real.sqrt (N a:ℝ)) hε
      (fun k=>C₂ k/Real.sqrt (N a:ℝ)*starSquared (fieldGibbs (J a) (h a)) f)
      (fun k=>(hm k a).2 f)
    convert ht using 1
    · simp only [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    · rw [←Finset.sum_mul,←Finset.sum_div]; ring

end SKGapCutoff.Recipe

end
end

end OAI
