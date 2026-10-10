import Mathlib

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma tame_iteratedFDeriv_comp (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : F → G) (f : E → F), ContDiff ℝ ∞ g  →  ContDiff ℝ ∞ f  →
      ∀ x, (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i g (f x)‖ ≤ A)  →
        (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i f x‖ ≤ A)  →
        ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤
          C*(1+‖iteratedFDeriv ℝ (n+1) g (f x)‖+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  let c : ℕ → ℝ := fun i => (n.choose i : ℝ)*i.factorial*A^(i+1)
  let S := ∑ i∈Finset.range (n+1), c i
  refine ⟨A+S*(A+1),by dsimp [S,c]; positivity,?_⟩
  intro g f hg hf x hgl hfl
  let Mg := ‖iteratedFDeriv ℝ (n+1) g (f x)‖
  let Mf := ‖iteratedFDeriv ℝ (n+1) f x‖
  have hMg : 0 ≤ Mg := norm_nonneg _
  have hMf : 0 ≤ Mf := norm_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcn (i : ℕ) : 0 ≤ c i := by dsimp [c]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hcn i)
  have hfg : fderiv ℝ (g ∘ f) =
      (fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by simp) (f y)) (hf.differentiable (by simp) y)
  have hcomp (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖ ≤ i.factorial*(A+Mg)*A^i := by
    apply norm_iteratedFDeriv_comp_le (n:=i) (hg.fderiv_right (m:=∞) (by simp)) hf (by exact_mod_cast le_top) x
    · intro j hj
      rw [norm_iteratedFDeriv_fderiv]
      by_cases hjn : j+1 ≤ n
      · exact (hgl (j+1) (by omega) hjn).trans (le_add_of_nonneg_right hMg)
      · have he : j+1=n+1 := by omega
        rw [he]
        exact le_add_of_nonneg_left hA0
    · intro j hj hj'
      exact (hfl j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  have hh := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    ((hg.fderiv_right (m:=∞) (by simp)).comp hf) (hf.fderiv_right (m:=∞) (by simp)) x (n:=n) (by exact_mod_cast le_top)
    (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hterm (i : ℕ) (hi : i∈Finset.range (n+1)) :
      (n.choose i : ℝ)*‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖*
        ‖iteratedFDeriv ℝ (n-i) (fderiv ℝ f) x‖  ≤
      c i*(A+Mg)+(if i=0 then A*Mf else 0) := by
    have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
    rw [norm_iteratedFDeriv_fderiv]
    by_cases hi0 : i=0
    · subst i
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,Function.comp_apply,
        Nat.sub_zero,ite_true]
      have hg1 : ‖fderiv ℝ g (f x)‖ ≤ A := by simpa only [norm_iteratedFDeriv_one] using hgl 1 le_rfl hn
      exact (mul_le_mul_of_nonneg_right hg1 hMf).trans (le_add_of_nonneg_left (mul_nonneg (hcn 0) (add_nonneg hA0 hMg)))
    · rw [ite_eq_right hi0,add_zero]
      have hlow := hfl (n-i+1) (by omega) (by omega)
      calc
        _  ≤  (n.choose i : ℝ)*(i.factorial*(A+Mg)*A^i)*A := by
          gcongr
          exact hcomp i hi'
        _ = c i*(A+Mg) := by dsimp [c]; rw [pow_succ]; ring
  rw [← norm_iteratedFDeriv_fderiv,hfg]
  refine hh.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<n+1 by omega,ite_true]
  change S*(A+Mg)+A*Mf ≤ (A+S*(A+1))*(1+Mg+Mf)
  nlinarith [mul_nonneg hS hMg,mul_nonneg hS hMf,mul_nonneg (mul_nonneg hS hA0) hMg,
    mul_nonneg (mul_nonneg hS hA0) hMf,mul_nonneg hA0 hMg]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {U V W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma norm_iteratedFDeriv_precomp_contraction (f : V → W) (hf : ContDiff ℝ ∞ f)
    (L : U →L[ℝ] V) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le _).trans (by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)).trans_eq (mul_one _))

lemma norm_iteratedFDeriv_pair_le {f : U → V} {g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) {C : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hc : ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun z => (f z,g z)) x‖ ≤ C := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by exact_mod_cast le_top)]
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg _).trans hb)
  intro m
  rw [ContinuousMultilinearMap.prod_apply,Prod.norm_mk]
  exact max_le ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
    ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun _ _ => norm_nonneg _)))

lemma bounded_derivatives_comp_on_compact {g : V → W} (hg : ContDiff ℝ ∞ g) {K : Set V}
    (hK : IsCompact K) (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : U → V), ContDiff ℝ ∞ f → ∀ x, f x∈K →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A) →
      ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i (g ∘ f) x‖ ≤ C := by
  have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.image (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))).isBounded.exists_norm_le
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let D := ∑ i, B i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hB i)
  have hiD (i : Fin (n+1)) : B i ≤ D := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  let c : Fin (n+1) → ℝ := fun i => i.val.factorial*D*A^i.val
  have hc (i : Fin (n+1)) : 0 ≤ c i := by dsimp [c]; positivity
  refine ⟨∑ i, c i,Finset.sum_nonneg (fun i _ => hc i),?_⟩
  intro f hf x hx hlow i hi
  have hcomp : ‖iteratedFDeriv ℝ i (g ∘ f) x‖ ≤ i.factorial*D*A^i := by
    apply norm_iteratedFDeriv_comp_le hg hf (by exact_mod_cast le_top)
    · intro j hj
      exact (hbound ⟨j,by omega⟩ _ hx).trans (hiD _)
    · intro j hj hj'
      exact (hlow j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  exact hcomp.trans (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1))))

lemma tame_comp_on_compact {g : V → W} (hg : ContDiff ℝ ∞ g) {K : Set V}
    (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : U → V), ContDiff ℝ ∞ f → ∀ x, f x∈K →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A) →
      ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤ C*(1+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  have hb (i : Fin (n+2)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.image (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))).isBounded.exists_norm_le
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let D : ℝ := A+∑ i, B i
  have hAD : A ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hD : 1 ≤ D := hA.trans hAD
  have hBD (i : Fin (n+2)) : B i ≤ D :=
    (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hA))
  obtain ⟨C,hC,hcomp⟩ := tame_iteratedFDeriv_comp (E:=U) (F:=V) (G:=W) n hn D hD
  refine ⟨C*(1+D),mul_nonneg hC (by linarith),?_⟩
  intro f hf x hx hlow
  have hh := hcomp g f hg hf x
    (fun i hi hi' => (hbound ⟨i,by omega⟩ _ hx).trans (hBD _))
    (fun i hi hi' => (hlow i hi hi').trans hAD)
  have ht := (hbound ⟨n+1,by omega⟩ _ hx).trans (hBD _)
  refine hh.trans (mul_le_mul_of_nonneg_left (by gcongr) hC |>.trans ?_)
  have hd := mul_nonneg (show 0 ≤ D by linarith) (norm_nonneg (iteratedFDeriv ℝ (n+1) f x))
  nlinarith

end RVM

end

end OAI
