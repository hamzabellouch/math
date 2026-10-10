import OAI.Geometry.NodalSets.Elliptic.RealJetErrorExpansion

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

lemma real_list_sum_square_bound {α : Type*} (ts : List α) (f : α → ℝ) (D : ℝ)
    (hf : ∀ t ∈ ts, (f t)^2 ≤ D) :
    (ts.map f).sum^2 ≤ (ts.length:ℝ)^2*D := by
  have hs : (ts.map f).sum = ∑ i : Fin ts.length, f (ts.get i) := by
    conv_lhs => rw [← List.ofFn_get ts]
    simp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _i : Fin ts.length ↦ (1:ℝ)) (fun i ↦ f (ts.get i))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one] at hc
  have he : (∑ i : Fin ts.length, (f (ts.get i))^2) ≤ (ts.length:ℝ)*D := by
    calc
      _ ≤ ∑ _i : Fin ts.length, D := Finset.sum_le_sum (fun i _ ↦ hf _ (List.get_mem ..))
      _ = _ := by simp
  rw [hs]
  calc
    _ ≤ (ts.length:ℝ)*(∑ i : Fin ts.length, (f (ts.get i))^2) := hc
    _ ≤ (ts.length:ℝ)*((ts.length:ℝ)*D) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by ring

lemma realJetProductSum_square_bound (a W : Yau.Jets.Coord → ℝ)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (extra ds : List (Fin 4))
    (he : extra.length ≤ 1) (hd : ds.length ≤ n) (x : Yau.Jets.Coord)
    (ha : ∀ es : List (Fin 4), es.length ≤ n → |partialJet a es x| ≤ B) :
    (realJetProductSum a W (realJetErrorTerms extra ds) x)^2 ≤
      (3:ℝ)^(2*n)*B^2*realFiniteJetSquare W n x := by
  have hterm (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ realJetErrorTerms extra ds) :
      (partialJet a t.1 x*partialJet W t.2 x)^2 ≤ B^2*realFiniteJetSquare W n x := by
    obtain ⟨haord,hword⟩ := realJetErrorTerms_orders extra ds he t ht
    have hca : (partialJet a t.1 x)^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (ha t.1 (haord.trans hd))
    rw [mul_pow]
    exact mul_le_mul hca (partialJet_sq_le_realFiniteJetSquare W n t.2 (hword.trans hd) x)
      (sq_nonneg _) (sq_nonneg _)
  have hcount : ((realJetErrorTerms extra ds).length:ℝ) ≤ (3:ℝ)^n := by
    have hc : ((realJetErrorTerms extra ds).length:ℝ) ≤ (3:ℝ)^ds.length := by
      exact_mod_cast realJetErrorTerms_length extra ds
    exact hc.trans (by gcongr; norm_num)
  have hsq : ((realJetErrorTerms extra ds).length:ℝ)^2 ≤ (3:ℝ)^(2*n) := by
    calc
      _ ≤ ((3:ℝ)^n)^2 := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; omega
  exact (real_list_sum_square_bound (realJetErrorTerms extra ds)
    (fun t ↦ partialJet a t.1 x*partialJet W t.2 x)
    (B^2*realFiniteJetSquare W n x) hterm).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsq
        (mul_nonneg (sq_nonneg B) (realFiniteJetSquare_nonneg W n x)))

theorem real_jet_error_bound (n : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      ∀ (x : Yau.Jets.Coord) (ds : List (Fin 4)), ds.length ≤ n →
      (∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (realJetErrorSource V W ds x)^2 + (∑ i, (realJetErrorFlux C W ds x i)^2) ≤
        K*realFiniteJetSquare W n x := by
  refine ⟨65*(3:ℝ)^(2*n)*B^2+1,by positivity,?_⟩
  intro C V W hC hV hW x ds hd hb
  let D := (3:ℝ)^(2*n)*B^2*realFiniteJetSquare W n x
  have hs : (realJetErrorSource V W ds x)^2 ≤ D := by
    rw [realJetErrorSource_expansion V W hV hW]
    simpa only [neg_sq] using realJetProductSum_square_bound V W n B hB [] ds
      (by simp) hd x (fun es hes ↦ (hb es hes).2)
  have hr (i : Fin 4) : (realJetErrorFlux C W ds x i)^2 ≤ 16*D := by
    rw [realJetErrorFlux_expansion C W hC hW]
    simp only [neg_sq]
    have ht (j : Fin 4) :
        (realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x)^2 ≤ D :=
      realJetProductSum_square_bound _ W n B hB [j] ds (by simp) hd x
        (fun es hes ↦ (hb es hes).1 i j)
    have hh := real_list_sum_square_bound (List.ofFn (fun j : Fin 4 ↦ j))
      (fun j ↦ realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x)
      D (fun j _ ↦ ht j)
    simpa only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_apply,
      Nat.cast_ofNat,show (4:ℝ)^2=16 from by norm_num] using hh
  have hf : (∑ i, (realJetErrorFlux C W ds x i)^2) ≤ 64*D := by
    calc
      _ ≤ ∑ _i : Fin 4, 16*D := Finset.sum_le_sum (fun i _ ↦ hr i)
      _ = _ := by simp; ring
  have hS := realFiniteJetSquare_nonneg W n x
  dsimp [D] at hs hf
  nlinarith only [hs,hf,hS]

end
end Yau.Geometry

end OAI
