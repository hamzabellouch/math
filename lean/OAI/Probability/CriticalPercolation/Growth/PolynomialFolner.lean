import Mathlib
import OAI.Probability.CriticalPercolation.Growth.PolynomialGrowthDescent
import OAI.Probability.CriticalPercolation.Growth.RealSparseDoubling

namespace OAI

section
noncomputable section
open Set Function Finset
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis

lemma sparse_small_increment (f : ℕ → ℝ) (hf : Monotone f)
    (hp : ∀ n, 0<f n) (C : ℝ) (hC : 0≤C) (d : ℕ)
    (hg : ∀ R, ∃ n≥R, f n≤C*(n:ℝ)^d)
    (ε : ℝ) (hε : 0<ε) (R : ℕ) :
    ∃ n≥R, f (n+1)-f n≤ε*f n := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)^(d+1)/ε)
  obtain ⟨r,hr,hgood⟩ := sparse_real_doubling f hf 0 (fun n _ => hp n)
    C hC d 2 (by omega) hg (max R N)
  have hR : R≤r := by omega
  have hlarge : (2:ℝ)^(d+1)<(r:ℝ)*ε := by
    have hn : (N:ℝ)≤r := by exact_mod_cast (show N≤r by omega)
    have he := (div_lt_iff₀ hε).mp hN
    nlinarith
  by_contra! hbad
  have ht : ∀ i≤r, (i:ℝ)*ε*f r≤f (r+i)-f r := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have h := ih (by omega)
      have hh := (hbad (r+i) (by omega)).le
      have hm := hf (show r≤r+i by omega)
      have him := mul_le_mul_of_nonneg_left hm hε.le
      push_cast
      have he : r+(i+1)=r+i+1 := by omega
      rw [he]
      nlinarith
  have h := ht r le_rfl
  rw [←two_mul] at h
  have hh := mul_lt_mul_of_pos_right hlarge (hp r)
  norm_num only [Nat.cast_ofNat] at hgood
  nlinarith [hp r]

lemma sum_sub_sum_bound_common_superset {A : Type*} (T U V : Finset A)
    (hUT : U⊆T) (hVT : V⊆T) (hcard : U.card=V.card)
    (f : A → ℝ) (M : ℝ) (hM : 0≤M) (hb : ∀ x∈T, |f x|≤M) :
    |(∑ x∈U, f x)-(∑ x∈V, f x)|≤2*((T.card:ℝ)-U.card)*M := by
  have hu : (∑ x∈U, f x)+(∑ x∈T\U, f x)=∑ x∈T, f x :=
    by rw [Finset.sum_sdiff_eq_sub hUT]; ring
  have hv : (∑ x∈V, f x)+(∑ x∈T\V, f x)=∑ x∈T, f x :=
    by rw [Finset.sum_sdiff_eq_sub hVT]; ring
  have hs (W : Finset A) (hWT : W⊆T) : |∑ x∈T\W, f x|≤((T.card:ℝ)-W.card)*M := by
    calc
      _ ≤ ∑ x∈T\W, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x∈T\W, M := Finset.sum_le_sum (fun x hx => hb x (Finset.mem_sdiff.mp hx).1)
      _ = _ := by
        rw [Finset.sum_const,Finset.card_sdiff_of_subset hWT,nsmul_eq_mul,Nat.cast_sub (Finset.card_le_card hWT)]
  have he : (∑ x∈U, f x)-(∑ x∈V, f x)=(∑ x∈T\V, f x)-(∑ x∈T\U, f x) := by linarith
  rw [he]
  apply (abs_sub _ _).trans
  calc
    _ ≤ (((T.card:ℝ)-V.card)+((T.card:ℝ)-U.card))*M := by
      linarith [hs V hVT, hs U hUT]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [←hcard]; linarith) hM

end CriticalPercolation.HarmonicAnalysis
namespace CriticalPercolation.SparseGrowth
variable {G : Type*} [Group G] [DecidableEq G]

lemma small_ball_increment (S : Finset G) (h1 : (1:G)∈S) (d : ℕ)
    (hg : HasDegree S d) (ε : ℝ) (hε : 0<ε) (R : ℕ) :
    ∃ n≥R, ((S^(n+1)).card:ℝ)-(S^n).card≤ε*(S^n).card := by
  obtain ⟨C,hC⟩ := hg
  apply HarmonicAnalysis.sparse_small_increment (fun n => ((S^n).card:ℝ))
    (fun i j hij => by dsimp; exact_mod_cast Finset.card_le_card (Finset.pow_subset_pow_right h1 hij))
    (fun n => by exact_mod_cast Finset.card_pos.mpr ⟨1,Finset.one_mem_pow h1⟩)
    C (Nat.cast_nonneg C) d ?_ ε hε R
  intro T
  obtain ⟨n,hn,hb⟩ := hC T
  exact ⟨n,hn,by exact_mod_cast hb⟩

lemma translated_ball_sum_bound (S : Finset G) (h1 : (1:G)∈S)
    (n : ℕ) (s : G) (hs : s∈S) (f : G → ℝ) (M : ℝ)
    (hM : 0≤M) (hb : ∀ x, |f x|≤M) :
    |(∑ x∈S^n, f (s*x))-(∑ x∈S^n, f x)|≤
      2*(((S^(n+1)).card:ℝ)-(S^n).card)*M := by
  have hT : (S^n).image (fun x => s*x)⊆S^(n+1) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [pow_succ']
    exact Finset.mul_mem_mul hs ha
  have hU : S^n⊆S^(n+1) := Finset.pow_subset_pow_right h1 (Nat.le_succ n)
  have he : ((S^n).image (fun x => s*x)).card=(S^n).card :=
    Finset.card_image_of_injective _ (mul_right_injective s)
  have H := HarmonicAnalysis.sum_sub_sum_bound_common_superset
    (S^(n+1)) ((S^n).image (fun x => s*x)) (S^n) hT hU he f M hM (fun x _ => hb x)
  rw [he,Finset.sum_image (fun x _ y _ h => mul_left_cancel h)] at H
  exact H

end CriticalPercolation.SparseGrowth
end
end

end OAI
