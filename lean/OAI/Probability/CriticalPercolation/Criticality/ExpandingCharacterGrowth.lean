import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma binaryProducts_map (f : B →* A) (g : ℕ → B) (n : ℕ) :
    (binaryProducts g n).image f = binaryProducts (fun i => f (g i)) n := by
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    simp only [binaryProducts, Finset.image_union]
    rw [←ih]
    congr 1
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact map_mul f (g n) x

lemma binaryProducts_card_norm_bound
    (φ : A →* Multiplicative ℂ) (g : ℕ → A) (b q : ℝ)
    (hb : 0 < b) (hq : 3 ≤ q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖ = b*q^n) :
    ∀ n, (binaryProducts g n).card=2^n ∧
      ∀ a∈binaryProducts g n,
        2*‖Multiplicative.toAdd (φ a)‖ ≤ b*(q^n-1) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [binaryProducts]
    · intro a ha
      have ha1 : a=1 := by simpa [binaryProducts] using ha
      simp [ha1]
  | succ n ih =>
    have hdis : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      obtain ⟨c,hc,hca⟩ := Finset.mem_image.mp ha'
      have heq : Multiplicative.toAdd (φ (g n)) =
          Multiplicative.toAdd (φ a)-Multiplicative.toAdd (φ c) := by
        rw [←hca,map_mul]
        change Multiplicative.toAdd (φ (g n)) =
          (Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c))-
            Multiplicative.toAdd (φ c)
        abel
      have hn := norm_sub_le (Multiplicative.toAdd (φ a)) (Multiplicative.toAdd (φ c))
      rw [←heq,he n] at hn
      have haB := ih.2 a ha
      have hcB := ih.2 c hc
      nlinarith
    constructor
    · simp only [binaryProducts,Finset.card_union_of_disjoint hdis,
        Finset.card_image_of_injective _ (mul_right_injective (g n)),ih.1,pow_succ]
      omega
    · intro a ha
      obtain ha|ha := Finset.mem_union.mp ha
      · have haB := ih.2 a ha
        have hpow : q^n ≤ q^(n+1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by linarith : 0≤q) n]
        exact haB.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hpow 1) hb.le)
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp ha
        have hn := norm_add_le (Multiplicative.toAdd (φ (g n))) (Multiplicative.toAdd (φ c))
        have hcB := ih.2 c hc
        rw [he n] at hn
        rw [map_mul]
        change 2*‖Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c)‖≤_
        rw [pow_succ]
        have hqn : 0≤q^n := pow_nonneg (by linarith) n
        have hprod : 3*(b*q^n) ≤ (b*q^n)*q := by
          calc
            3*(b*q^n) = (b*q^n)*3 := mul_comm _ _
            _ ≤ (b*q^n)*q := mul_le_mul_of_nonneg_left hq (mul_nonneg hb.le hqn)
        nlinarith

theorem no_expanding_short_character (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (f : B →* A) (hf : Injective f)
    (φ : B →* Multiplicative ℂ) (g : ℕ → B) (b q : ℝ)
    (hb : 0<b) (hq : 3≤q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖=b*q^n)
    (L : ℕ) (hL : 0<L) (hw : ∀ n, f (g n)∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  have hc := (binaryProducts_card_norm_bound φ g b q hb hq he n).1
  calc
    2^n = ((binaryProducts g n).image f).card := by
      rw [Finset.card_image_of_injective _ hf,hc]
    _ = (binaryProducts (fun i => f (g i)) n).card := by rw [binaryProducts_map]
    _ ≤ (S^(L*n^2)).card :=
      Finset.card_le_card (binaryProducts_subset_pow S h1 (fun i => f (g i)) L hw n)

theorem HasPolynomialDegree.norm_conj_eigencharacter_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    (a : A) (φ : H →* Multiplicative ℂ) (ζ : ℂ)
    (heigen : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      ζ * Multiplicative.toAdd (φ x))
    (b : H) (hb : Multiplicative.toAdd (φ b) ≠ 0) : ‖ζ‖≤1 := by
  by_contra! hl
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (3:ℝ) hl
  obtain ⟨S,h1,hs,hgen,hgrowth⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen {a,a⁻¹,(b:A)}
  have haL : a∈S^L := hL (by simp)
  have haiL : a⁻¹∈S^L := hL (by simp)
  have hbL : (b:A)∈S^L := hL (by simp)
  have hepow : ∀ m : ℕ, ∀ x : H,
      Multiplicative.toAdd (φ ((MulAut.conjNormal (a^m)) x)) =
        ζ^m * Multiplicative.toAdd (φ x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ',map_mul,MulAut.mul_apply,heigen,ih,pow_succ']
      ring
  let g : ℕ → H := fun n => (MulAut.conjNormal (a^(k*n))) b
  apply no_expanding_short_character S h1 d hgrowth H.subtype H.subtype_injective
    φ g ‖Multiplicative.toAdd (φ b)‖ (‖ζ‖^k) (norm_pos_iff.mpr hb) hk.le
    (fun n => ?_) (2*L*k+L+1) (by omega) (fun n => ?_)
  · dsimp only [g]
    rw [hepow,norm_mul,norm_pow,pow_mul,mul_comm]
  · change ((MulAut.conjNormal (a^(k*n))) b : A)∈_
    rw [MulAut.conjNormal_apply]
    have haP : a^(k*n)∈S^(L*(k*n)) := by
      rw [pow_mul]
      exact Finset.pow_mem_pow haL
    have haiP : (a^(k*n))⁻¹∈S^(L*(k*n)) := by
      rw [←inv_pow,pow_mul]
      exact Finset.pow_mem_pow haiL
    apply Finset.pow_subset_pow_right h1
      (show L*(k*n)+L+L*(k*n)≤(2*L*k+L+1)*(n+1) by nlinarith)
    rw [pow_add,pow_add]
    exact Finset.mul_mem_mul (Finset.mul_mem_mul haP hbL) haiP

end CriticalPercolation.SparseGrowth
end
end

end OAI
