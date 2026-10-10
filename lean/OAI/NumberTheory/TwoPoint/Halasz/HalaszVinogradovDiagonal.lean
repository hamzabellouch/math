import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open Finset MvPolynomial

theorem halasz_vinogradov_esymm {s : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∑ i, x i^j = ∑ i, y i^j) :
    ∀ k : ℕ, k ≤ s →
      eval x (esymm (Fin s) ℚ k) = eval y (esymm (Fin s) ℚ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hks
    by_cases hk : k=0
    · subst k
      simp
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have he (a : ℕ × ℕ) (ha : a ∈ (antidiagonal k).filter (fun a => a.1<k)) :
        eval x ((-1: MvPolynomial (Fin s) ℚ)^a.1 * esymm (Fin s) ℚ a.1 * psum (Fin s) ℚ a.2) =
          eval y ((-1: MvPolynomial (Fin s) ℚ)^a.1 * esymm (Fin s) ℚ a.1 * psum (Fin s) ℚ a.2) := by
      obtain ⟨ha,hak⟩ := mem_filter.mp ha
      have hab : a.1+a.2=k := mem_antidiagonal.mp ha
      have hp := hpower a.2 (by omega) (by omega)
      have hi := ih a.1 hak (by omega)
      simp only [map_mul,map_pow,map_neg,map_one]
      rw [hi]
      have heval : eval x (psum (Fin s) ℚ a.2) = eval y (psum (Fin s) ℚ a.2) := by
        simpa [psum] using hp
      rw [heval]
    have hsum := sum_congr rfl he
    have hx := congrArg (eval x) (mul_esymm_eq_sum (Fin s) ℚ k)
    have hy := congrArg (eval y) (mul_esymm_eq_sum (Fin s) ℚ k)
    simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hx hy
    have heq : (k:ℚ)*eval x (esymm (Fin s) ℚ k) =
        (k:ℚ)*eval y (esymm (Fin s) ℚ k) := by
      rw [hx,hy]
      simpa only [map_mul,map_pow,map_neg,map_one] using
        congrArg (fun z : ℚ => (-1:ℚ)^(k+1)*z) hsum
    exact mul_left_cancel₀ (by exact_mod_cast hk : (k:ℚ)≠0) heq

/-- The complete diagonal system determines the multiset of its variables. -/
theorem halasz_vinogradov_multiset {s : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∑ i, x i^j = ∑ i, y i^j) :
    (univ.val.map x) = (univ.val.map y) := by
  let a : Multiset ℚ := univ.val.map x
  let b : Multiset ℚ := univ.val.map y
  have ha : a.card=s := by simp [a]
  have hb : b.card=s := by simp [b]
  have he : ∀ k : ℕ, a.esymm k=b.esymm k := by
    intro k
    by_cases hk : k ≤ s
    · have hx := aeval_esymm_eq_multiset_esymm (Fin s) ℚ k x
      have hy := aeval_esymm_eq_multiset_esymm (Fin s) ℚ k y
      rw [aeval_eq_eval] at hx hy
      exact hx.symm.trans ((halasz_vinogradov_esymm x y hpower k hk).trans hy)
    · rw [Multiset.esymm_of_card_lt (by omega : a.card<k),
        Multiset.esymm_of_card_lt (by omega : b.card<k)]
  have hprod : (a.map (fun t => Polynomial.X-Polynomial.C t)).prod =
      (b.map (fun t => Polynomial.X-Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,ha,hb]
    apply sum_congr rfl
    intro k _
    rw [he k]
  have hr := congrArg Polynomial.roots hprod
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hr

noncomputable def halaszVinogradovFiber {s N : ℕ} (x : Fin s → Fin N) (k : ℕ) :
    Finset (Fin s → Fin N) := by
  classical
  exact univ.filter (fun y => ∀ j ∈ Icc 1 k,
    (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j)

@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]

lemma halasz_vinogradov_fiber_perm {s N k : ℕ} (hsk : s ≤ k)
    (x y : Fin s → Fin N) (hy : y ∈ halaszVinogradovFiber x k) :
    (List.ofFn y).Perm (List.ofFn x) := by
  classical
  have hp := mem_halaszVinogradovFiber.mp hy
  let v : Fin N → ℚ := fun a => (a.val:ℚ)+1
  have hv : Function.Injective v := by
    intro a b hab
    have he : (a.val:ℚ)=(b.val:ℚ) := add_right_cancel hab
    exact Fin.ext (by exact_mod_cast he)
  have hq : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      (∑ i, v (y i)^j) = ∑ i, v (x i)^j := by
    intro j hj hjs
    have hh := (hp j (mem_Icc.mpr ⟨hj,hjs.trans hsk⟩)).symm
    dsimp only [v]
    exact_mod_cast hh
  have hm := halasz_vinogradov_multiset (fun i => v (y i)) (fun i => v (x i)) hq
  have hu : (univ:Finset (Fin s)).val=(List.finRange s:Multiset (Fin s)) := by
    apply Multiset.ext.mpr
    intro i
    simp
  apply Multiset.coe_eq_coe.mp
  rw [List.ofFn_eq_map,List.ofFn_eq_map,← Multiset.map_coe,← Multiset.map_coe,← hu]
  apply Multiset.map_injective hv
  simpa only [Multiset.map_map,Function.comp_def] using hm

theorem halasz_vinogradov_fiber_card {s N k : ℕ} (hsk : s ≤ k)
    (x : Fin s → Fin N) : (halaszVinogradovFiber x k).card ≤ s.factorial := by
  classical
  let A := halaszVinogradovFiber x k
  have hinj : Function.Injective (List.ofFn : (Fin s → Fin N) → List (Fin N)) :=
    List.ofFn_injective
  have hsub : A.image List.ofFn ⊆ (List.ofFn x).permutations.toFinset := by
    intro l hl
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hl
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr
      (halasz_vinogradov_fiber_perm hsk x y hy))
  calc
    A.card = (A.image List.ofFn).card := (card_image_of_injective A hinj).symm
    _ ≤ ((List.ofFn x).permutations.toFinset).card := card_le_card hsub
    _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
    _ = s.factorial := by rw [List.length_permutations,List.length_ofFn]

noncomputable def halaszVinogradovCount (s k N : ℕ) : ℕ :=
  ∑ x : Fin s → Fin N, (halaszVinogradovFiber x k).card

/-- The diagonal-range upper bound for the complete Vinogradov system. -/
theorem halasz_vinogradov_diagonal_bound {s k N : ℕ} (hsk : s ≤ k) :
    halaszVinogradovCount s k N ≤ N^s*s.factorial := by
  unfold halaszVinogradovCount
  calc
    _ ≤ ∑ _x : Fin s → Fin N, s.factorial :=
      sum_le_sum (fun x _ => halasz_vinogradov_fiber_card hsk x)
    _ = _ := by simp

lemma halasz_vinogradov_count_lower (s k N : ℕ) : N^s ≤ halaszVinogradovCount s k N := by
  classical
  have hx (x : Fin s → Fin N) : 1 ≤ (halaszVinogradovFiber x k).card := by
    apply card_pos.mpr
    refine ⟨x,?_⟩
    simp [halaszVinogradovFiber]
  unfold halaszVinogradovCount
  calc
    _ = ∑ _x : Fin s → Fin N, 1 := by simp
    _ ≤ _ := sum_le_sum (fun x _ => hx x)

lemma halasz_vinogradov_count_antitone (s N : ℕ) :
    Antitone (fun k => halaszVinogradovCount s k N) := by
  classical
  intro k l hkl
  unfold halaszVinogradovCount
  apply sum_le_sum
  intro x _
  apply card_le_card
  intro y hy
  apply mem_halaszVinogradovFiber.mpr
  intro j hj
  exact (mem_halaszVinogradovFiber.mp hy) j (mem_Icc.mpr
    ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans hkl⟩)

end TwoPointCorrelations

end OAI
