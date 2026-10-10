import OAI.NumberTheory.CubicMoment.Estimates.PrimeBins

namespace OAI

/-! The first-bin identity with the actual selected divisor and its
complement. The crossing test only sees the selected divisor, while
inverse-binomial weighting restores every original squarefree term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stopping_bin_scalar_norm_le_one {N k : ℕ} (hk : k ≤ N) :
    ‖(N.choose k:ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv,Complex.norm_natCast]
  apply inv_le_one_of_one_le₀
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.choose_pos hk))

def stoppingSelected (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (j : ℕ) (t : Finset Eisenstein) : Finset Eisenstein :=
  primeBinPrefix s b j ∪ t

def stoppingRemainder (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (j : ℕ) (t : Finset Eisenstein) : Finset Eisenstein :=
  s \ stoppingSelected s b j t

lemma stoppingSelected_subset {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    stoppingSelected s b j t ⊆ s := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (Finset.mem_filter.mp hp).1
  · exact (Finset.mem_filter.mp (ht hp)).1

lemma stoppingSelected_surrogate {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    (ell : ℕ → ℝ) {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    primeSurrogate (stoppingSelected s b j t) b ell =
      primeSurrogate (primeBinPrefix s b j) b ell * ell j^t.card := by
  have hd : Disjoint (primeBinPrefix s b j) t :=
    (primeBinPrefix_disjoint s b j).mono_right ht
  rw [stoppingSelected,primeSurrogate,Finset.prod_union hd]
  congr 1
  calc
    _ = ∏ _p ∈ t, ell j := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp (ht hp)).2]
    _ = _ := Finset.prod_const _

lemma stoppingSelected_bin_count {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    (stoppingSelected s b j t).filter (fun p => b p = j) = t := by
  ext p
  by_cases hp : p ∈ t
  · have he := (Finset.mem_filter.mp (ht hp)).2
    simp [stoppingSelected,hp,he]
  · simp only [Finset.mem_filter,stoppingSelected,Finset.mem_union,
      primeBinPrefix,Finset.mem_filter,hp,or_false]
    constructor
    · rintro ⟨⟨_,hbp⟩,he⟩
      omega
    · intro h
      exact h.elim

lemma stoppingRemainder_bin_count {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (_ht : t ⊆ primeBin s b j) :
    (stoppingRemainder s b j t).filter (fun p => b p = j) = primeBin s b j \ t := by
  ext p
  simp only [stoppingRemainder,stoppingSelected,primeBinPrefix,primeBin,
    Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨⟨hp,hn⟩,he⟩
    exact ⟨⟨hp,he⟩,fun h => hn (Or.inr h)⟩
  · rintro ⟨⟨hp,he⟩,hnt⟩
    refine ⟨⟨hp,?_⟩,he⟩
    rintro (⟨_,hlt⟩ | hpt)
    · omega
    · exact hnt hpt

lemma stoppingSelected_bins_le {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j)
    {p : Eisenstein} (hp : p ∈ stoppingSelected s b j t) : b p ≤ j := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (Finset.mem_filter.mp hp).2.le
  · exact (Finset.mem_filter.mp (ht hp)).2.le

lemma stoppingRemainder_bins_ge {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j : ℕ} {t : Finset Eisenstein} {p : Eisenstein}
    (hp : p ∈ stoppingRemainder s b j t) : j ≤ b p := by
  obtain ⟨hpS,hpout⟩ := Finset.mem_sdiff.mp hp
  by_contra h
  apply hpout
  apply Finset.mem_union_left
  exact Finset.mem_filter.mpr ⟨hpS,by omega⟩

/-- The failed first-stage test can be read entirely from the selected
side at a later stopping bin. This is the extra ordinary-block predicate. -/
lemma stoppingSelected_earlier_prefix {s : Finset Eisenstein} {b : Eisenstein → ℕ}
    {j h : ℕ} (hhj : h ≤ j) {t : Finset Eisenstein} (ht : t ⊆ primeBin s b j) :
    (stoppingSelected s b j t).filter (fun p => b p < h) = primeBinPrefix s b h := by
  ext p
  constructor
  · intro hp
    obtain ⟨hps,hph⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨stoppingSelected_subset ht hps,hph⟩
  · intro hp
    obtain ⟨hpS,hph⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS,?_⟩),hph⟩
    exact hph.trans_le hhj

lemma cutoffMoebius_stoppingSelected (ψ : ℝ → ℝ) (w : ℝ)
    {s : Finset Eisenstein} (hs : ∀ p ∈ s, primaryPrime p)
    {b : Eisenstein → ℕ} {j : ℕ} {t : Finset Eisenstein}
    (ht : t ⊆ primeBin s b j) :
    cutoffMoebius ψ w (∏ p ∈ stoppingSelected s b j t, p) *
      cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s b j t, p) =
        cutoffMoebius ψ w (∏ p ∈ s, p) := by
  have hsel := stoppingSelected_subset ht
  unfold stoppingRemainder
  rw [cutoffMoebius_prime_product ψ w _ (fun p hp => hs p (hsel hp)),
    cutoffMoebius_prime_product ψ w _ (fun p hp => hs p (Finset.mem_sdiff.mp hp).1),
    cutoffMoebius_prime_product ψ w s hs]
  exact stopping_coefficient_split s (stoppingSelected s b j t) hsel _

/-- One original term is exactly the sum over all selections at its
first stopping bin. All crossing predicates lie on the selected side. -/
theorem prime_bin_stopping_identity (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) (b : Eisenstein → ℕ) (ell : ℕ → ℝ)
    {m : ℕ} (hb : ∀ p ∈ s, b p < m) (hell : ∀ j < m, 1 < ell j)
    {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s b ell) (ψ : ℝ → ℝ) (w : ℝ) :
    ∃ j < m, ∃ k : ℕ, 1 ≤ k ∧ k ≤ (primeBin s b j).card ∧
      (∑ t ∈ (primeBin s b j).powersetCard k,
        if R*primeSurrogate (stoppingSelected s b j t) b ell/ell j < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected s b j t) b ell then
          ((primeBin s b j).card.choose k:ℂ)⁻¹ *
            (cutoffMoebius ψ w (∏ p ∈ stoppingSelected s b j t, p) *
             cutoffMoebius ψ w (∏ p ∈ stoppingRemainder s b j t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  obtain ⟨j,hjm,k,hk,hks,hprev,hhit⟩ := first_prime_bin s b ell hb hell hR hstart hend
  refine ⟨j,hjm,k,hk,hks,?_⟩
  calc
    _ = ∑ _t ∈ (primeBin s b j).powersetCard k,
        ((primeBin s b j).card.choose k:ℂ)⁻¹*cutoffMoebius ψ w (∏ p ∈ s, p) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hsub := (Finset.mem_powersetCard.mp ht).1
      have hcard := (Finset.mem_powersetCard.mp ht).2
      have hc : R*primeSurrogate (stoppingSelected s b j t) b ell/ell j < Z ∧
          Z ≤ R*primeSurrogate (stoppingSelected s b j t) b ell := by
        rw [stoppingSelected_surrogate ell hsub,hcard,←mul_assoc]
        exact ⟨hprev,hhit⟩
      rw [ite_eq_left hc,cutoffMoebius_stoppingSelected ψ w hs hsub]
    _ = _ := by
      rw [← Finset.sum_mul,stopping_bin_weights_sum (primeBin s b j) k hks,one_mul]

end CubicFirstMoment

end

end OAI
