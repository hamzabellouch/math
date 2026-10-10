import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicConjugateGeneration

namespace OAI

/-! # The actual kernel of an infinite cyclic quotient is finitely generated

Schreier corrections of the given generators, and all their cyclic
conjugates, generate the kernel. Polynomial growth makes this a finite window.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem cyclicConjugateSubgroup_conjugation (t : G) (R : Finset G) (j : ℤ)
    {x : G} (hx : x ∈ cyclicConjugateSubgroup t R) :
    t ^ j * x * t ^ (-j) ∈ cyclicConjugateSubgroup t R := by
  let f := (MulAut.conj (t ^ j)).toMonoidHom
  have hle : cyclicConjugateSubgroup t R ≤ (cyclicConjugateSubgroup t R).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨k, r, hr, rfl⟩
    change t ^ j * (t ^ k * r * t ^ (-k)) * (t ^ j)⁻¹ ∈ cyclicConjugateSubgroup t R
    rw [← zpow_neg, cyclic_conjugation_add]
    exact Subgroup.subset_closure ⟨j + k, r, hr, rfl⟩
  have hh := hle hx
  change t ^ j * x * (t ^ j)⁻¹ ∈ cyclicConjugateSubgroup t R at hh
  simpa only [← zpow_neg] using hh

def cyclicSchreierLetter (q : G →* Multiplicative ℤ) (t s : G) : G :=
  s * t ^ (-(q s).toAdd)

omit [DecidableEq G] in
theorem cyclicHeight_zpow (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) (n : ℤ) : q (t ^ n) = Multiplicative.ofAdd n := by
  rw [map_zpow, ht]
  apply Multiplicative.ext
  change n • (1 : ℤ) = n
  simp

omit [DecidableEq G] in
theorem cyclicSchreierLetter_mem_ker (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) (s : G) : cyclicSchreierLetter q t s ∈ q.ker := by
  change q (s * t ^ (-(q s).toAdd)) = 1
  rw [map_mul, cyclicHeight_zpow q t ht]
  apply Multiplicative.ext
  change (q s).toAdd + -(q s).toAdd = 0
  simp

theorem cyclicSchreierKernel_eq (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤) :
    cyclicConjugateSubgroup t (S.image (cyclicSchreierLetter q t)) = q.ker := by
  let K := cyclicConjugateSubgroup t (S.image (cyclicSchreierLetter q t))
  have hK : K ≤ q.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, r, hr, rfl⟩
    obtain ⟨s, _, rfl⟩ := mem_image.mp hr
    change q (t ^ j * cyclicSchreierLetter q t s * t ^ (-j)) = 1
    rw [map_mul, map_mul, cyclicSchreierLetter_mem_ker q t ht s,
      cyclicHeight_zpow q t ht, cyclicHeight_zpow q t ht]
    apply Multiplicative.ext
    change j + 0 + -j = 0
    omega
  have hR (s : G) (hs : s ∈ S) : cyclicSchreierLetter q t s ∈ K := by
    have hr : cyclicSchreierLetter q t s ∈ S.image (cyclicSchreierLetter q t) :=
      mem_image.mpr ⟨s, hs, rfl⟩
    exact Subgroup.subset_closure ⟨0, cyclicSchreierLetter q t s, hr, by simp⟩
  have hform (g : G) : ∃ k ∈ K, ∃ n : ℤ, g = k * t ^ n := by
    have hg : g ∈ Subgroup.closure (S : Set G) := hgen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      refine ⟨cyclicSchreierLetter q t s, hR s hs, (q s).toAdd, ?_⟩
      simp [cyclicSchreierLetter, zpow_neg, mul_assoc]
    | one => exact ⟨1, K.one_mem, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk, n, rfl⟩ := hx
      obtain ⟨l, hl, m, rfl⟩ := hy
      refine ⟨k * (t ^ n * l * t ^ (-n)), K.mul_mem hk
        (cyclicConjugateSubgroup_conjugation t _ n hl), n + m, ?_⟩
      simp [zpow_add, zpow_neg, mul_assoc]
    | inv x _ hx =>
      obtain ⟨k, hk, n, rfl⟩ := hx
      refine ⟨t ^ (-n) * k⁻¹ * t ^ n,
        ?_, -n, ?_⟩
      · simpa only [neg_neg] using
          cyclicConjugateSubgroup_conjugation t _ (-n) (K.inv_mem hk)
      · simp [zpow_neg, mul_assoc]
  apply le_antisymm hK
  intro g hg
  obtain ⟨k, hk, n, he⟩ := hform g
  have hn : n = 0 := by
    have hq := congrArg q he
    rw [hg, map_mul, hK hk, one_mul, cyclicHeight_zpow q t ht] at hq
    have h := congrArg Multiplicative.toAdd hq
    simpa using h.symm
  simpa only [he, hn, zpow_zero, mul_one] using hk

theorem cyclic_kernel_fg_of_polynomial_growth
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (q : G →* Multiplicative ℤ) (hq : Function.Surjective q) : q.ker.FG := by
  obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
  rw [← cyclicSchreierKernel_eq q t ht S hgen]
  exact cyclicConjugateSubgroup_fg_of_polynomial_growth S hS hgen hvol t _

end PolycyclicRecognition

end

end OAI
