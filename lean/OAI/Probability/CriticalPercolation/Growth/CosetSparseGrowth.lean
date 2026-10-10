import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.NormalClosureGrowth

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

def ball (K : Subgroup A) (S : Set A) (n : ℕ) : Set (A ⧸ K) :=
  (QuotientGroup.mk : A → A ⧸ K) '' S^n

def HasDegree (K : Subgroup A) (S : Set A) (d : ℕ) : Prop :=
  (∀ n, (ball K S n).Finite) ∧ ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (ball K S n).ncard≤C*n^d

lemma ball_mono (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S) :
    Monotone (ball K S) := fun _ _ h => Set.image_mono (Set.pow_subset_pow_right h1 h)

lemma not_quadratic_exponential_lower (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree K S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (ball K S (L*n^2)).ncard) : False := by
  obtain ⟨hfin,C,hC⟩ := hg
  obtain ⟨N,hN⟩ := SparseGrowth.eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (ball K S (L*n^2)).ncard := hlo n
      _ ≤ (ball K S r).ncard := Set.ncard_le_ncard (ball_mono K S h1 hnr) (hfin r)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma binaryProducts_coset_inj (K : Subgroup A) (H : ℕ → Subgroup A) (hH : Monotone H)
    (hK : K≤H 0) (g : ℕ → A) (hg : ∀ n, g n∈H (n+1)) (hout : ∀ n, g n∉H n) :
    ∀ n, Set.InjOn (QuotientGroup.mk : A → A ⧸ K) (SparseGrowth.binaryProducts g n : Set A) := by
  intro n
  induction n with
  | zero => simp [SparseGrowth.binaryProducts,Set.InjOn]
  | succ n ih =>
    intro x hx y hy he
    have hKn : K≤H n := hK.trans (hH (Nat.zero_le n))
    have hmem := SparseGrowth.binaryProducts_mem H hH g hg n
    have hbad (x y : A) (hx : x∈SparseGrowth.binaryProducts g n)
        (hy : y∈SparseGrowth.binaryProducts g n)
        (he : (QuotientGroup.mk x : A ⧸ K)=QuotientGroup.mk (g n*y)) : False := by
      have hxy : x⁻¹*(g n*y)∈H n := hKn (QuotientGroup.eq.mp he)
      have hz := (H n).mul_mem ((H n).mul_mem (hmem x hx) hxy) ((H n).inv_mem (hmem y hy))
      apply hout n
      simpa only [mul_inv_cancel_left,mul_assoc,mul_inv_cancel,mul_one] using hz
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · exact ih hx hy he
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      exact False.elim (hbad x z hx hz he)
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact False.elim (hbad y z hy hz he.symm)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      apply congrArg (fun t => g n*t)
      apply ih ha hb
      apply QuotientGroup.eq.mpr
      have hh := QuotientGroup.eq.mp he
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hh

lemma binaryProducts_subset_pow (S : Set A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, (SparseGrowth.binaryProducts g n : Set A) ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [SparseGrowth.binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Set.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Set.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Set.mul_mem_mul (hg n) (ih hy)

lemma no_linear_strict_chain (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree K S d) (H : ℕ → Subgroup A) (hH : Monotone H) (hK : K≤H 0)
    (g : ℕ → A) (hgin : ∀ n, g n∈H (n+1)) (hgout : ∀ n, g n∉H n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower K S h1 d hg L hL
  intro n
  have hin := binaryProducts_coset_inj K H hH hK g hgin hgout n
  rw [←SparseGrowth.binaryProducts_card H hH g hgin hgout n]
  have heq := hin.ncard_image
  rw [Set.ncard_coe_finset] at heq
  rw [←heq]
  exact Set.ncard_le_ncard (Set.image_mono (binaryProducts_subset_pow S h1 g L hword n)) (hg.1 _)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
