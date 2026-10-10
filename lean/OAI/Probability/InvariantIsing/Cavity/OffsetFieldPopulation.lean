import OAI.Probability.InvariantIsing.Cavity.OffsetFieldPressure
import OAI.Probability.InvariantIsing.Cavity.ConsecutiveGroupProfile

namespace OAI

/-! The zero-field prefix has vanishing population; repeated field blocks
retain the original label proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def offsetSiteGroup {n : ℕ} {A : Type*} (r K : ℕ) (g : Fin n → A) :
    Fin (r+K*n) → Option A :=
  Fin.addCases (fun _ => none) (fun i => some (consecutiveSiteGroup K g i))

lemma offsetSiteGroup_none {n K r : ℕ} {A : Type*} [DecidableEq A] (g : Fin n → A) :
    spinGroupSize (offsetSiteGroup r K g) none=r := by
  simp only [spinGroupSize, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp [offsetSiteGroup]

lemma offsetSiteGroup_some {n K r : ℕ} {A : Type*} [DecidableEq A] (g : Fin n → A) (a : A) :
    spinGroupSize (offsetSiteGroup r K g) (some a)=K*spinGroupSize g a := by
  rw [← consecutiveSiteGroup_size (K := K) g a]
  simp only [spinGroupSize, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp [offsetSiteGroup]

lemma offsetSiteGroup_field {n r K : ℕ} {A : Type*} (g : Fin n → A) (b : A → ℝ) :
    (fun i => Option.elim (offsetSiteGroup r K g i) 0 b)=
      offsetBlockField r K (fun i => b (g i)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [offsetSiteGroup,offsetBlockField,consecutiveSiteGroup,consecutiveBlockField]

lemma offsetSiteGroup_population_tendsto {n : ℕ} (hn : 0<n) (r q : ℕ) (hq : 0<q)
    {A : Type*} [Fintype A] [DecidableEq A] (g : Fin n → A) (γ : A → ℝ)
    (hg : ∀ a, (spinGroupSize g a : ℝ)=n*γ a) :
    Tendsto (fun j a => (spinGroupSize (offsetSiteGroup r (q+j) g) a : ℝ)/(r+(q+j)*n))
      atTop (𝓝 (fun a => Option.elim a 0 γ)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  cases a with
  | none =>
      have hh := cavity_affine_ratio_tendsto 0 r n r q hn hq
      simpa only [offsetSiteGroup_none,Nat.mul_zero,Nat.zero_add,Nat.cast_zero,zero_div,
        Nat.cast_add,Nat.cast_mul,Nat.add_comm,add_comm,add_zero,Option.elim_none] using hh
  | some a =>
      have hh := offset_field_fraction_tendsto hn r q hq (γ a)
      simpa only [offsetSiteGroup_some,Nat.cast_mul,hg,mul_assoc,Option.elim_some] using hh

lemma someSiteGroup_population_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (g : (j : ℕ) → Fin (N j) → A) (γ : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ)) :
    Tendsto (fun j a => (spinGroupSize (fun i => some (g j i)) a : ℝ)/N j)
      atTop (𝓝 (fun a => Option.elim a 0 γ)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  cases a with
  | none =>
      simpa only [spinGroupSize,Option.some_ne_none,Finset.filter_false,Finset.card_empty,
        Nat.cast_zero,zero_div,Option.elim_none] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | some a =>
      simpa only [spinGroupSize,Option.some.injEq,Option.elim_some] using (tendsto_pi_nhds.mp hg) a

end InvariantIsing

end

end OAI
