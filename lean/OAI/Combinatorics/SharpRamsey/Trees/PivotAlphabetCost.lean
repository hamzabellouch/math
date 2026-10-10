import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotAlphabetMembership
import OAI.Combinatorics.SharpRamsey.Trees.PivotIndexCost

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {n : ℕ} {b τ P H : ℝ}

lemma three_card_le_exp (l m n : ℕ) (L : ℝ)
    (h : log ((l:ℝ)+1)+log ((m:ℝ)+1)+log ((n:ℝ)+1)≤L) :
    (l:ℝ)*m*n≤exp L := by
  calc
    _ ≤ ((l:ℝ)+1)*((m:ℝ)+1)*((n:ℝ)+1) := by gcongr <;> linarith
    _ = exp (log ((l:ℝ)+1)+log ((m:ℝ)+1)+log ((n:ℝ)+1)) := by
      rw [exp_add,exp_add,exp_log (by positivity),exp_log (by positivity),exp_log (by positivity)]
    _ ≤ _ := exp_le_exp.mpr h

def headerCost : ℝ :=
  log ((Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))):ℝ)+1)+
  log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma headerCost_nonneg : 0≤headerCost (K:=K) (V:=V) := by
  exact add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V)))); linarith))
    (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card (Projectivization K (Module.Dual K V))); linarith))

variable (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
include hb hH hP haP

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem Book.header_index_cost
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (s t : ℕ)
    (hh : Header (Nat.card K) b (n+3) U s t) :
    log (((book.library U s t).card:ℝ)+1)+log ((firstBound b U t:ℝ)+1)+
      log ((secondBound b U s:ℝ)+1)≤
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hlib := (book.valid U s t hh).2.2
  rcases hh with ⟨hs,ht,hsu,htv,hprod,_⟩
  have hb' : 0≤b+log 4 := add_nonneg hb (log_nonneg (by norm_num))
  have hbP : b+log 4≤P := (add_le_add_right (log_le_log (by norm_num) (by norm_num : (4:ℝ)≤1000000)) b).trans haP
  have he := local_index_budget hq (add_nonneg hb (log_nonneg (by norm_num))) haP hP hH
    (by exact_mod_cast hs) (by exact_mod_cast ht) (by exact_mod_cast hsu) (by exact_mod_cast htv)
    (show 0<(Nat.card K:ℝ)^(n+3) by positivity) hb' hbP hprod hlib
  simpa only [firstBound,secondBound,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective,
    potential] using he

theorem Book.allowed_card_exp (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    ((book.allowed z U).card:ℝ)≤exp (headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)) := by
  let L := (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)
  have hh (s t : ℕ) : ((book.library U s t).card:ℝ)*firstBound b U t*secondBound b U s≤exp L := by
    by_cases hh : Header (Nat.card K) b (n+3) U s t
    · exact three_card_le_exp _ _ _ L (book.header_index_cost hb hH hP haP U s t hh)
    · simp only [book.invalid U s t hh,card_empty,Nat.cast_zero,zero_mul]
      exact (exp_pos L).le
  calc
    _ ≤ ∑ s : FirstSize (K:=K) (V:=V),∑ t : SecondSize (K:=K) (V:=V),
        ((book.library U s t).card:ℝ)*firstBound b U t*secondBound b U s := by
      exact_mod_cast book.allowed_card z U
    _ ≤ ∑ _s : FirstSize (K:=K) (V:=V),∑ _t : SecondSize (K:=K) (V:=V),exp L := by
      exact sum_le_sum (fun s _=>sum_le_sum (fun t _=>hh s t))
    _ = (((Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))):ℝ)+1)*
        ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1))*exp L := by
      simp only [sum_const,card_univ,nsmul_eq_mul,FirstSize,SecondSize,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
      ring
    _ = _ := by
      rw [exp_add]
      congr 1
      dsimp only [headerCost]
      rw [exp_add,exp_log (by positivity),exp_log (by positivity)]

theorem Book.allowed_log_cost (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    log ((book.allowed z U).card:ℝ)≤headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P) := by
  by_cases hz : (book.allowed z U).card=0
  · rw [hz,Nat.cast_zero,log_zero]
    exact add_nonneg headerCost_nonneg (mul_nonneg (by positivity)
      (add_nonneg (potential_nonneg _ _) (by linarith)))
  · apply (log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr
    exact book.allowed_card_exp hb hH hP haP z U

end
end SharpLogRamsey.ActualPivot

end

end OAI
