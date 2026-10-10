import OAI.NumberTheory.TotientAsymptotic.InitialRoughData
import OAI.NumberTheory.TotientAsymptotic.CollisionPrimeCount

namespace OAI

/-! Counting the extracted prime with the rough cofactor fixed. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma initial_prime_fiber_bound {a b d : ℕ} {y L C : ℝ}
    (hd : 0 < d) (hy : Real.exp 2 ≤ y) (hBy : 1 ≤ B y) (hL : 0 < L) (hC : 0 < C)
    (hcount : ∀ a b N : ℕ,0 < a → 0 < b → a ≠ b → (a:ℝ) ≤ y → (b:ℝ) ≤ y → L ≤ Real.log N →
      ∀ Q : Finset ℕ,(∀ q ∈ Q,q ≤ N ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
      (Q.card:ℝ) ≤ C*N*(B y)^2/L^3)
    (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E,InitialPrimeData a b d y L e)
    (v : ℕ) (hv : v ∈ E.image Prod.fst) :
    ((E.filter (fun e => e.1=v)).card:ℝ) ≤
      (C*(y/d)*(B y)^2/L^3)*(v:ℝ)⁻¹ := by
  classical
  obtain ⟨e,he,hev⟩ := Finset.mem_image.mp hv
  have hw := hE e he
  have hv0 : 0 < v := hev ▸ hw.residual_pos
  have hdv : (0:ℝ) < (d*v:ℕ) := by exact_mod_cast Nat.mul_pos hd hv0
  have hy0 : 0 ≤ y := (Real.exp_pos 2).le.trans hy
  let N := ⌊y/(d*v:ℕ)⌋₊
  let F := E.filter (fun e => e.1=v)
  let Q := F.image Prod.snd
  have hqdata (q : ℕ) (hq : q ∈ Q) :
      q ≤ N ∧ q.Prime ∧ (a*v*q+1).Prime ∧ (b*v*q+1).Prime := by
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hf,hfv⟩ := Finset.mem_filter.mp hf
    have hh := hE f hf
    refine ⟨?_,hh.prime,?_,?_⟩
    · apply Nat.le_floor
      apply (le_div_iff₀ hdv).mpr
      have hs := hh.size
      rw [hfv] at hs
      simpa only [Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using hs
    · simpa only [hfv] using hh.left_prime
    · simpa only [hfv] using hh.right_prime
  have heQ : e.2 ∈ Q := Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hev⟩,rfl⟩
  have hlogN : L ≤ Real.log N := hw.log_lower.trans
    (Real.log_le_log (by exact_mod_cast hw.prime.pos) (by exact_mod_cast (hqdata e.2 heQ).1))
  have ha : 0 < a*v := hev ▸ hw.left_pos
  have hb : 0 < b*v := hev ▸ hw.right_pos
  have hab : a*v ≠ b*v := hev ▸ hw.different
  have hay : ((a*v:ℕ):ℝ) ≤ y := hev ▸ hw.left_le
  have hby : ((b*v:ℕ):ℝ) ≤ y := hev ▸ hw.right_le
  have hc := hcount (a*v) (b*v) N ha hb hab hay hby hlogN Q hqdata
  have hcard : Q.card=F.card := Finset.card_image_of_injOn (by
    intro f hf g hg heq
    exact Prod.ext ((Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm) heq)
  rw [hcard] at hc
  have hN : (N:ℝ) ≤ y/(d*v:ℕ) := Nat.floor_le (div_nonneg hy0 hdv.le)
  calc
    _ ≤ C*N*(B y)^2/L^3 := hc
    _ ≤ C*(y/(d*v:ℕ))*(B y)^2/L^3 := by gcongr
    _ = _ := by push_cast; field_simp

end TotientAsymptotic

end

end OAI
