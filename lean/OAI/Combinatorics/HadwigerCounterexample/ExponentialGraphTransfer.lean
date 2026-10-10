import OAI.Combinatorics.HadwigerCounterexample.FiniteGraphTransfer
import OAI.Combinatorics.HadwigerCounterexample.ExponentialRates

namespace OAI

/-! # Exponential Graph Transfer -/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Real Filter

def ord (g N : ℕ) := (2:ℕ)^(1000*g*N)
theorem cast_ord (g N : ℕ) : ((ord g N : ℕ):ℝ) = bp (1000*g*N) := by
  unfold ord
  have h := bp_nat (1000*g*N)
  push_cast at *
  exact h.symm

theorem tendsto_ord {g : ℕ} (hg : 0 < g) : Tendsto (ord g) atTop atTop := by
  have hl : Tendsto (fun n : ℕ => bp (1000*g*n)) atTop atTop :=
    (bp_tendsto (show (0:ℝ)<1000*g by positivity)).comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop]
  intro b
  filter_upwards [hl.eventually (eventually_ge_atTop (b:ℝ))] with i hi
  change _ ≤ bp _ at hi
  rw [← cast_ord] at hi
  exact_mod_cast hi

/-- Raw supersaturation ⇒ existence for the sampled order. Takes any fixed
polynomial bit-count bound of degree two for the raw unit space. In particular
the eventual N-bound is independent of every law and graph. -/
theorem transfer_scales {g : ℕ} (hg : 0 < g) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Type) [Fintype A] [Nonempty A]
      (H : Holes A) (μ : Wgt A), IsLaw μ →
      (Fintype.card (A × A) : ℝ) ≤ bp (B * (N:ℝ)^2) →
      (∀ w : Wgt (A × A), IsLaw w → pairCaps μ (bp 1000) (bp (4000*g*N)) w →
        carried w H.unit → bp (-100*g*N) ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2)) →
      ∃ x : Fin (ord g N) → A,
        (H.graph x).indepNum ≤ 2 ∧
        (connectedMatchingNumber (H.graph x) : ℚ) < (ord g N : ℚ)/100 := by
  have hg' : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hh := bp_poly_dom_nat (a:=100*g) (by positivity) (B+1) 2
  filter_upwards [hh, eventually_ge_atTop 1,
    (tendsto_ord hg).eventually (eventually_ge_atTop 2)] with N hN hN' hord
  intro A _ _ H μ hμ hA hs
  let y : ℝ := g * (N:ℝ)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN'
  have hy : 1 ≤ y := by unfold y; nlinarith
  let m := ord g N
  let L : ℕ := 2^(200*g*N)
  have hm : (m:ℝ) = bp (1000*y) := by rw [cast_ord]; unfold y; ring_nf
  have hl : (L:ℝ) = bp (200*y) := by
    have h := (bp_nat (200*g*N)).symm
    push_cast at h
    dsimp only [L]
    push_cast
    unfold y
    rwa [← mul_assoc]
  let z : ℝ := B*(N:ℝ)^2
  have hz : 0 ≤ z := by unfold z; positivity
  have hb : z + 1 < bp (100*y) := by
    have hh : (B+1)*(N:ℝ)^2 < bp (100*y) := by simpa only [y, mul_assoc] using hN
    unfold z
    nlinarith only [hh,hNr]
  let k := (m+199)/200
  refine transfer H hμ (bp_pos _) (bp_pos _) (bp_pos _) hs (L:=L) (k:=k) ?_ ?_ ?_
  · have hi : log (Fintype.card (A × A) : ℝ) ≤ z * Real.log 2 := by
      rw [← log_bp]
      exact Real.log_le_log (by exact_mod_cast Fintype.card_pos) hA
    apply lt_of_le_of_lt hi
    calc z * log 2 < bp (100*y)*log 2 :=
           mul_lt_mul_of_pos_right (by linarith only [hb]) (Real.log_pos (by norm_num))
         _ = _ := by
           rw [hl,← mul_assoc (bp (200 * y)),← bp_add]
           unfold y; ring_nf
  · change 200*((m+199)/200) < m+200
    omega
  · have hk : (m:ℝ) ≤ 200*k := by
      have hk : m ≤ 200*k := by unfold k; omega
      exact_mod_cast hk
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hord
    let a := (Fintype.card (A × A):ℝ)+1
    have ha : a ≤ bp (z+1) := by
      rw [bp_add,bp_one]
      have hx : 1 ≤ bp z := by simpa only [bp_zero] using bp_le hz
      change _ ≤ bp z at hA
      dsimp only [a]
      linarith only [hx,hA]
    have hal : a^L ≤ bp (m:ℝ) := calc
      a^L ≤ bp (z+1)^L := by
        have hp : 0 ≤ a := by dsimp [a]; positivity
        gcongr
      _ = bp ((z+1)*L) := (bp_mul_nat _ _).symm
      _ ≤ bp (m:ℝ) := bp_le (by
        rw [hm,hl]
        calc (z+1)*bp (200*y) ≤ bp (100*y)*bp (200*y) :=
               mul_le_mul_of_nonneg_right hb.le (bp_pos _).le
             _ ≤ bp (1000*y) := by rw [← bp_add]; apply bp_le; linarith only [hy])
    let d := bp (4000*(g:ℝ)*(N:ℝ))
    have ha1 : bp (m:ℝ) * ((2:ℝ)^m * (2/bp 1000)^k) ≤ bp (-(m:ℝ)) := by
      rw [← bp_nat, show 2/bp 1000 = bp (1-1000) by simp only [bp_sub,bp_one],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      linarith
    have ha2 : bp (m:ℝ) * ((m:ℝ)^(k+k) * (d⁻¹)^k) ≤ bp (-(m:ℝ)) := by

      have he : (m:ℝ)^(k+k) = bp ((1000*y)*(k+k:ℕ)) := by
        rw [hm,bp_mul_nat]
      rw [he, show d⁻¹ = bp (-(4000*y)) by simp only [bp_neg,d,y,mul_assoc],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      push_cast
      have hx : (k:ℝ) ≤ y*k := by
        have : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have hx : bp (-(m:ℝ)) < 1/2 := by
      rw [show (1:ℝ)/2 = bp (-1) by simp only [one_div,bp_neg,bp_one]]
      exact bp_lt (by linarith only [hm'])
    change a^L * (2^m * (2/bp 1000)^k + (m:ℝ)^(k+k) * d⁻¹^k) < 1
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hal (by
      have h := bp_pos 1000
      have h' : 0 < d := bp_pos _
      positivity)) ?_
    linarith only [ha1,ha2,hx]

end HadwigerCounterexample

end

end OAI
