import OAI.Combinatorics.HadwigerCounterexample.ProductComparisonScales

namespace OAI

/-! # Weak Product Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

theorem shadow_norm (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (ε : ℝ) (h : shadowed v q U ε)
    (hN : 2*num (I × Toast p)-(N:ℝ)≤ -1) :
    let W := netFact (trayPort p v.t)
    ∀ f : v.Localist N,(∀ i j,|f i j|≤1) →
      |avg (lawNu p N v.t q) (fun x=> U x*prodW f x)| ≤ W*ε := by
  classical
  intro W f hf
  let B := pr unif (ownPart (p:=p) v.t q (N:=N))
  have ht := priceNu v.t q hN
  have hW : 0<W := netFact_pos
  have hb : 0<B := (inv_pos_of_pos hW).trans_le ht
  let F i := U i * prodW f i
  have hh :
      board v q U f=B*avg (lawNu p N v.t q) F := by
    change _=pr _ (ownPart (p:=p) v.t q)*avg (unifOn _) _
    rw [← part_reset _ F hb]
    unfold board curtain F partMean
    simp only [mul_assoc]
  have he := h f hf; rw [hh,abs_mul,abs_of_pos hb] at he
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos hW)
  exact ((mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans he).trans_eq (by field_simp)

set_option maxHeartbeats 600000 in
theorem weakly (v : Template p I) (M : ℕ) (hM : 1 ≤ M)
    (C ε b : ℝ) (hε : 0<ε) (hb : 0≤ b) :
    ∃ (r : ℕ) (c : ℝ), 0<c ∧ ∀ᶠ n : ℕ in atTop, let N:= M*n
    ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)), (∀ i, |U i|≤ b) →
    ∃ T, design v T b r ∧
      (∀ f : v.Localist N,(∀ i j, |f i j|≤1) →
        |avg (lawNu p N v.t q) (fun x=> (U x-T x)*prodW f x)|≤ ε) ∧
      engaged v q (U-T) n C (bp (-c*n)) ε := by
  classical
  let W:=netFact (trayPort p v.t)
  have hW : 0<W := netFact_pos
  let u := min ε (ε/W)
  have hu : 0<u := lt_min hε (by positivity)
  obtain ⟨r,c,hc,h⟩ := plays_calendar p M hM C b hb (Fintype.card I) I (le_refl _) v u hu
  refine ⟨r,c,hc,?_⟩
  filter_upwards [h,(cast_tops M hM).eventually
    (eventually_ge_atTop (2*num (I × Toast p)+1))]
    with n hn hN N q U hU
  change 2*num (I×Toast p)+1 ≤ (N:ℝ) at hN
  obtain ⟨T,hT,hQ,h⟩:=hn q U hU
  refine ⟨T,hT,fun f hf=>?_,?_⟩
  · have he := shadow_norm v q (U-T) u hQ (by linarith only [hN]) f hf
    have hh : W*u≤ ε := by rw [mul_comm]; exact (le_div_iff₀ hW).mp (min_le_right ..)
    exact he.trans hh
  intro m hN w hw s x hx hz
  refine (pr_mono hw.1.nz (fun i hh=>?_)).trans (h m hN w hw s x hx hz)
  obtain ⟨f,hf,hg⟩ := hh
  exact ⟨f,hf,lt_of_le_of_lt (min_le_left ..) hg⟩
end Template
end HadwigerCounterexample

end

end OAI
