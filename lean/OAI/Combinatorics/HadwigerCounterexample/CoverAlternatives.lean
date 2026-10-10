import OAI.Combinatorics.HadwigerCounterexample.PhaseClassCompatibility
import OAI.Combinatorics.HadwigerCounterexample.LowRankKernelAlternative

namespace OAI

/-! # Cover Alternatives -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Filter
open scoped BigOperators Topology
open PredictionClass
variable {p : Shape} {n N M : ℕ}
theorem longStory (T : Cov p N) (d : ℕ) (hd : cdim p T≤d)
    (c : PredictionClass) (α : Party) (r : F) (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (hh : ∀ x,w x≠ 0 → covered p T (Δ x)) :
    ∃ P : UnitType p n N×UnitType p n N→Prop,named P (bp (3*d*(N:ℝ))) ∧
      named (P ∘ Prod.swap) (bp (3*d*(N:ℝ))) ∧
      ∀ x,pairW w w x≠0→ (P x↔ matchUp Δ α r c x) := by
  classical
  let Q (x : Daypair p T×Daypair p T) : Prop :=
    c.compatible α r (fun i=>x.2.2 i x.1.1, fun i => x.1.2 i x.2.1)
  let f := daypair p T Δ w
  refine ⟨fun x=>Q (f x.1,f x.2),day_named p T Δ w d hd Q,day_named p T Δ w d hd (Q∘Prod.swap),
    fun x hx=>?_⟩
  have hs (x y : UnitType p n N) (hz : w x≠0) (i) :
      (f y).2 i (f x).1=tone p y (unary i) (Δ x) :=
    shadow_valid p T Δ hh x y (unary i) hz
  unfold Q matchUp quench
  dsimp only
  simp_rw [hs _ _ (left_ne_zero_of_mul hx), hs _ _ (right_ne_zero_of_mul hx)]

theorem matSeason (T : Cov p N) (d : ℕ) (hd : cdim p T≤d)
    (α : Party) (r : F) (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (hh : ∀ x,w x≠ 0 → covered p T (Δ x)) :
    ∃ F : Mat (UnitType p n N) (UnitType p n N), F.rank ≤ 2*d*N ∧
      (∀ x, F x x=0) ∧ ∀ x,pairW w w x≠0→ (F x.1 x.2=0 ↔ matchUp Δ α r twinned x) := by
  let F := circus p T Δ w
  have he : F.rank ≤ N*d := (circus_rank ..).trans (Nat.mul_le_mul_left _ hd)
  refine ⟨F+Fᵀ, (mrk_add_le F Fᵀ).trans ?_,fun x=>char_two _,fun x hx=>?_⟩
  · rw [Matrix.rank_transpose]; nlinarith
  · unfold matchUp compatible quench
    dsimp only; rw [←tone_vec,←tone_vec]
    have h x y (hx : w x ≠ 0) : F x y = tone p y allSide (Δ x) :=
      shadow_valid p T Δ hh x y allSide hx
    change (F x.1 x.2+F x.2 x.1=0) ↔ _
    rw [h _ _ (left_ne_zero_of_mul hx),h _ _ (right_ne_zero_of_mul hx)]

set_option maxHeartbeats 1000000 in
theorem coFiber (l : Filter ℕ) (hz : l≤atTop) {M : ℕ} (hM : 1≤ M) (d : ℕ)
    (p : Shape) (w : ∀ n,Wgt (UnitType p n (M*n)))
    (α : Party) (r : F) (Δ : ∀ n, UnitType p n (M*n) → Ambient p (M*n))
    (h : ∀ᶠ n in l, IsLaw (w n) ∧
       ∃ T : Cov p (M*n),cdim p T≤d∧∀ x,w n x≠0 → covered p T (Δ n x))
    (he : slight l (fun n=>pr (pairW (w n) (w n)) (matchUp (Δ n) α r twinned))) :
    ∃ S : ∀ n, UnitType p n (M*n)→Prop,warm l (fun n=>((M*n:ℕ):ℝ)) (fun n=>pr (w n) (S n)) ∧
      ∀ᶠ n in l, ∀ x,S n x.1 → S n x.2 → matchUp (Δ n) α r twinned x := by
  classical
  let X n:= UnitType p n (M*n)
  let q n:= matchUp (Δ n) α r twinned
  let c (k : ℕ) := ((k:ℝ)+1)⁻¹
  let P n (S : X n→Prop) (k : ℕ) :=
     bp (-(c k)*((M*n:ℕ):ℝ)) ≤ pr (w n) S ∧ ∀ x,S x.1 → S x.2 → q n x
  have hf (k : ℕ) : ∀ᶠ n in l,∃ S : X n→Prop,P n S k := by
    obtain ⟨θ,hθ,hg⟩:= fiber_growth (2*d) (c k) (by unfold c; positivity) (by positivity)
    filter_upwards [h,he θ hθ, (trend_sizes l hz hM).1.eventually hg] with n hn hh hF
    obtain ⟨hv,T,hT,h⟩:=hn
    obtain ⟨F,hf,hz,hc⟩:= matSeason T d hT α r (Δ n) (w n) h
    have ht : pr (pairW (w n) (w n)) (fun x => F x.1 x.2=0) ≤ θ :=
      (avg_congr (fun x hx => show ind _=ind _ from congrArg ind (propext (hc x hx)))).trans_le hh
    have hr : (F.rank:ℝ)≤ 2*d*(M*n:ℕ) := by exact_mod_cast hf
    obtain ⟨S,hS,ht⟩:= hF (X n) F (w n) hv hr hz ht
    let Y (x:X n) := S x∧ w n x≠0
    have he : pr (w n) Y=pr (w n) S := avg_congr (fun x hx=>by simp [Y, hx])
    refine ⟨Y, hS.trans_eq he.symm, fun x hx hy =>
      (hc x (mul_ne_zero hx.2 hy.2)).mp (ht x.1 hx.1 x.2 hy.1)⟩
  obtain ⟨k,hk,hf⟩:= diagonal_gains l hz (fun n k => ∃ S : X n→Prop,P n S k) hf
  obtain ⟨S,h⟩:= taking hf
  refine ⟨S,fun ε he=>?_, h.mono fun i hi=>hi.2⟩
  filter_upwards [h,slight_inv_stage hk ε he] with n hn hh
  exact (bp_le (mul_le_mul_of_nonneg_right (neg_le_neg hh) (Nat.cast_nonneg _))).trans hn.1
end HadwigerCounterexample

end

end OAI
