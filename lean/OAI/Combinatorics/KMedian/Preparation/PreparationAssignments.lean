import Mathlib
import OAI.Combinatorics.KMedian.Preparation.SupplierMap
import OAI.Combinatorics.KMedian.Preparation.CoupledPreparation

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem supplier_assignments (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (next : T → T) (hnext : ∀ t, next t=t → c t=0)
    (hAP : ∀ t, Disjoint (A t) (P t)) (s : T) (d : I → ℝ) (R : Star I T → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp : 0 < p s) (hR0 : ∀ e, 0 ≤ R e)
    (hradius : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
      ∀ e, 0 < L.R ω s e → match supplier next e with
      | .inl i => d i ≤ R e
      | .inr t => ∀ i, 0 < L.C ω ξ (t,i) → d i ≤ R e) :
    letI := L.finite
    ∃ r : (L.Ω × (T → Finset I)) → (I ⊕ (T × I)) → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ Sum.elim
          (fun i => g*(L.O z.1 (.inl i):ℝ))
          (fun ti => g*(L.C z.1 z.2 ti:ℝ)) a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ P s, y i*d i)/p s+
        (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*R e) := by
  classical
  let := L.finite
  let μ := L.ν.joint L.κ
  let Y := fun z : L.Ω × (T → Finset I) => fun t i => g*(L.C z.1 z.2 (t,i):ℝ)
  let u := fun z : L.Ω × (T → Finset I) => fun i => g*(L.O z.1 (.inl i):ℝ)
  let q := fun z : L.Ω × (T → Finset I) => fun e => g*(L.R z.1 s e:ℝ)
  let b := fun ω t => g*(L.K ω t:ℝ)
  have halloc : ∀ z, 0 < μ.weight z → ∃ r : I ⊕ (T × I) → ℝ,
      (∀ a, 0 ≤ r a ∧ r a ≤ Sum.elim (u z) (fun ti => Y z ti.1 ti.2) a) ∧
      (∑ a, r a)=1 ∧
      (∑ a, r a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        (∑ i, Y z s i*d i)+(∑ e, q z e*R e) := by
    intro z hz
    obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
    have hsum : ∀ t, ∑ i, Y z t i=b z.1 t := by
      intro t
      simp only [Y,b,← mul_sum,← Nat.cast_sum,(L.pieces z.1 z.2 hξ t).1]
    have hqt : (∑ e, q z e)=1-b z.1 s := by
      have he := congrArg (fun n : ℕ => g*(n:ℝ)) (L.exact_total z.1 s)
      simp only [Nat.cast_add,Nat.cast_sum,mul_add,hunit,mul_sum] at he
      dsimp only [q,b]
      linarith only [he]
    have hzero : ∀ e, weight y P A c γ e=0 → q z e=0 := by
      intro e he
      have ho := L.open_zero z.1 hω e he
      have hr := L.request_cap z.1 hω s e
      rw [ho] at hr
      simp only [q,Nat.eq_zero_of_le_zero hr,Nat.cast_zero,mul_zero]
    have htarget : ∀ e, s ∉ targets A e → q z e=0 := by
      intro e he
      simp only [q,L.request_target z.1 s e he,Nat.cast_zero,mul_zero]
    apply allocate_suppliers (supplier next) (q z) s (u z) (Y z) (b z.1) d R
      (fun t i => mul_nonneg hg.le (Nat.cast_nonneg _)) hsum (L.half z.1)
      (fun e => mul_nonneg hg.le (Nat.cast_nonneg _)) hqt
    · intro i
      rw [outside_supplier]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.request_cap z.1 hω s (.inl i))) hg.le
    · exact self_supplier_zero P A y c γ next (q z) s hAP hnext htarget hzero
    · intro e he
      have he' : 0 < L.R z.1 s e := by
        have hp' := (mul_pos_iff_of_pos_left hg).mp he
        exact_mod_cast hp'
      have hrad := hradius z.1 hω z.2 hξ e he'
      cases hh : supplier next e with
      | inl i => simpa only [hh] using hrad
      | inr t =>
        simp only [hh] at hrad
        intro i hi
        have hi' : 0 < L.C z.1 z.2 (t,i) := by
          have hv := (mul_pos_iff_of_pos_left hg).mp hi
          exact_mod_cast hv
        exact hrad i hi'
  choose r hr using fun z : {z // 0 < μ.weight z} => halloc z.1 z.2
  let r' := fun z => if hz : 0 < μ.weight z then r ⟨z,hz⟩ else fun _ => 0
  refine ⟨r',?_,?_⟩
  · intro z hz
    have hz' : 0 < μ.weight z := hz
    simp only [r',dite_eq_left hz']
    exact ⟨(hr ⟨z,hz'⟩).1,(hr ⟨z,hz'⟩).2.1⟩
  · have he : μ.expect (fun z => ∑ a, r' z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
        μ.expect (fun z => (∑ i, Y z s i*d i)+(∑ e, q z e*R e)) :=
      μ.expect_mono_support (fun z hz => by
        simpa only [r',dite_eq_left hz] using (hr ⟨z,hz⟩).2.2)
    apply he.trans
    rw [FiniteLaw.expect_add]
    apply add_le_add
    · have hmean : μ.expect (fun z => ∑ i, Y z s i*d i)=
          L.ν.expect (fun ω => (b ω s/p s)*(∑ i ∈ P s, y i*d i)) := by
        rw [FiniteLaw.expect_joint]
        apply congrArg L.ν.expect
        funext ω
        rw [FiniteLaw.expect_sum]
        simp only [Y,FiniteLaw.expect_mul_right,L.piece_mean]
        simp only [ite_mul,zero_mul,sum_ite_mem,univ_inter]
        rw [mul_sum]
        exact sum_congr rfl (fun i _ => by dsimp only [b]; ring)
      rw [hmean]
      have ha : 0 ≤ ∑ i ∈ P s, y i*d i := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
      calc
        _ ≤ L.ν.expect (fun _ => (∑ i ∈ P s, y i*d i)/p s) := L.ν.expect_mono (fun ω => by
          have hcap : b ω s ≤ 1 := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.total_cap ω s)) hg.le).trans_eq hunit
          calc
            _ ≤ (1/p s)*(∑ i ∈ P s, y i*d i) := mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hcap hp.le) ha
            _ = _ := by ring)
        _ = _ := L.ν.expect_const _
    · rw [FiniteLaw.expect_joint]
      simp only [q,FiniteLaw.expect_const,FiniteLaw.expect_sum,FiniteLaw.expect_mul_right]
      exact sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (L.request_mean s e) (hR0 e))

end MetricKMedian.Preparation
end
end

end OAI
