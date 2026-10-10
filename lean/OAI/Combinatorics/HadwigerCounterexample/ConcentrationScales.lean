import OAI.Combinatorics.HadwigerCounterexample.DependentPairConcentration

namespace OAI

/-! # Concentration Scales -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Finset Filter Real Function
open scoped BigOperators Topology
variable {X : Type*}

/-- pay slack for any fixed multiple of exponentially smaller term. -/
theorem pay_nat {a b : ℝ} (c : ℝ) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ bp (-b*n) := by
  have h := (bp_tendsto (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually (eventually_ge_atTop c)] with n hn
  change c ≤ bp ((a-b)*n) at hn
  refine (mul_le_mul_of_nonneg_right hn (bp_pos _).le).trans_eq ?_
  rw [← bp_add, show (a-b)*n + -a*n= -b*n by ring]

theorem pay_div_nat {a b : ℝ} (c u : ℝ) (hu : 0 < u) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ u*bp (-b*n) := by
  filter_upwards [pay_nat (c/u) hab] with n hn
  calc _ = u*(c/u*bp (-a*n)) := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left hn hu.le

theorem cast_tops (M : ℕ) (hM : 1≤M) :
    Tendsto (fun n : ℕ => (↑(M*n):ℝ)) atTop atTop := by
  simp_rw [Nat.cast_mul]; exact
    (tendsto_const_mul_atTop_of_pos (show 0<(M:ℝ) from by
      exact_mod_cast (show 0 < M from hM))).mpr tendsto_natCast_atTop_atTop

variable {p : Shape} {M n N : ℕ}
variable {I J K G A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable [Fintype A] [Fintype B]
variable {g : Route J G}

omit [Fintype G] [DecidableEq J] in
theorem port_limit (g : Route J G) (i : G) :
    num (Port g i) ≤ num J := by
  exact_mod_cast Fintype.card_subtype_le _

namespace Program
variable {s : Program p n g A}

/-- empirical input-and-image law -/
def makeData (s : Program p n g A) (w : Wgt A) (o : Forum p n N G) :
    Wgt (A×Rack J N) :=
  mapW w (fun x => (x,s.showKey x o))
omit [Fintype G] [DecidableEq G] in
theorem data_law (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (hw : IsLaw w) : IsLaw (s.makeData w o) := mapW_law hw _
omit [Fintype G] [DecidableEq G] in
theorem view_data (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (f : Wgt (A×Rack J N)) :
    avg (s.makeData w o) f=s.oexpect w (fun a b => f (a,b)) o := mapW_avg ..
omit [Fintype G] [DecidableEq G] in
theorem freq_data (s : Program p n g A) (w : Wgt A) (o : Forum p n N G)
    (P : A×Rack J N→Prop) :
    pr (s.makeData w o) P = oFreq w (fun a b => P (a,b)) o s := mapW_pr ..

set_option maxHeartbeats 600000 in
theorem variance_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (r u : ℝ) (hu : 0 < u) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (T : A→ Wgt (Rack J N)) (w : Wgt A), IsLaw w →
      (∀ x y, |T x y|≤1) →2*num (Full p n)<N →
      pr (draws Bool w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      (let v := forumLaw m N
       let f := s.oexpect w T
       avg v (fun x => (f x-avg v f)^2)) ≤ u*bp (-(1/4:ℝ)*n) := by
  let t := tied g Bool
  let k := num (Bool×J)
  let b := 2*netFact t
  let c := num G* (2*bp k)+1
  filter_upwards [pay_div_nat (a:=1) (2*bp r) (u/2) (by positivity) (b:=1/4) (by norm_num),
    pay_div_nat (a:=1/2) (b*c) (u/2) (by positivity) (b:=1/4) (by norm_num),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hh hk N m A _ s T w hw hT hN h
  change (2*k+1) ≤ (↑(M*n) : ℝ) at hk
  have he := oVar m hN T w hw hT k (fun i => port_limit _ i) (by linarith only [hk])
    (bp (r-n)) h
  apply he.trans
  subst N
  have hv : (n:ℝ) ≤ (M*n:ℕ) := by exact_mod_cast (show n ≤ M*n from by nlinarith)
  let P := bp (-(1/2:ℝ)*n)
  have ht : twinkle t k (M*n) ≤ c*P := by
    have hq : bp (k-(M*n:ℕ)) ≤ bp k*P := by
      unfold P; rw [← bp_add]; apply bp_le; linarith only [hv,Nat.cast_nonneg (α:=ℝ) n]
    have hr : bp (-(↑(M*n):ℝ)/2)≤P := bp_le (by linarith only [hv])
    calc _ ≤ num G*(2*(bp k * P))+P := add_le_add
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by norm_num))
                  (Nat.cast_nonneg _)) hr
         _ = _ := by unfold c; ring
  have h1 : 2*bp (r-n) ≤ u/2*bp (-(1/4:ℝ)*n) := by
    simpa only [mul_assoc,← bp_add,neg_mul,one_mul,←sub_eq_add_neg] using hn
  have h2 : 2*netFact t* twinkle t k (M*n)≤ u/2*bp (-(1/4:ℝ)*n) :=
    (mul_le_mul_of_nonneg_left ht (by apply mul_nonneg (by norm_num) netFact_pos.le)).trans
      (le_trans (le_of_eq (Eq.symm (mul_assoc b c P))) hh)
  exact (add_le_add h1 h2).trans_eq (by ring)

theorem approx_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (r η : ℝ) (hη : 0<η) (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (w : Wgt A), IsLaw w →
      2*num (Full p n)<N →
      pr (draws Bool w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      approxData (forumLaw m N) (s.makeData w) η (bp (-(1/4:ℝ)*n)) := by
  filter_upwards [variance_calendar p M g r (η^2) (by positivity) hM]
    with n hn N m A _ s w hw hN he F hF
  subst N
  let T (x : A) (y : Rack J (M*n)) := F (x,y)
  rw [mixW_avg]; simp_rw [view_data]
  refine (outlier (forum_law m hN).nz _ η hη
    (hn m _ s T w hw (fun x y => hF _) hN he)).trans_eq ?_
  field_simp

theorem thin_calendar (p : Shape) (M : ℕ) (g : Route J G)
    (b η c : ℝ) (hc : 0 < c) (hη : 0<η) (hM : 1≤M) :
    ∃ l : ℕ, ∀ r : ℝ, ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (A : Type) [Fintype A] (s : Program p n g A)
      (w : Wgt A), IsLaw w →
      2*num (Full p n)<N →
      pr (draws (Fin l) w) (fun x => ¬ s.free x) ≤ bp (r-n) →
      thinData (forumLaw m N) (s.makeData w) (bp (-c*n)) η (bp (-b*n)) := by
  obtain ⟨l,hl⟩ := exists_nat_gt (b/c)
  let d := η^l/2
  have hd : 0<d := by positivity
  let t := tied g (Fin l)
  let k := num (Fin l × J)
  refine ⟨l,fun r => ?_⟩
  filter_upwards [pay_div_nat (a:=1) (bp r) d hd (b:=0) (by norm_num),
    pay_div_nat (a:=c*l) (netFact t) d hd (b:=b)
      (by rwa [div_lt_iff₀ hc,mul_comm] at hl),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hh hk N m A _ s w hw hN hr P hP
  subst N; let N := M*n
  change 2*k+1 ≤ (N:ℝ) at hk
  let T (x : A) (y : Rack J N) := P (x,y)
  let v := forumLaw (G:=G) m N
  let f := fun o => oFreq w T o s
  rw [show pr (mixW v (s.makeData w)) P=avg v (fun x => pr (s.makeData w x) P) from mixW_avg ..] at hP
  simp_rw [freq_data] at *
  have hi : bp (r-n) ≤ d := by
    simpa only [neg_zero,zero_mul,bp_zero,mul_one,← bp_add,neg_mul,one_mul, ← sub_eq_add_neg]
      using hn
  have hj : η^l=d+d := by unfold d; ring
  have he := oTail m hN T w hw (k:=k) (fun i => port_limit _ i) (by linarith only [hk])
    (bp (r-n)) hr hη.le
  have hv := forum_law (G:=G) m hN
  apply le_of_mul_le_mul_left _ hd
  calc d*pr v (fun x => η ≤ f x)
    _ ≤ _ := mul_le_mul_of_nonneg_right (show d≤η^l-bp (r-n) from by
             rw [hj]; linarith only [hi]) (pr_nonneg hv.nz)
    _ ≤ _ := he
    _ ≤ netFact t * bp (-c*n)^l := mul_le_mul_of_nonneg_left
           (pow_le_pow_left₀ (avg_nonneg hv.nz fun x => pr_nonneg hw.nz) hP l) netFact_pos.le
    _ ≤ _ := by rw [← bp_mul_nat,show -c*n*l= -(c*l)*n by ring]; exact hh
end Program
end HadwigerCounterexample

end

end OAI
