import OAI.Combinatorics.HadwigerCounterexample.SurrogateStatusLaws

namespace OAI

/-! # Cell Positivity Scales -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}
namespace StatusAnalysis
open Template
variable {b : PreparationParameters}

namespace Appearance
variable (x : Appearance p) {s0 : ℕ}

theorem readCap (x : Appearance p) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
    ∀ Y : Silhouette p N r,pr (raw m N) (fun o=> x.apt∧¬ x.close Y o ε)≤bp (-(1/16:ℝ)*n) := by
  classical
  have hp:=h.enter.first
  by_cases ha : x.apt
  · let δ : ℝ := ε/(r+1:ℝ)
    have hδ : 0<δ:=by unfold δ; positivity
    filter_upwards [flat_recital x.trot M hp.hM hp.hJ δ hδ,eventually_ge_atTop (2*p.r),
      pay_nat (a:=1/8) (b:=1/16) (num (Fin r)) (by norm_num)] with n hn ht hB N m hN Y
    let w:= x.wit n; let v:= raw m N
    have hw : IsLaw w:= witLaw ha hp.hR ht
    let P (i : Fin r) (o : Orient p n N):=
      δ≤ |x.empirical Y o i - x.reference Y i|
    have hk (i : Fin r) : pr v (P i) ≤ bp (-(1/8:ℝ)*n) := by
      let S (z) := ind (Y x.l x.q z=i)
      have hf z : |S z|≤1 := by unfold S; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
      refine hn m w x.q hw (normW_carried (subW_carried _ _))
        (scopedZ_bit p n _ _ _ hw) hN S hf
    have he (o : Orient p n N) (h : x.apt∧¬x.close Y o ε) : ∃ i,P i o := by
      by_contra! hh
      apply h.2
      unfold close varOne
      calc _ ≤ ∑ i : Fin r,δ:= Finset.sum_le_sum fun i _=>le_trans (abs_sub_comm ..).le
             (le_of_not_ge (hh i))
           _ ≤ ε := by
             simp; unfold δ
             calc _ ≤ ((r:ℝ)+1)* (ε/(r+1:ℝ)) := mul_le_mul_of_nonneg_right (by linarith) hδ.le
                  _ = ε := by field_simp
    have hv : IsLaw v:= raw_law m hN
    exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz P)).trans
      (((Finset.sum_le_sum fun i _=>hk i).trans_eq (by simp [num])).trans hB)
  filter_upwards with n N m hN Y
  simp_rw [show (x.apt)=False from eq_false ha,false_and,pr_false]; exact (bp_pos _).le

def foil (x : Appearance p) (Y : Silhouette p N r) (o : Orient p n N)
    (m : Mixer p n) (K : ℕ) (δ : ℝ) :=
    ∀ (z:Digest p.g) (i:Fin r), z.feasible x.l x.f → z.sumBit=x.q →
      δ ≤ x.reference Y i → Template.patrol x.trot m (scopedScan p n x.l x.f z)
        (fun y => Y x.l x.q y=i) K x.q o

theorem foilCap (x : Appearance p) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (δ:ℝ) (hδ:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
      unaryGood m b.pins s0 → ∀ Y: Silhouette p N r,
      pr (raw m N) (fun i=>¬x.foil Y i m b.pins δ)≤bp (-(1/18:ℝ)*n) := by
  classical
  have ht:=h.enter.first
  let A:= Digest p.g × Fin r
  let Q n (m:Mixer p n) (Y:Silhouette p (M*n) r) (a : A) (o : Orient p n (M*n)) :=
    a.1.feasible x.l x.f ∧ a.1.sumBit=x.q ∧ δ≤x.reference Y a.2 ∧
      ¬Template.patrol x.trot m (scopedScan p n x.l x.f a.1)
        (fun y=>Y x.l x.q y=a.2) b.pins x.q o
  have hg (a:A) :
      ∀ᶠ n:ℕ in atTop,let N:=M*n;∀ m:Mixer p n,2*num (Full p n)<(N:ℝ) →
        unaryGood m b.pins s0→∀ Y:Silhouette p N r,
          pr (raw m N) (Q n m Y a) ≤ bp (-(1/16:ℝ)*n) := by
    by_cases hf : a.1.feasible x.l x.f ∧ a.1.sumBit=x.q
    · filter_upwards [patrolled x.trot M ht.hM ht.hg ht.hJ a.1 hf.1 ht.hR δ hδ h.profiles
        h.gleaming] with n hn N m hN hM Y
      by_cases he : δ ≤ x.reference Y a.2
      · let S : AtomKey (p:=p) (x.trot.t ()) (M*n) →Prop := fun i=>Y x.l x.q i=a.2
        let v:=scopedScan p n (x.trot.t ()) (x.trot.f ()) a.1
        have hx : δ ≤ pr (lawOmega p (M*n) (x.trot.t ()) a.1.sumBit) S := by
          rw [hf.2]; exact he
        have hh (i:Orient p n (M*n)) (h:Q n m Y a i) :
            ¬Template.patrol x.trot m v S b.pins a.1.sumBit i := hf.2 ▸ h.2.2.2
        exact (pr_mono (raw_law m hN).nz hh).trans (hn m hM hN S hx)
      have hg : Q n m Y a=fun _=> False :=
        funext fun i=> eq_false (fun h=>he h.2.2.1)
      change pr (raw m (M*n)) (Q n m Y a) ≤ _
      rw [hg,pr_false]; exact (bp_pos _).le
    filter_upwards with n N m hN hg Y
    have hh : Q n m Y a=fun _=> False :=
      funext fun i=> eq_false (fun h=> hf ⟨h.1,h.2.1⟩)
    change pr (raw m (M*n)) (Q n m Y a) ≤ _
    rw [hh,pr_false]; exact (bp_pos _).le
  filter_upwards [eventually_all.mpr hg,pay_nat (a:=1/16) (b:=1/18) (num A) (by norm_num)]
    with n hn hB N m hN hM Y
  have he o (h : ¬x.foil Y o m b.pins δ) : ∃ i, Q n m Y i o := by
    unfold foil at h
    push Not at h
    obtain ⟨z,i,h⟩:=h
    exact ⟨(z,i),h⟩
  let v:=raw m N
  have hv : IsLaw v:=raw_law m hN
  exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hn i m hN hM Y).trans_eq (by simp [num])).trans hB)
end Appearance

def smoothSilk (p : Shape) (ε δ:ℝ) (Y:Silhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:Orient p n N) :=
    ∀ x : Appearance p,(x.apt → x.close Y o ε) ∧ x.foil Y o m K δ

variable {s0 : ℕ}

def gauze (p : Shape) (ε δ:ℝ) (Y:Silhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:UnitType p n N) :=
  ∀ i,smoothSilk p ε δ Y m K (onSide o i)

private theorem silken (p : Shape) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε δ : ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
      unaryGood m b.pins s0 → ∀ Y: Silhouette p N r,
      pr (raw m N) (fun i=>¬smoothSilk p ε δ Y m b.pins i)≤bp (-(1/20:ℝ)*n) := by
  classical
  let A:= Appearance p
  filter_upwards [eventually_all.mpr (fun x:A=>x.foilCap r M h δ hd),
    eventually_all.mpr (fun x:A=>x.readCap r M h ε he),
    pay_nat (a:=1/18) (b:=1/20) (num A*2) (by norm_num)] with n hn ht hB N m hN hM Y
  let v:=raw m N
  have hv : IsLaw v:=raw_law m hN
  let P (x:A) (o:Orient p n N) :=
    (x.apt ∧ ¬x.close Y o ε)∨ ¬x.foil Y o m b.pins δ
  have hk x : pr v (P x) ≤ 2*bp (-(1/18:ℝ)*n) := by
    rw [two_mul]; apply (pr_or_le hv.nz).trans
    refine add_le_add ((ht x m hN Y).trans (bp_le ?_)) (hn x m hN hM Y)
    linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hi o (h : ¬smoothSilk p ε δ Y m b.pins o) : ∃ i, P i o := by
    unfold smoothSilk at h
    obtain ⟨i,h⟩:= Classical.not_forall.mp h
    exact ⟨i,by unfold P; tauto⟩
  refine ((pr_mono hv.nz hi).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hk i).trans_eq ?_).trans hB)
  simp [num,mul_assoc]

theorem gauzeCalendar (p : Shape) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε δ:ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,∀ u : Wgt (UnitType p n N),
      PreparationParameters.Align b s0 p M n m u → ∀ Y: Silhouette p N r,
      pr u (fun i=>¬gauze p ε δ Y m b.pins i)≤bp (-(1/100:ℝ)*n) := by
  classical
  filter_upwards [silken p r M h ε δ he hd,pay_nat (a:=1/20-1/32) (b:=1/100) 2
    (by norm_num)] with n hn ht N m u hu Y
  let P (o:Orient p n N) := ¬smoothSilk p ε δ Y m b.pins o
  let Q (i:Bool) (o:UnitType p n N):=P (onSide o i)
  have hc : bySide p u m (bp ((1/32:ℝ)*n)) := fun i=> by
    have hh:= hu.drain
    cases i; exact hh.2.2.1; exact hh.2.1
  have hf : ∀ i,pr u (Q i) ≤bp (-((1/20:ℝ)-1/32)*n) := by
    intro i
    let x := fun o:UnitType p n N=>onSide o i
    change pr u (fun i=>P (x i)) ≤_
    rw [←mapW_pr]
    exact (pr_cap (hc i) P).trans ((mul_le_mul_of_nonneg_left
      (hn m hu.cols hu.hymn Y) (bp_pos _).le).trans_eq (by rw [←bp_add]; congr 1; ring))
  have he o (h : ¬gauze p ε δ Y m b.pins o) : ∃ i,Q i o := Classical.not_forall.mp h
  have hv : IsLaw u:=hu.drain.1
  rw [two_mul] at ht
  refine ((pr_mono hv.nz he).trans ((pr_exists_le hv.nz _).trans ?_))
  rw [Fintype.sum_bool]; exact (add_le_add (hf _) (hf _)).trans ht

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
