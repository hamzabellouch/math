import OAI.Combinatorics.HadwigerCounterexample.ConditionalLargeSetHits

namespace OAI

/-! # Large Set Hits -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K r s0:ℕ}
namespace StatusAnalysis
namespace Quill
variable {q:Format} {d:Rates} {b:Bool} (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F)
def dilate (K:ℕ) := (w.pen t).kappa*((basebeta p K)/2)^Fintype.card (Messenger q)
theorem dilate_pos (K:ℕ) : 0<w.dilate t K :=
   mul_pos (kappa_pos _) (pow_pos (half_pos (basebeta_pos _ _)) _)

set_option maxHeartbeats 1000000 in
theorem sheen_hit (m:Mixer p n) (Y:Silhouette p N r) (o:UnitType p n N) (s:Charts p n d)
    (H:Keys (p:=p) t N→Prop)
    {ε δ:ℝ} (hp:0<δ) (he: ε≤pr (lawNu p N t z) H)
    (hw : w.moral t z) (ht :1≤p.r) (hn:2*p.r≤n)
    (hg : w.steady t z m K s o)
    (hN:2*num (Messenger q×Toast p)-(N:ℝ)≤ -1) (hh:2*num (Toast p)-(N:ℝ)≤ -1)
    (hK : num (Messenger q)*(r*δ+2*netFact (trayPort p t)*bp (-(N:ℝ)/2)) ≤ ε/2)
    (hq:gauze p δ δ Y m K o) :
    w.dilate t K * (ε/2) ≤ w.sheen t z o m s Y (fun x=> ind (H x)) := by
  classical
  let ν:=lawNu p N t z
  have hu i:IsLaw (w.policies t z n i) := Appearance.witLaw (w.allure_apt t z hw _) ht hn
  have hν := nuLaw t z hN
  let I:=Messenger q
  let f i:=w.allure t z i
  let P (i:I) (x:Keys (p:=p) t N) := δ≤ (f i).reference Y (Y (t i) (z i) (x i))
  let Q (x:Keys (p:=p) t N):=∀ i,P i x
  have hm i : pr ν (fun x=>¬P i x)≤
      r*δ+2*netFact (trayPort p t)*bp (-(N:ℝ)/2) := by
    unfold P; simp_rw [not_le]
    exact w.tinyCell_loss t z Y hp.le _ hN hh
  have h1 : pr ν (fun x=>¬Q x) ≤ ε/2 := by
    have hx (x) (h:¬Q x) : ∃ i,¬ P i x := Classical.not_forall.mp h
    refine ((pr_mono hν.nz hx).trans (pr_exists_le hν.nz _)).trans
      ((Finset.sum_le_sum (fun i _=>hm i)).trans ?_)
    rw [Finset.sum_const]
    simpa only [Finset.card_univ,nsmul_eq_mul] using hK
  have h2 : ε/2 ≤ pr ν (fun x=> H x∧Q x) :=
    le_trans (by linarith only [he,h1]) (pr_shield hν.nz H Q)
  let L:=w.dilate t K; let Z:=basebeta p K/2
  have hh x (hx:Q x) : L ≤ w.mirror t z o m s Y x := by
    have hg' i : Z ≤ w.seraph t z o m s Y i (x i):= w.thinGlaze t z m Y o i s (x i) hp hw hg hq ht hn (hx i)
    apply mul_le_mul_of_nonneg_left _ (kappa_pos _).le
    change Z^Fintype.card I≤prodW _ _
    rw [show Z^Fintype.card I=∏ i:Messenger q,Z from by simp [I]]
    exact Finset.prod_le_prod₀ (fun i _=> (half_pos (basebeta_pos _ _)).le) fun i _=>hg' i
  apply (mul_le_mul_of_nonneg_left h2 (w.dilate_pos _ _).le).trans
  unfold pr sheen; rw [←avg_mul']; refine avg_mono hν.nz fun i => ?_
  dsimp only
  by_cases h:H i
  · rw [show (H i ∧ Q i)=Q i from propext (and_iff_right h),ind_one h,mul_one]
    by_cases hp : Q i
    · rw [ind_one hp,mul_one]; exact hh i hp
    rw [ind_zero hp,mul_zero]
    exact (w.mirror_floor t z o m s Y hu i).1
  rw [ind_zero h,ind_zero (show ¬ (H i∧ Q i) from fun hv=>h hv.1),mul_zero,mul_zero]

variable {b':PreparationParameters}
def sober (K:ℕ) (H:Keys (p:=p) t N→Prop) (m:Mixer p n) (α:ℝ) (o:UnitType p n N) :=
  ∀ s:Charts p n d,w.steady t z m K s o → α≤w.prowl s t z m o (fun x=>ind (H x))

set_option maxHeartbeats 1400000 in
theorem soberCalendar (h:AnalyticParameters p M b' s0) (hw : w.moral t z) (ε:ℝ) (he:0<ε) :
    ∃ (α c:ℝ),0<α∧0<c ∧ ∀ᶠ n:ℕ in atTop,let N:=M*n;let K:=b'.pins;
      ∀ (m:Mixer p n) (U:Wgt (UnitType p n N)), b'.Align s0 p M n m U →
      ∀ H : Keys (p:=p) t N→Prop, ε≤pr (lawNu p N t z) H →
      pr U (fun i=>¬w.sober t z K H m α i) ≤ bp (-c*n) := by
  classical
  let K:=b'.pins
  let α:=w.dilate t K*(ε/4)
  have hα :0<α:=mul_pos (dilate_pos ..) (by positivity)
  obtain ⟨r,u,c,hu,hc,hR⟩:= w.sideRelease t z M h hw α hα
  let I:=Messenger q; let D:=num I; have hD : 0 ≤ D:=Nat.cast_nonneg _
  let β:= ε/(4*(D+1)*(r+1:ℝ)); let δ:=min u β
  have hd : 0<δ:= lt_min hu (show 0<β from by unfold β; positivity)
  have hδ : D*(r:ℝ)*δ ≤ ε/4 := by
    have hi : δ* (4*(D+1)*(r+1:ℝ)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
    have hh :  D*(r:ℝ) ≤ (D+1)*(r+1:ℝ) := mul_le_mul (by linarith) (by linarith)
      (by positivity) (by positivity)
    linarith only [hi,mul_le_mul_of_nonneg_right hh hd.le]
  have hq:=h.enter.first
  let k:ℝ:=min c (1/100)
  have hk:0<k:=lt_min hc (by norm_num)
  refine ⟨α,k/2,hα,half_pos hk,?_⟩
  let L:=2*netFact (trayPort p t)
  have hz:= (trend_sizes atTop (le_refl _) hq.hM).2
  have hX : ∀ᶠ n : ℕ in atTop,D*(L*bp (-((M*n:ℕ):ℝ)/2))≤ε/4 := by
    have heq:=((((bp_tendsto_zero (by norm_num: 0<(1/2:ℝ))).comp hz).const_mul L).const_mul D)
    have hx : ∀ᶠ n : ℕ in atTop,D*(L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ)))≤ ε/4 := heq.eventually
      (eventually_le_nhds (by rw [mul_zero,mul_zero]; positivity))
    filter_upwards [hx] with n hn; rw [show -((M*n:ℕ):ℝ)/2= -(1/2:ℝ)*((M*n:ℕ):ℝ) from by ring]
    exact hn
  filter_upwards [hR,hX,gauzeCalendar p r M h δ δ hd hd,pay_nat (a:=k) 2 (half_lt_self hk),
    hz.eventually (eventually_ge_atTop (2*num (Toast p)+1)),
    hz.eventually (eventually_ge_atTop (2*num (I×Toast p)+1))]
    with n hn hx hv he' hG hI N K m U hm H hH
  let W:=fun x=> ind (H x)
  obtain ⟨Y,hY⟩:=hn W (fun i=>(abs_of_nonneg (ind_nonneg (H i))).trans_le (ind_le_one _))
  let F:= w.flunk t z Y W m u α
  let Q i:= ¬gauze p δ δ Y m K i
  have h1 :pr U F≤bp (-c*n) := hY r Y (self_refine Y) _ _ hm
  have h2 :pr U Q ≤bp (-(1/100:ℝ)*n) := hv _ _ hm Y
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change 2*num (Messenger q×Toast p)+1 ≤ (N:ℝ) at hI; linarith only [hI]
  have ht : 2*num (Toast p)-(N:ℝ) ≤ -1 := by
    change _≤(N:ℝ) at hG; linarith only [hG]
  have h3 o (h :¬w.sober t z K H m α o) : F o ∨ Q o := by
    by_contra! hh
    obtain ⟨s,hg,hl⟩:= show ∃ s,w.steady t z m K s o∧ w.prowl s t z m o W<α from by
      unfold sober at h; push Not at h; exact h
    have hσ : gauze p δ δ Y m K o := not_not.mp hh.2
    have ht := w.sheen_hit t z m Y o s H hd hH hw hq.hR hm.age hg hhN ht
      (show D*(r*δ+L*bp (-(N:ℝ)/2))≤ε/2 by
        change _*(L*bp (-(N:ℝ)/2)) ≤_ at hx; linarith only [hx,hδ]) hσ
    refine hh.1 ⟨hg.frame,Station.gauzed_area _ _ _ _ hw δ (min_le_left ..)
      _ hσ,s,?_⟩
    rw [abs_sub_comm]
    refine lt_of_lt_of_le ?_ (le_abs_self _); unfold α W at *
    linarith only [ht,hl]
  have ht (x:ℝ) (hx : k≤x): bp (-x*n) ≤ bp (-k*n) := bp_le
    (mul_le_mul_of_nonneg_right (neg_le_neg hx) (Nat.cast_nonneg _))
  rw [two_mul] at he'
  have hg:=hm.drain.1
  exact ((pr_mono hg.nz h3).trans (pr_or_le hg.nz)).trans
    ((add_le_add (h1.trans (ht _ (min_le_left ..))) (h2.trans (ht _ (min_le_right ..)))).trans he')

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
