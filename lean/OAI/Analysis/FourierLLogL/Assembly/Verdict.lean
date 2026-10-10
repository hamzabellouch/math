import OAI.Analysis.FourierLLogL.Assembly.Chill
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace CastShow
open Troupe

def holders (j : ℕ) := Finset.Ico 0 (mainIx j+2)
def picker (j M : ℕ) : Policy M := fun s => priciest s j true
def bouts (i _j : ℕ) (s : Scene M) := surcharge s true (i-1)
def aura (i : ℕ) (e : Event j M) := edgeFee (fun _ => i-1) true e

def upperFare (e : Event j M) :=
    10^140*(height j/Thermal.H j)*beginFee e+
      512*edgeFee (picker j M) false e+
      4*10^20*infoFee e + 10^40*Thermal.H j^40* (∑ i∈holders j, aura i e)

lemma stamp_upper (s : Scene M) (j : ℕ) :
    stamp s j ≤ 512*mutedR s j true + 10^20*fax s+
      10^40*Thermal.H j^40*(∑ i∈holders j,bouts i j s) := by
  let R := holders j; let n := mainIx j; let a := Thermal.H j
  let f (i) := bouts i j s
  have he : 1 ≤ a := H_ge j
  have hp : 0 < a := H_pos j
  have hi (i) : 0 ≤ f i := surcharge_nonneg _ _ _
  have HR : 0 ≤ ∑ i∈R,f i := Finset.sum_nonneg fun i _ => hi _
  let K := Finset.Ico 0 (n+1)
  have HH :
      ∑ i∈K, parody s i/depthRate i ≤ (10^6*a^40)*∑ i∈R, f i := by
    have he' : 0 ≤ 10^6*a^40 := by positivity
    apply le_trans (b:=(10^6*a^40)*∑ i∈K,f i)
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hv
      have hI : i ≤ n := by
        have hx : i < n+1 := (Finset.mem_Ico.mp hv).2; omega
      have Hx : parody s i ≤ 10^6*a^32*f i := parody_fee s j i (hI.trans (Nat.le_add_right _ _))
      have Hv := depth_rate_fee i j hI
      rw [div_eq_mul_one_div]
      apply le_trans (mul_le_mul Hx Hv (by have := (rate_easy i).1; positivity)
        (by have := hi i; positivity)); change 10^6*a^32*f i*a^8 ≤ _
      exact le_of_eq (by ring)
    · apply mul_le_mul_of_nonneg_left _ he'
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hi i
      unfold K R holders n; intro i hi
      obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hi; exact Finset.mem_Ico.mpr ⟨ha,by omega⟩
  have HK : f (n+1) ≤ ∑ i∈R,f i := Finset.single_le_sum (fun i _ => hi i)
    (Finset.mem_Ico.mpr ⟨by omega,by unfold n; omega⟩)
  have HT : parody s (n+1) ≤ (10^6*a^40)*∑ i∈R, f i := by
    apply (parody_fee s j (n+1) le_rfl).trans
    change 10^6*a^32*f (n+1) ≤ _
    gcongr <;> first| omega| apply hi
  unfold stamp stampAux
  change _ + (4*parody s (n+1)+10^20*(fax s+∑ i∈K,_)) ≤ _+_+10^40*a^40*(∑ i∈R,f i)
  nlinarith [mul_nonneg (show 0 ≤ a^40 by positivity) HR]

private lemma bound_bit (s : Scene M) (k : Bool)
    (h : Safe s j J f) (he : s.live=true) (hp : work s j J f) :
    let b := Event.march s (Turn.move (j:=j)) k
    billOf b ≤ upperFare b := by
  intro b
  unfold b upperFare
  let r := s.norm/s.mass
  have ht : normStamp s j=r*stamp s j := ite_eq_left he
  have h1 : edgeFee (picker j M) false b=r*mutedR s j true := by
    unfold b edgeFee toll
    simp only [true_and,ite_eq_left hp.2.2, r, picker,mutedR]
  have h2 (i) : aura i b=r*bouts i j s := by
    unfold aura b edgeFee toll
    simp only [true_and,ite_eq_left hp.2.2,r,bouts]
  have HH : 0 ≤ r := div_nonneg h.norm_ok h.mass_lower
  change normStamp s j ≤ _*0+512*edgeFee (picker j M) false b+
    4*10^20*(1/4*r*fax s)+ 10^40* Thermal.H j^40*(∑ i∈holders j,aura i b)
  simp_rw [h2,h1,ht,← Finset.mul_sum]
  apply le_trans (mul_le_mul_of_nonneg_left (stamp_upper s j) HH)
  exact le_of_eq (by ring)

lemma short_trace_bound (t : Play j M s) (h : t.Follows J f) (he : s.live=true) :
    let v := trace false t
    v.flatFee billOf ≤ v.flatFee upperFare := by
  induction t with
  | rest s => simp only [trace,flat_finish,le_refl]
  | freeze s t ih =>
    intro v
    change flatFee (.finish s true : Road j M s) billOf ≤ flatFee (.finish s true) upperFare
    rw [flat_finish,flat_finish]
  | ticket s t ih =>
    simp only [trace,flat_push]
    apply add_le_add _ (ih h.2.2.2.2 he)
    unfold upperFare billOf beginFee edgeFee infoFee gateTax
    have H : ∀ i, aura i (.pace s .renew : Event j M)=0 := fun i => rfl
    simp only [H,reset,he,↓reduceIte,Finset.sum_const_zero]
    exact le_of_eq (by ring)
  | jump s l r il ir =>
    simp only [trace, flat_fork _ _ (traced _ false h)]
    apply Ex_mono; intro b
    apply add_le_add (bound_bit s b h.1 he h.2.1)
    cases b
    exact il h.2.2.2.1 he
    exact ir h.2.2.2.2 he
  | attempt s u l r il ir =>
    simp only [trace,flat_fork _ _ (traced _ false h)]
    apply Ex_mono; intro b
    apply add_le_add
    · have H : ∀ i, aura i (.march s (.ask u) b)=0 := fun i => rfl
      simp [upperFare,H,beginFee,edgeFee,infoFee,billOf]
    · cases b; exact il h.2.2.2.2.1 he; exact ir h.2.2.2.2.2 he

lemma linear_fee (t : Road j M s) (A B : Event j M → ℝ) (a : ℝ) :
    flatFee t (fun i => A i+B i)=flatFee t A+flatFee t B ∧
      flatFee t (fun i => a*A i)=a*flatFee t A := by
  have HE (l : List (Event j M)) :
      (l.map (fun i => A i+B i)).sum=(l.map A).sum+(l.map B).sum ∧
      (l.map (fun i => a*A i)).sum=a*(l.map A).sum := by
    induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons,List.sum_cons, ih.1, ih.2]
      constructor <;> ring
  constructor
  · unfold flatFee expHike Journal.fee; simp_rw [(HE _).1, Ex_add]
  unfold flatFee expHike Journal.fee; simp_rw [(HE _).2, Ex_lmul]

lemma sum_fee (t : Road j M s) (p : Finset ℕ) (f : ℕ → Event j M → ℝ) :
    t.flatFee (fun i => ∑ z∈p,f z i)=∑ z∈p,t.flatFee (f z) := by
  induction p using Finset.induction_on with
  | empty =>
    have H (s : Journal j M) : s.fee (fun _ => 0)=0 := by
      unfold Journal.fee; induction s.events with
      | nil => simp
      | cons a l ih => simp
    simp only [Finset.sum_empty,flatFee,expHike,H,Ex_const]
  | @insert a p ha ih =>
    simp only [Finset.sum_insert ha]
    rw [(linear_fee t (f a) (fun i => _) 0).1,ih]

lemma upper_total :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ,
      (∀ x,f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, t.Trusted J f → 1/Thermal.H j ≤ s.mass →
        t.flatFee upperFare ≤ 10^190*height j := by
  filter_upwards [global_edges, fisher_bound, final_coarse,hpoly 1 42] with j he hq ht hk
    M J f hF s t h hp
  let a := Thermal.H j; let d := height j; let phi := t.flatFee
  let x := limitC
  obtain ⟨H1,H2⟩ := he M J f hF t h hp
  have H₃ := hq M J f hF t h hp
  have H₄ := (ht M J s f t h hp).2.2 rfl
  let R := holders j
  have HH : ∑ i∈R,phi (aura i) ≤ 300000*x*a^2 := by
    calc
      _ ≤ ∑ _i∈R,10000*x*a := Finset.sum_le_sum fun i hi => by
        have hh := (Finset.mem_Ico.mp hi).2
        apply H2
        unfold testIx; omega
      _ ≤ _ := by
        unfold R holders
        simp only [Finset.sum_const,Nat.card_Ico,Nat.sub_zero,nsmul_eq_mul]
        have he : ((mainIx j:ℕ):ℝ) ≤ 19*a := (main_bounds j (Nat.le_add_right _ 3)).2.1
        push_cast
        have HX : 1 ≤ a := H_ge _
        unfold x limitC; nlinarith
  let f₁ := edgeFee (picker j M) false (j:=j)
  let C := 10^140*(d/a)
  let Y := 10^40*a^40
  have HY : 0 ≤ C ∧ 0 ≤ Y := by
    have hi : 0 < a := H_pos _
    have hh : 0 < d := d_pos j
    unfold C Y; constructor <;> positivity

  have HE (A B : Event j M → ℝ) : phi (fun i => A i+B i)=phi A+phi B := (linear_fee t A B 1).1
  have HM (A : Event j M → ℝ) (c : ℝ) : phi (fun i => c*A i)=c*phi A := (linear_fee t A A c).2
  have H := H1 (picker j M)
  unfold upperFare
  change phi (fun e => C*beginFee e+512*f₁ e+4*10^20*infoFee e + Y*(∑ i∈R,aura i e)) ≤ _
  simp_rw [HE (fun _ => _) (fun _ => _),HM]
  rw [show phi (fun e => ∑ i∈R,aura i e) = ∑ i∈R,phi (aura i) from sum_fee t R aura]
  have Ha : 1 ≤ a := H_ge _
  have hd : 0 ≤ d := (d_pos j).le
  change phi f₁ ≤ 1000*d at H
  change phi infoFee ≤ x*d at H₃
  change phi beginFee ≤ 100*x*a at H₄
  have HZ : a^42 ≤ d := by simpa using hk
  have HC : C*(100*x*a) ≤ 10^180*d := by
    have He : 0<a := by linarith
    unfold x limitC C
    rw [show 10^140*(d/a)*(100*10^30*a)=10^172*d by field_simp; ring]
    linarith
  have HL : Y*(300000*x*a^2) ≤ 10^78*d := by
    apply le_trans _ (mul_le_mul_of_nonneg_left HZ (by norm_num : (0:ℝ)≤10^78))
    unfold Y x limitC
    nlinarith [pow_nonneg (lt_of_lt_of_le zero_lt_one Ha).le 42]
  change _ ≤ 10^190*d
  have HH' := mul_le_mul_of_nonneg_left HH HY.2
  have H₄' := mul_le_mul_of_nonneg_left H₄ HY.1
  unfold x limitC at *
  linarith

end CastShow


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
