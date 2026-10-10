import OAI.Combinatorics.PerfectMatching.CompletePairs

namespace OAI

section

namespace BinaryMatching
noncomputable section
open Finset MatchingEntropy
variable {n : ℕ}

lemma degree_add (x z : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+z e) v=
      (completeGraph n).degree x v+(completeGraph n).degree z v := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).degree_linear x z 1 1 v

lemma cut_add (x z : Pair n → ℝ) (S : Finset (Fin n)) :
    (completeGraph n).cutMass (fun e => x e+z e) S=
      (completeGraph n).cutMass x S+(completeGraph n).cutMass z S := by
  simpa only [one_smul,one_mul,Pi.add_def] using (completeGraph n).cutMass_linear x z 1 1 S

lemma cut_bound {z : Pair n → ℝ} {b : ℝ} (hb : 0≤b) (hz : ∀ e, |z e|≤b)
    (S : Finset (Fin n)) : |(completeGraph n).cutMass z S|≤Fintype.card (Pair n)*b := by
  calc
    _ ≤ ∑ e∈(completeGraph n).cut S, |z e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e∈(completeGraph n).cut S, b := sum_le_sum (fun e _ => hz e)
    _ = ((completeGraph n).cut S).card*b := by simp
    _ ≤ Fintype.card (Pair n)*b := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hb

def degreeCorrection (x : Pair n → ℝ) (e : Pair n) : ℝ :=
  let d := fun v => 1-(completeGraph n).degree x v
  (d e.val.1+d e.val.2)/((n:ℝ)-2)-(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))

lemma correction_degree (hn : 4≤n) (x : Pair n → ℝ) (v : Fin n) :
    (completeGraph n).degree (fun e => x e+degreeCorrection x e) v=1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : (n:ℝ)-2≠0 := by linarith
  have h1 : (n:ℝ)-1≠0 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  rw [degree_add]
  have hc : degreeCorrection x = ((n:ℝ)-2)⁻¹ • (fun e : Pair n => d e.val.1+d e.val.2) +
      (-1:ℝ) • (fun _ => (∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))) := by
    funext e; simp only [degreeCorrection,d,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  rw [hc,(completeGraph n).degree_linear,degree_vertex_add,degree_constant]
  dsimp [d]
  field_simp
  ring

lemma correction_bound (hn : 4≤n) {x : Pair n → ℝ} {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w) (e : Pair n) :
    |degreeCorrection x e|≤2*w := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have h2 : 0<(n:ℝ)-2 := by linarith
  have h1 : 0<(n:ℝ)-1 := by linarith
  let d := fun v => 1-(completeGraph n).degree x v
  have hd (v) : |d v|≤w := by dsimp [d]; rw [abs_sub_comm]; exact hdeg v
  have hsum : |∑ v,d v|≤(n:ℝ)*w := by
    calc
      _ ≤ ∑ v,|d v| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n,w := sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  have ha : |(d e.val.1+d e.val.2)/((n:ℝ)-2)|≤w := by
    rw [abs_div,abs_of_pos h2,div_le_iff₀ h2]
    have hh := abs_add_le (d e.val.1) (d e.val.2)
    nlinarith [hd e.val.1,hd e.val.2]
  have hb : |(∑ v,d v)/(((n:ℝ)-2)*((n:ℝ)-1))|≤w := by
    rw [abs_div,abs_of_pos (mul_pos h2 h1),div_le_iff₀ (mul_pos h2 h1)]
    have hp : (n:ℝ)≤((n:ℝ)-2)*((n:ℝ)-1) := by nlinarith
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hp hw])
  exact (abs_sub _ _).trans (by dsimp [degreeCorrection] at *; linarith [ha,hb])

def uniform (n : ℕ) : Pair n → ℝ := fun _ => 1/((n:ℝ)-1)

lemma uniform_box (hn : 4≤n) (e : Pair n) : uniform n e∈Set.Icc (0:ℝ) 1 := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (by norm_num) (by linarith)
  · exact (div_le_one (by linarith)).2 (by linarith)

lemma uniform_degree (hn : 4≤n) (v : Fin n) :
    (completeGraph n).degree (uniform n) v=1 := by
  unfold uniform
  rw [degree_constant]
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  field_simp [show (n:ℝ)-1≠0 by linarith]

def TrivialCut (S : Finset (Fin n)) : Prop := S.card=1 ∨ Sᶜ.card=1

lemma trivial_cut_degree {x : Pair n → ℝ} (hx : ∀ v,(completeGraph n).degree x v=1)
    {S : Finset (Fin n)} (hS : TrivialCut S) : (completeGraph n).cutMass x S=1 := by
  rcases hS with h|h
  · obtain ⟨v,rfl⟩ := card_eq_one.mp h
    simpa using hx v
  · obtain ⟨v,hv⟩ := card_eq_one.mp h
    have he : (completeGraph n).cutMass x S=(completeGraph n).cutMass x Sᶜ := by
      simp only [LooplessGraph.cutMass,LooplessGraph.cut_compl]
    rw [he,hv,LooplessGraph.cutMass_singleton,hx]

lemma uniform_nontrivial_cut (heven : Even n) {S : Finset (Fin n)} (hodd : Odd S.card)
    (hS : ¬TrivialCut S) : (3/2:ℝ)≤(completeGraph n).cutMass (uniform n) S := by
  have hcards : S.card+Sᶜ.card=n := by simp
  have ha : 3≤S.card := by
    have ho := Nat.odd_iff.mp hodd
    have hh : S.card≠1 := fun h => hS (Or.inl h)
    omega
  have hb : 3≤Sᶜ.card := by
    have ho := Nat.odd_iff.mp hodd
    have he := Nat.even_iff.mp heven
    have hh : Sᶜ.card≠1 := fun h => hS (Or.inr h)
    omega
  have ha' : (3:ℝ)≤S.card := by exact_mod_cast ha
  have hb' : (3:ℝ)≤Sᶜ.card := by exact_mod_cast hb
  have hc' : (S.card:ℝ)+Sᶜ.card=n := by exact_mod_cast hcards
  have hn : (6:ℝ)≤n := by linarith
  unfold uniform
  rw [cut_constant]
  rw [mul_one_div,le_div_iff₀ (by linarith : 0<(n:ℝ)-1)]
  have hp := mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')
  nlinarith

lemma uniform_feasible (hn : 4≤n) (heven : Even n) :
    uniform n∈(completeGraph n).polytope := by
  rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
  refine ⟨fun e => (uniform_box hn e).1,uniform_degree hn,?_⟩
  intro S hS
  by_cases ht : TrivialCut S
  · rw [trivial_cut_degree (uniform_degree hn) ht]
  · linarith [uniform_nontrivial_cut heven hS ht]

theorem feasibility_repair (hn : 4≤n) (heven : Even n) {x : Pair n → ℝ}
    (hx : ∀ e,x e∈Set.Icc (0:ℝ) 1) {w : ℝ} (hw : 0≤w)
    (hdeg : ∀ v, |(completeGraph n).degree x v-1|≤w)
    (hcut : ∀ S : Finset (Fin n),Odd S.card → 1-w≤(completeGraph n).cutMass x S) :
    ∃ y∈(completeGraph n).polytope,∀ e,|y e-x e|≤(2+10*(n:ℝ)^2)*w := by
  let A : ℝ := 10*(n:ℝ)^2
  let c := degreeCorrection x
  let x' := fun e => x e+c e
  let t := min 1 (A*w)
  let y : Pair n → ℝ := (1-t) • x'+t • uniform n
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤t := le_min (by norm_num) (mul_nonneg hA hw)
  have ht1 : t≤1 := min_le_left _ _
  have htw : t≤A*w := min_le_right _ _
  have hc := correction_bound hn hw hdeg
  have hx'd := correction_degree hn x
  have hx'lo (e) : -2*w≤x' e := by
    have hh := (abs_le.mp (hc e)).1
    dsimp [x',c]; linarith [(hx e).1]
  have hx'cut (S) (hS : Odd S.card) :
      1-(1+2*(Fintype.card (Pair n):ℝ))*w≤(completeGraph n).cutMass x' S := by
    have hh := (abs_le.mp (cut_bound (mul_nonneg (by norm_num) hw) hc S)).1
    dsimp [x',c]; rw [cut_add]
    linarith [hcut S hS]
  have hA1 : 2≤A/((n:ℝ)-1) := by
    apply (le_div_iff₀ (by linarith)).2
    dsimp [A]; nlinarith
  have hA2 : 1+2*(Fintype.card (Pair n):ℝ)≤A/2 := by
    have hq : (Fintype.card (Pair n):ℝ)≤(n:ℝ)^2 := by exact_mod_cast q_le_square (n:=n)
    dsimp [A]; nlinarith
  have hyd : ∀ v,(completeGraph n).degree y v=1 := by
    intro v; dsimp [y]; rw [LooplessGraph.degree_linear,hx'd,uniform_degree hn]; ring
  have hy : y∈(completeGraph n).polytope := by
    by_cases hbig : 1≤A*w
    · have htt : t=1 := min_eq_left hbig
      simpa only [y,htt,sub_self,zero_smul,one_smul,zero_add] using uniform_feasible hn heven
    · have htt : t=A*w := min_eq_right (le_of_not_ge hbig)
      rw [(completeGraph n).polytope_eq_constraints (by simpa using heven)]
      refine ⟨?_,hyd,?_⟩
      · intro e
        have h0 := mul_le_mul_of_nonneg_left (hx'lo e) (sub_nonneg.mpr ht1)
        have h1 := mul_le_mul_of_nonneg_right hA1 hw
        change 0≤(1-t)*x' e+t*uniform n e
        unfold uniform
        rw [htt] at *
        simp only [div_eq_mul_inv] at h1 ⊢
        nlinarith [mul_nonneg ht hw]
      · intro S hS
        by_cases htr : TrivialCut S
        · rw [trivial_cut_degree hyd htr]
        · have h0 := mul_le_mul_of_nonneg_left (hx'cut S hS) (sub_nonneg.mpr ht1)
          have h1 := mul_le_mul_of_nonneg_left (uniform_nontrivial_cut heven hS htr) ht
          have h2 := mul_le_mul_of_nonneg_right hA2 hw
          dsimp [y]; rw [LooplessGraph.cutMass_linear]
          have hqw : 0≤(1+2*(Fintype.card (Pair n):ℝ))*w := by positivity
          rw [htt] at *
          nlinarith [mul_nonneg ht hqw]
  refine ⟨y,hy,fun e => ?_⟩
  have hu : |uniform n e-x e|≤1 := by
    rw [abs_le]; constructor <;> linarith [(uniform_box hn e).1,(uniform_box hn e).2,(hx e).1,(hx e).2]
  have he : y e-x e=(1-t)*c e+t*(uniform n e-x e) := by dsimp [y,x']; ring
  rw [he]
  calc
    _ ≤ |(1-t)*c e|+|t*(uniform n e-x e)| := abs_add_le _ _
    _ = (1-t)*|c e|+t*|uniform n e-x e| := by rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*(2*w)+t*1 := add_le_add (mul_le_mul_of_nonneg_left (hc e) (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hu ht)
    _ ≤ (2+10*(n:ℝ)^2)*w := by dsimp [A] at htw; nlinarith [mul_nonneg ht hw]

end
end BinaryMatching
end

end OAI
