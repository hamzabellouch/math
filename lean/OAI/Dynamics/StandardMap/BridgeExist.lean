import OAI.Dynamics.StandardMap.BridgeGrid

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma aligned_intervals_eventually {R : ℕ} (s t : Fin R → DyadicTime)
    (hst : ∀ j,(s j:ℝ)<(t j:ℝ)) :
    ∀ᶠ p : ℕ in atTop, ∃ (a : Fin R → ℤ) (m : Fin R → ℕ),
      (∀ j,0< m j) ∧ (∀ j,((2^p:ℕ):ℝ)*(s j:ℝ)=(a j:ℝ)) ∧
      (∀ j,((2^p:ℕ):ℝ)*(t j:ℝ)=(a j:ℝ)+(m j:ℝ)) := by
  have he (j : Fin R) : ∀ᶠ p : ℕ in atTop,∃ a : ℤ,∃ m : ℕ,0< m ∧
      ((2^p:ℕ):ℝ)*(s j:ℝ)=(a:ℝ) ∧ ((2^p:ℕ):ℝ)*(t j:ℝ)=(a:ℝ)+(m:ℝ) := by
    obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually (s j) (t j) (hst j)
    filter_upwards [eventually_ge_atTop p₀] with p hp
    obtain ⟨a,m,hm,ha,hb⟩ := hp₀ p hp
    exact ⟨a,2*m,by omega,ha,by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb⟩
  filter_upwards [Filter.eventually_all.mpr he] with p hp
  choose a m hm ha hb using hp
  exact ⟨a,m,hm,ha,hb⟩
lemma exists_bridgeGrid {Rw Rh : ℕ} (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ))
    (sw tw : Fin Rw → DyadicTime) (sh th : Fin Rh → DyadicTime)
    (hw : ∀j,(sw j:ℝ)<(tw j:ℝ)) (hh : ∀j,(sh j:ℝ)<(th j:ℝ))
    (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hwl : ∀j,-((1:ℝ)/(2:ℝ)^q)≤(sw j:ℝ)-(u:ℝ))
    (hwr : ∀j,(tw j:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q)
    (hhl : ∀j,-((1:ℝ)/(2:ℝ)^q)≤(sh j:ℝ)-(v:ℝ))
    (hhr : ∀j,(th j:ℝ)-(v:ℝ)≤(1:ℝ)/(2:ℝ)^q) :
    ∃ B : BridgeGrid Rw Rh,B.u=u ∧ B.v=v ∧ B.sw=sw ∧ B.tw=tw ∧ B.sh=sh ∧ B.th=th := by
  have hlarge : ∀ᶠ p : ℕ in atTop,(100:ℝ)≤((2^p:ℕ):ℝ)*((v:ℝ)-(u:ℝ)) := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const (sub_pos.mpr huv)
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht.eventually_ge_atTop 100
  have huv' := aligned_intervals_eventually (fun _ : Fin 1 => u) (fun _ : Fin 1 => v) (fun _ => huv)
  obtain ⟨p,hpq,hpN,⟨aa,mm,hmm,haa,hmm'⟩,⟨aw,nw,hnw,haw,htw⟩,⟨ah,nh,hnh,hah,hth⟩⟩ :=
    (eventually_ge_atTop q |>.and (hlarge.and (huv'.and ((aligned_intervals_eventually sw tw hw).and
      (aligned_intervals_eventually sh th hh))))).exists
  let b := aa 0
  let N := mm 0
  let r := 2^(p-q)
  have hN : (N:ℝ)=((2^p:ℕ):ℝ)*((v:ℝ)-(u:ℝ)) := by
    have h1 := haa 0
    have h2 := hmm' 0
    dsimp [b,N] at *
    linarith
  have hr : (r:ℝ)=((2^p:ℕ):ℝ)*((1:ℝ)/(2:ℝ)^q) := by
    dsimp [r]
    push_cast
    rw [show p=q+(p-q) from (Nat.add_sub_of_le hpq).symm,pow_add]
    simp only [Nat.add_sub_cancel_left]
    field_simp
  have hpow : (0:ℝ)≤((2^p:ℕ):ℝ) := by positivity
  refine ⟨{
    p := p
    u := u
    v := v
    b := b
    N := N
    r := r

    large := ?_
    narrow := ?_
    hu := haa 0
    hv := hmm' 0,
    sw := sw
    tw := tw
    sh := sh
    th := th
    aw := fun j => aw j-b
    nw := nw
    ah := fun j => ah j-b
    nh := nh,
    pw := hnw
    ph := hnh
    hwleft := ?_
    hwright := ?_
    hhleft := ?_
    hhright := ?_,
    hsw := ?_
    htw := ?_
    hsh := ?_
    hth := ?_},rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact_mod_cast (by rw [hN]; exact hpN : (100:ℝ)≤N)
  · rw [hr,hN]
    nlinarith [mul_le_mul_of_nonneg_left hq hpow]
  · intro j
    have hb := haa 0
    have hj := haw j
    have h := mul_le_mul_of_nonneg_left (hwl j) hpow
    rw [mul_neg,←hr] at h
    exact_mod_cast (show -(r:ℝ)≤(aw j:ℝ)-(b:ℝ) by dsimp [b]; nlinarith)
  · intro j
    have hb := haa 0
    have hj := htw j
    have h := mul_le_mul_of_nonneg_left (hwr j) hpow
    rw [←hr] at h
    exact_mod_cast (show (aw j:ℝ)-(b:ℝ)+(nw j:ℝ)≤r by dsimp [b]; nlinarith)
  · intro j
    have hb := hmm' 0
    have hj := hah j
    have h := mul_le_mul_of_nonneg_left (hhl j) hpow
    rw [mul_neg,←hr] at h
    exact_mod_cast (show -(r:ℝ)≤(ah j:ℝ)-(b:ℝ)-(N:ℝ) by dsimp [b,N]; nlinarith)
  · intro j
    have hb := hmm' 0
    have hj := hth j
    have h := mul_le_mul_of_nonneg_left (hhr j) hpow
    rw [←hr] at h
    exact_mod_cast (show (ah j:ℝ)-(b:ℝ)+(nh j:ℝ)-(N:ℝ)≤r by dsimp [b,N]; nlinarith)
  · intro j; simpa only [sub_add_cancel] using haw j
  · intro j; simpa only [sub_add_cancel] using htw j
  · intro j; simpa only [sub_add_cancel] using hah j
  · intro j; simpa only [sub_add_cancel] using hth j
end StandardMapEntropy

end OAI
