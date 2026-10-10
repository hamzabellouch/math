import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.HighNumerics
import OAI.Combinatorics.RamseyFive.Trees.IntegerWindows

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking
open scoped Topology
noncomputable section

lemma reciprocal_drop_ratio {σ D η w G C : ℝ} (hη : 0<η) (hσ : 1≤σ)
    (hD : σ^beta η≤D) (hw : 0≤w) (hC : 0≤C)
    (hG : G≤C*w*D*σ^(3*beta η)) :
    (G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η))≤
      w*((C+4+2*Real.log 64)*σ^(-3*beta η)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hb:=beta_pos hη
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hDp : 0<D := by linarith
  have hp3 : 1≤σ^(3*beta η) := Real.one_le_rpow hσ (by positivity)
  have hp23 : σ^(2*beta η)≤σ^(3*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hl : 0≤Real.log 64 := Real.log_nonneg (by norm_num)
  have hbig : 1≤D*σ^(3*beta η) := (by nlinarith : 1≤D*σ^(3*beta η))
  have hlog : Real.log 64≤D*σ^(3*beta η)*Real.log 64 := by nlinarith
  calc
    _ ≤ ((C+4+2*Real.log 64)*w*D*σ^(3*beta η))/(D*σ^(6*beta η)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hp23 (show 0≤4*w*D by positivity),
        mul_le_mul_of_nonneg_left hlog (show 0≤2*w by positivity)]
    _ =w*((C+4+2*Real.log 64)*(σ^(3*beta η)/σ^(6*beta η))) := by field_simp
    _ =_ := by rw [←Real.rpow_sub hs];congr 3;ring

lemma eventually_reciprocal_drop_fraction {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ D w G : ℝ,σ^beta η≤D→0≤w→
      G≤C*w*D*σ^(3*beta η)→
      (G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η))≤w*δ := by
  have hb : 0<3*beta η := by have:=beta_pos hη;positivity
  have ht : Tendsto (fun σ : ℝ=>(C+4+2*Real.log 64)*σ^(-3*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop hb).const_mul (C+4+2*Real.log 64)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hδ] with σ hσ ht
  intro D w G hD hw hG
  exact (reciprocal_drop_ratio hη hσ hD hw hC hG).trans (mul_le_mul_of_nonneg_left ht.le hw)

lemma open_gap_scale {σ D η c w : ℝ} (hη : 0<η) (hσ : 1≤σ) (hc : 0<c)
    (hw : 0≤w) (hD : 0≤D) (hlo : c*σ^(1+η/2)≤w*D) :
    3*σ≤(3/c)*w*D*σ^(3*beta η) := by
  have hb:=beta_pos hη
  have hp : σ≤σ^(1+η/2) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlo (by positivity : 0≤3/c)
  have hcancel : (3/c)*(c*σ^(1+η/2))=3*σ^(1+η/2) := by field_simp
  rw [hcancel] at hh
  calc
    3*σ≤3*σ^(1+η/2) := by linarith
    _ ≤(3/c)*(w*D) := hh
    _ ≤(3/c)*(w*D)*σ^(3*beta η) := le_mul_of_one_le_right (by positivity)
        (Real.one_le_rpow hσ (by positivity))
    _ =_ := by ring

lemma reciprocal_integer_pack {η c σ q D : ℝ} {m : ℕ}
    (hη : 0<η) (hc : 0<c) (hσ : 1≤σ) (hqp : 0<q) (hq : 2≤q)
    (hD1 : 1≤D) (hDhi : D≤σ^(1-η/2))
    (hlen : c*q*σ^(1+η)≤ m) (hm : (m:ℝ)≤q*σ^(1+η)) (hm4 : 4≤ m)
    (hfit : 8/c≤σ^η) (hTopen : σ^(-(η/2-3000*beta η))<1/4)
    (hTclosed : ∀D : ℝ,D≤σ^(1-η/2)→D*σ^(3000*beta η)≤(c/16)*σ)
    (hwbig : σ^(1+η/2)≤σ^2) (closed : Bool) :
    ∃w n : ℕ, 0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
      (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
      (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
      (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
      2*(q*D*σ^(3000*beta η))≤n := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := by linarith
  have hsig : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have powadd (a b : ℝ) : σ^a*σ^b=σ^(a+b) := (Real.rpow_add hp _ _).symm

  cases closed with
  | true =>
      obtain ⟨hn,hpack,hlo,hhi⟩:=integral_window_packing m 1 (by norm_num) (by simpa using hm4)
      simp only [mul_one] at hn hpack hlo hhi
      refine ⟨1,m/4,by norm_num,hn,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa only [Nat.one_mul,Nat.mul_comm] using hpack
      · simpa only [Nat.cast_one,one_mul,mul_one] using (show (m:ℝ)≤8*(m/4:ℕ) by linarith)
      · simp only [Nat.cast_one,one_mul]
        exact hDhi.trans (Real.rpow_le_rpow_of_exponent_le hσ (by linarith))
      · simp only [Nat.cast_one]
        nlinarith
      · intro _
        nlinarith
      · intro hh
        contradiction
      · have hx:=mul_le_mul_of_nonneg_left (hTclosed D hDhi) hqp.le
        have hh:=mul_le_mul_of_nonneg_left hsig (show 0≤c*q/16 by positivity)
        nlinarith
  | false =>
      have ha1 : 1≤σ^(η/2) := Real.one_le_rpow hσ (by positivity)
      have hx : 2≤q*D*σ^(η/2) := by
        have hqd : 2≤q*D := by nlinarith
        nlinarith
      have hfit' : 8*(q*D*σ^(η/2))≤(m:ℝ) := by
        have hd : D*σ^(η/2)≤σ := by
          calc
            _ ≤σ^(1-η/2)*σ^(η/2) := mul_le_mul_of_nonneg_right hDhi (by positivity)
            _ =σ := by rw [powadd];rw [show 1-η/2+η/2=(1:ℝ) by ring,Real.rpow_one]
        have hcσ : 8≤c*σ^η := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hfit
        have hmlo : 8*q*σ≤c*q*σ^(1+η) := by
          rw [Real.rpow_add hp,Real.rpow_one]
          nlinarith [mul_le_mul_of_nonneg_right hcσ (show 0≤q*σ by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hd hqp.le]
      obtain ⟨hn,hw,hpack,hlo,hwlo,hwhi⟩:=integer_window_length hqp hDp
        (Real.rpow_pos_of_pos hp (η/2)) hx m rfl hfit'
      let n:=⌊q*D*σ^(η/2)⌋₊
      let w:=m/(4*n)
      have hlo' : (c/8)*σ^(1+η/2)≤(w:ℝ)*D := by
        apply le_trans _ hwlo
        apply (le_div_iff₀ (by positivity : 0<8*q*σ^(η/2))).mpr
        have heq : (c/8)*σ^(1+η/2)*(8*q*σ^(η/2))=c*q*σ^(1+η) := by
          calc
            _ =c*q*(σ^(1+η/2)*σ^(η/2)) := by ring
            _ =_ := by rw [powadd];congr 2;ring
        rwa [heq]
      have hhi' : (w:ℝ)*D≤σ^(1+η/2) := by
        apply hwhi.trans
        apply (div_le_iff₀ (by positivity : 0<2*q*σ^(η/2))).mpr
        have heq : σ^(1+η/2)*(2*q*σ^(η/2))=2*q*σ^(1+η) := by
          calc
            _ =2*q*(σ^(1+η/2)*σ^(η/2)) := by ring
            _ =_ := by rw [powadd];congr 2;ring
        rw [heq]
        nlinarith
      refine ⟨w,n,hw,hn,hpack,by linarith,hhi',?_,?_,fun _=>hlo',?_⟩
      · have hh:(w:ℝ)≤(w:ℝ)*D := le_mul_of_one_le_right (by positivity) hD1
        exact hh.trans (hhi'.trans hwbig)
      · intro hh
        contradiction
      · have hnlo:=(integral_floor_half hx).2.1
        have hexp : σ^(3000*beta η)=σ^(-(η/2-3000*beta η))*σ^(η/2) := by
          rw [powadd];congr 1;ring
        have ht : 4*σ^(3000*beta η)≤σ^(η/2) := by
          rw [hexp]
          nlinarith [mul_le_mul_of_nonneg_right hTopen.le (Real.rpow_nonneg hp.le (η/2))]
        have hh:=mul_le_mul_of_nonneg_left ht (show 0≤q*D by positivity)
        dsimp only [n]
        nlinarith

theorem eventually_reciprocal_packing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D : ℝ) (m : ℕ),2≤q→σ^beta η≤D→D≤σ^(1-η/2)→
      c*q*σ^(1+η)≤ m→(m:ℝ)≤q*σ^(1+η)→∀closed : Bool,
      ∃ (w n rounds rem : ℕ),
        0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
        (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
        (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
        (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
        0<rounds ∧ 0<rem ∧ n≤2*rem ∧ rem+rounds≤n ∧
        q*D*σ^(3000*beta η)/2≤rounds ∧ (n:ℝ)/2≤rem := by
  have hb:=beta_pos hη
  have he : 0<η/2-3000*beta η := by unfold beta;linarith
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2/c),
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (8/c)),
    (tendsto_rpow_neg_atTop he).eventually_lt_const (by norm_num : (0:ℝ)<1/4),
    eventually_stage_scale hη 3000 (c/16) (by unfold beta;linarith) (by positivity)]
    with σ hσ hσc hfit hTopen hTclosed
  intro q D m hq hD hDhi hlen hm closed
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 0<q := by linarith
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hDp : 0<D := by linarith
  have hpow1 : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hsig : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hm4 : 4≤ m := by
    have hsc : 2≤c*σ := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hσc
    have : (4:ℝ)≤ m := by nlinarith [mul_le_mul_of_nonneg_left hsig (mul_nonneg hc.le hqp.le)]
    exact_mod_cast this
  have hlarge : 2≤q*D*σ^(3000*beta η) := by
    have hx : 1≤σ^(3000*beta η) := Real.one_le_rpow hσ (by positivity)
    have hqd : 2≤q*D := by nlinarith
    nlinarith
  have powadd (a b : ℝ) : σ^a*σ^b=σ^(a+b) := (Real.rpow_add hp _ _).symm
  have hwbig : σ^(1+η/2)≤σ^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hpack:=reciprocal_integer_pack hη hc hσ hqp hq hD1 hDhi hlen hm hm4
    hfit hTopen hTclosed hwbig closed
  obtain ⟨w,n,hw,hn,hpack,hlo,hhi,hw2,hclosed,hopen,hTn⟩:=hpack
  obtain ⟨hT,hr,h2r,hroom,hrem,hTlo⟩:=integral_round_packing hlarge n hTn
  exact ⟨w,n,⌊q*D*σ^(3000*beta η)⌋₊,n-⌊q*D*σ^(3000*beta η)⌋₊,
    hw,hn,hpack,hlo,hhi,hw2,hclosed,hopen,hT,hr,h2r,hroom,hTlo,hrem⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
