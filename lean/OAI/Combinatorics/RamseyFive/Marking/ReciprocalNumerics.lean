import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalLevelProducer

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Asymptotics Real
open scoped Topology
noncomputable section

lemma reciprocal_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
      Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b)) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne']
    rw [←Real.rpow_sub hσp]
    congr 1
    ring
  have hc := div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos hσp _) hs
  unfold reciprocalBadMass
  rw [mul_div_assoc,add_div,he]
  exact add_le_add (Real.exp_le_exp.mpr (neg_le_neg hs))
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (by norm_num))

lemma reciprocal_core_uniform {σ D b C : ℝ} (hσ : 1≤σ) (hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
      2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
    2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+
      2*(Real.log σ/σ^(3*b)))+
      2*Real.exp 1*(Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne',←Real.rpow_sub hσp]
    congr 1
    ring
  have hl : Real.log (5*σ+1)≤Real.log 6+Real.log σ := by
    rw [←Real.log_mul (by norm_num : (6:ℝ)≠0) hσp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hn : 0≤Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1) := by
    have := Real.log_nonneg hσ
    positivity
  have hd := div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hσp _) hs
  have hl' : (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      (Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b)) := by
    calc
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/(D*σ^(2*b)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/σ^(3*b) := hd
      _ = _ := by ring
  have hf : 2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b))) := by
    calc
      _ = 2*((D*σ^b)/(D*σ^(2*b))+
        (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))) := by ring
      _ ≤ _ := by rw [he];linarith
  exact add_le_add hf (mul_le_mul_of_nonneg_left (reciprocal_bad_uniform hσ hb hD hC) (by positivity))

theorem eventually_reciprocal_endpoints {b : ℝ} (hb : 0<b) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀ D : ℝ,σ^b≤D→
      reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤ε ∧
      2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤1/2 := by
  have ht := tendsto_rpow_neg_atTop hb
  have h3 : 0<3*b := by positivity
  have hn := tendsto_rpow_neg_atTop h3
  have hc : Tendsto (fun σ : ℝ=>C/σ^(3*b)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop C
  have he : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h3)
  have hbad : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) atTop (𝓝 0) := by
    simpa using he.add ((ht.add hc).const_mul 50)
  have hc' : Tendsto (fun σ : ℝ=>(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b))
      atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop (Real.log 32+Real.log 33+2*(Real.log 6+1))
  have hl := (isLittleO_log_rpow_atTop h3).tendsto_div_nhds_zero
  have hcore := (((ht.add hc').add (hl.const_mul 2)).const_mul 2).add (hbad.const_mul (2*Real.exp 1))
  simp only [add_zero,mul_zero] at hcore
  filter_upwards [eventually_ge_atTop (1:ℝ),hbad.eventually_lt_const hε,
    hcore.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ he hc
  intro D hD
  exact ⟨(reciprocal_bad_uniform hσ hb hD hC).trans he.le,
    (reciprocal_core_uniform hσ hb hD hC).trans hc.le⟩

def publicRetentionError (σ b H : ℝ) : ℝ :=
  let q:=Real.exp σ
  let ε:=σ^(-2000*b)/q
  H*(20*H*(50*q/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*(320016*ε)+
    (q/(σ^(-1000*b)))*(4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-q))+
    (20*H+2)*(50*q/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*(160008*ε)

def publicRetentionEnvelope (σ b : ℝ) : ℝ :=
  (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)*σ^(-1998*b)+
    ((4*Real.exp 1)^2*320016)*σ^(-999*b)+5*(σ^b*Real.exp (-σ))+
    (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-1999*b)+
    (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-2000*b)

lemma publicRetentionError_bound {σ b H : ℝ} (hσ : 1≤σ) (hH : 0≤H) (hH' : H≤σ^b) :
    publicRetentionError σ b H≤publicRetentionEnvelope σ b := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hEq : 0<Real.exp σ := Real.exp_pos _
  have hpow : 0<σ^(-1000*b) := Real.rpow_pos_of_pos hp _
  have hε : 0≤σ^(-2000*b)/Real.exp σ := by positivity
  have hmax : publicRetentionError σ b H≤publicRetentionError σ b (σ^b) := by
    unfold publicRetentionError
    dsimp only
    apply add_le_add
    · apply mul_le_mul hH' _ (by positivity) (by positivity)
      apply add_le_add _ le_rfl
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hH' (by norm_num)) (by positivity)) (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity))
        (by positivity)
  have he : Real.exp (-Real.exp σ)≤Real.exp (-σ) := by
    apply Real.exp_le_exp.mpr
    have := Real.add_one_le_exp σ
    linarith
  have hr1 : σ^b*σ^b*σ^(-2000*b)=σ^(-1998*b) := by
    rw [←Real.rpow_add hp,←Real.rpow_add hp]
    congr 1
    ring
  have hr2 : σ^b/σ^(-1000*b)*σ^(-2000*b)=σ^(-999*b) := by
    rw [←Real.rpow_sub hp,←Real.rpow_add hp]
    congr 1
    ring
  have hr3 : σ^b*σ^(-2000*b)=σ^(-1999*b) := by
    rw [←Real.rpow_add hp]
    congr 1
    ring
  have hrewrite : publicRetentionError σ b (σ^b)=
      (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)*σ^(-1998*b)+
      ((4*Real.exp 1)^2*320016)*σ^(-999*b)+5*(σ^b*Real.exp (-Real.exp σ))+
      (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-1999*b)+
      (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-2000*b) := by
    rw [←hr1,←hr2,←hr3]
    unfold publicRetentionError
    field_simp
    ring
  apply hmax.trans
  rw [hrewrite]
  unfold publicRetentionEnvelope
  have hh:=mul_le_mul_of_nonneg_left he (le_of_lt (Real.rpow_pos_of_pos hp b))
  linarith

lemma publicRetentionEnvelope_tendsto {b : ℝ} (hb : 0<b) :
    Tendsto (fun σ=>publicRetentionEnvelope σ b) atTop (𝓝 0) := by
  have h1:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<1998) hb)
  have h2:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<999) hb)
  have h3:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b 1 zero_lt_one
  have h4:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<1999) hb)
  have h5:=tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<2000) hb)
  simpa only [publicRetentionEnvelope,neg_mul,one_mul,neg_one_mul,mul_zero,add_zero] using
    ((((h1.const_mul (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)).add
      (h2.const_mul ((4*Real.exp 1)^2*320016))).add (h3.const_mul 5)).add
      (h4.const_mul (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008))).add
      (h5.const_mul (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008))

theorem eventually_retention_error {b : ℝ} (hb : 0<b) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀ (D H : ℝ),σ^b≤D→0≤H→H≤σ^b→
      2*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C+publicRetentionError σ b H≤ε := by
  filter_upwards [eventually_reciprocal_endpoints hb C (ε/4) hC (by positivity),
    (publicRetentionEnvelope_tendsto hb).eventually_lt_const (show 0<ε/2 by positivity),
    eventually_ge_atTop (1:ℝ)] with σ hbad herr hσ
  intro D H hD hH hH'
  have h1:=(hbad D hD).1
  have h2:=(publicRetentionError_bound hσ hH hH').trans herr.le
  linarith
end
end SharpRamseyFive.Marking

end OAI
