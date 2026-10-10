import OAI.MathematicalPhysics.Heisenberg.PeriodicReturnEstimate

namespace OAI

section

noncomputable section
open Filter Topology
namespace Heisenberg.Bootstrap

lemma nat_rpow_tendsto_zero (e : ℝ) (he : e < 0) :
    Tendsto (fun n : ℕ=>(n:ℝ)^e) atTop (𝓝 0) := by
  have hh:=tendsto_rpow_neg_atTop (neg_pos.mpr he)
  simpa only [Function.comp_def,neg_neg] using hh.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

lemma exponent_split (x a b : ℝ) (hx : 0 < x) :
    x^a=x^b*x^(a-b) := by rw [←Real.rpow_add hx]; congr 1; ring

theorem choose_parameters (d : ℕ) (hd : 3 ≤ d) (M : ℕ)
    (B F G p₀ : ℝ) (_hB : 0 ≤ B) (hF : 0 ≤ F) (hG : 0 ≤ G) (hp₀ : 0 < p₀) :
    ∃ (p s : ℝ) (R : ℕ),0 < p ∧ p < 1/4 ∧ p ≤ p₀ ∧ 0 < s ∧
      s=p^(-(11/10:ℝ)) ∧ 1 ≤ R ∧ M ≤ R ∧ 8*B*Real.exp 1*s ≤ R ∧
      2*(G*((1+(R:ℝ))^d*p^(2*d)+1/(1+(R:ℝ)))+1/(1+(R:ℝ)))+
        8*F*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4 := by
  obtain ⟨K,hK⟩:=exists_nat_gt (max (8*B*Real.exp 1) 1)
  have hK1 : 1 ≤ K := by
    have hh : (1:ℝ) < K := (le_max_right _ _).trans_lt hK
    exact_mod_cast hh.le
  have hKb : 8*B*Real.exp 1 ≤ K := (le_max_left _ _).trans hK.le
  let A:=2*G*((K:ℝ)+1)^d
  let C:=2*(G+1)
  let D:=8*F*((K:ℝ)+1)^((1:ℝ)/100)
  let e:ℝ:=(10/11:ℝ)-(9/11)*(d:ℝ)
  have he : e < 0 := by
    have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
    dsimp only [e]
    linarith
  have ht : Tendsto (fun n : ℕ=>A*(n:ℝ)^e+C*(n:ℝ)^(-(1/11:ℝ))+
      D*(n:ℝ)^(-(89/1100:ℝ))) atTop (𝓝 0) := by
    simpa using (((nat_rpow_tendsto_zero e he).const_mul A).add
      ((nat_rpow_tendsto_zero (-(1/11:ℝ)) (by norm_num)).const_mul C)).add
      ((nat_rpow_tendsto_zero (-(89/1100:ℝ)) (by norm_num)).const_mul D)
  have hp := nat_rpow_tendsto_zero (-(10/11:ℝ)) (by norm_num)
  have ev := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and
    ((hp.eventually (gt_mem_nhds hp₀)).and
      ((hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and
        (eventually_ge_atTop (max M 1))))
  obtain ⟨r,hrerror,hrp,hrsmall,hr⟩:=ev.exists
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hrpos : 0 < (r:ℝ) := lt_of_lt_of_le zero_lt_one hrR
  let p:ℝ:=(r:ℝ)^(-(10/11:ℝ))
  let R:ℕ:=K*r
  have hp : 0 < p := Real.rpow_pos_of_pos hrpos _
  have hRr : r ≤ R := by dsimp [R]; nlinarith
  have hR : (r:ℝ) ≤ R := by exact_mod_cast hRr
  have hRup : 1+(R:ℝ) ≤ ((K:ℝ)+1)*r := by dsimp [R]; push_cast; nlinarith
  have hrpow : (r:ℝ)^d*p^(2*d)=(r:ℝ)^(-(9/11:ℝ)*(d:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast p]
    dsimp only [p]
    rw [←Real.rpow_mul hrpos.le,←Real.rpow_add hrpos]
    congr 1
    push_cast
    ring
  have hreg : (1+(R:ℝ))^d*p^(2*d) ≤ ((K:ℝ)+1)^d*(r:ℝ)^(-(9/11:ℝ)*(d:ℝ)) := by
    calc
      _ ≤ (((K:ℝ)+1)*r)^d*p^(2*d) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hRup d) (by positivity)
      _ = _ := by rw [mul_pow,mul_assoc,hrpow]
  have htail : 1/(1+(R:ℝ)) ≤ (r:ℝ)^(-1:ℝ) := by
    rw [Real.rpow_neg_one]
    rw [←one_div]
    exact one_div_le_one_div_of_le hrpos (by linarith)
  have hflow : (1+(R:ℝ))^((1:ℝ)/100)/(r:ℝ) ≤
      ((K:ℝ)+1)^((1:ℝ)/100)*(r:ℝ)^(-(99/100:ℝ)) := by
    calc
      _ ≤ (((K:ℝ)+1)*r)^((1:ℝ)/100)/(r:ℝ) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hRup (by norm_num)) hrpos.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hrpos.le,mul_div_assoc,←Real.rpow_sub_one hrpos.ne']
        congr 2
        norm_num
  refine ⟨p,(r:ℝ),R,hp,hrsmall,hrp.le,hrpos,?_,(hr1.trans hRr),?_,?_,?_⟩
  · dsimp only [p]
    rw [←Real.rpow_mul hrpos.le]
    norm_num
  · exact (le_max_left _ _).trans (hr.trans hRr)
  · dsimp [R]
    push_cast
    nlinarith
  · have hmain : 2*(G*((1+(R:ℝ))^d*p^(2*d)+1/(1+(R:ℝ)))+1/(1+(R:ℝ)))+
        8*F*(1+(R:ℝ))^((1:ℝ)/100)/(r:ℝ) ≤
        A*(r:ℝ)^(-(9/11:ℝ)*(d:ℝ))+C*(r:ℝ)^(-1:ℝ)+D*(r:ℝ)^(-(99/100:ℝ)) := by
      have h1:=mul_le_mul_of_nonneg_left hreg hG
      have h2:=mul_le_mul_of_nonneg_left htail hG
      have h3:=mul_le_mul_of_nonneg_left hflow (by positivity : 0 ≤ 8*F)
      dsimp only [A,C,D]
      rw [←mul_div_assoc] at h3
      nlinarith
    apply hmain.trans_lt
    have he' : (-(9/11:ℝ)*(d:ℝ))-(-(10/11:ℝ))=e := by dsimp [e]; ring
    rw [exponent_split (r:ℝ) (-(9/11:ℝ)*(d:ℝ)) (-(10/11:ℝ)) hrpos,
      exponent_split (r:ℝ) (-1:ℝ) (-(10/11:ℝ)) hrpos,
      exponent_split (r:ℝ) (-(99/100:ℝ)) (-(10/11:ℝ)) hrpos,he']
    have h1 : (-1:ℝ)-(-(10/11:ℝ))=-(1/11:ℝ) := by norm_num
    have h2 : (-(99/100:ℝ))-(-(10/11:ℝ))=-(89/1100:ℝ) := by norm_num
    rw [h1,h2]
    change _ < p/4
    calc
      _ = p*(A*(r:ℝ)^e+C*(r:ℝ)^(-(1/11:ℝ))+D*(r:ℝ)^(-(89/1100:ℝ))) := by dsimp [p]; ring
      _ < p*(1/4) := mul_lt_mul_of_pos_left hrerror hp
      _ = _ := by ring

end Heisenberg.Bootstrap
end
end

end OAI
