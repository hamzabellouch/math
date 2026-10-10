import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.ReceiverWeights

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma capped_inverse_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,x≤cappedRepresentative j) :
    ∑j∈S,(x/cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.max' hne
    have hj₀ : j₀∈S := S.max'_mem hne
    have hjmax (j : ℕ) (hj : j∈S) : j≤j₀ := S.le_max' j hj
    have hp (j : ℕ) (hj : j∈S) : x/cappedRepresentative j≤((2:ℝ)⁻¹)^(j₀-j) := by
      have he : cappedRepresentative j₀=cappedRepresentative j*((2:ℝ)⁻¹)^(j₀-j) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmax j hj)]
      apply (div_le_iff₀ (cappedRepresentative_pos j)).mpr
      rw [mul_comm,←he]
      exact hS j₀ hj₀
    have hpoint (j : ℕ) (hj : j∈S) : (x/cappedRepresentative j)^α≤(((2:ℝ)⁻¹)^α)^(j₀-j) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg hx.le (cappedRepresentative_pos j).le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j₀-j) S := by
      intro i hi j hj hij
      have hi' := hjmax i hi
      have hj' := hjmax j hj
      change j₀-i=j₀-j at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j₀-j) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j₀-j),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma relative_occupation_angular_sum {θ φ K κ e : ℝ} (hθ : 0<θ) (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (he : 1/4<e) (hsector : φ≤κ*θ)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,(cappedRepresentative j)^e*(1+φ/cappedRepresentative j)^(1/4:ℝ) ≤
    (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e+
      ((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))*θ^e := by
  have he0 : 0<e := by linarith
  have hsub : 0<e-1/4 := by linarith
  have hsum := capped_positive_power_sum_unscaled (mul_pos hK hθ) he0 S hS
  have hsum' := capped_positive_power_sum_unscaled (mul_pos hK hθ) hsub S hS
  have hpoint (j : ℕ) : (cappedRepresentative j)^e*(1+φ/cappedRepresentative j)^(1/4:ℝ) ≤
      (cappedRepresentative j)^e+φ^(1/4:ℝ)*(cappedRepresentative j)^(e-1/4) := by
    have hσ := cappedRepresentative_pos j
    have hq := Real.rpow_add_le_add_rpow (by norm_num : (0:ℝ)≤1)
      (div_nonneg hφ hσ.le) (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1)
    rw [Real.one_rpow,Real.div_rpow hφ hσ.le] at hq
    calc
      _≤(cappedRepresentative j)^e*(1+φ^(1/4:ℝ)/(cappedRepresentative j)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hσ.le _)
      _= _ := by rw [Real.rpow_sub hσ]; ring
  have hφpow := Real.rpow_le_rpow hφ hsector (by norm_num : (0:ℝ)≤1/4)
  have heq : θ^(e-1/4)*θ^(1/4:ℝ)=θ^e := by rw [←Real.rpow_add hθ]; congr 1; ring
  calc
    _ ≤ ∑j∈S,((cappedRepresentative j)^e+φ^(1/4:ℝ)*(cappedRepresentative j)^(e-1/4)) :=
      Finset.sum_le_sum (fun j _=>hpoint j)
    _ = (∑j∈S,(cappedRepresentative j)^e)+φ^(1/4:ℝ)*(∑j∈S,(cappedRepresentative j)^(e-1/4)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ((1-((2:ℝ)⁻¹)^e)⁻¹)*(K*θ)^e+
        (κ*θ)^(1/4:ℝ)*(((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*(K*θ)^(e-1/4)) := by
      apply add_le_add hsum
      apply mul_le_mul hφpow hsum' (Finset.sum_nonneg (fun j _=>Real.rpow_nonneg (cappedRepresentative_pos j).le _))
      exact Real.rpow_nonneg (mul_nonneg hκ hθ.le) _
    _ = _ := by
      rw [Real.mul_rpow hK.le hθ.le,Real.mul_rpow hκ hθ.le,Real.mul_rpow hK.le hθ.le]
      calc
        _ = (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e)*θ^e+
          (((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))*(θ^(e-1/4)*θ^(1/4:ℝ)) := by ring
        _ = _ := by rw [heq]; ring

def relativeSourceAngle (θ φ σ : ℝ) : ℝ :=
  (min θ σ)^(3/2:ℝ)*(1+φ/σ)^(1/4:ℝ)

def relativeAngularConstant (K κ e : ℝ) : ℝ :=
  (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e+
    ((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))

lemma relativeAngularConstant_nonneg {K κ e : ℝ} (hK : 0≤K) (hκ : 0≤κ) (he : 1/4<e) :
    0≤relativeAngularConstant K κ e := by
  have h0 : 0≤e := by linarith
  have h1 : 0≤e-1/4 := by linarith
  unfold relativeAngularConstant
  apply add_nonneg
  · exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h0))) (Real.rpow_nonneg hK _)
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h1))) (Real.rpow_nonneg hK _)) (Real.rpow_nonneg hκ _)

lemma relativeSourceAngle_nonneg {θ φ σ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0<σ) :
    0≤relativeSourceAngle θ φ σ := by
  dsimp [relativeSourceAngle]
  positivity

lemma relative_source_angle_sum {θ φ K κ β : ℝ} (hθ : 0<θ) (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (_hβ : 0≤β) (hβ1 : β≤1/2) (hsector : φ≤κ*θ)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,relativeSourceAngle θ φ (cappedRepresentative j)/(cappedRepresentative j)^β ≤
      relativeAngularConstant K κ (3/2-β)*θ^(3/2-β) := by
  have he : 1/4<3/2-β := by linarith
  apply le_trans _ (relative_occupation_angular_sum hθ hφ hK hκ he hsector S hS)
  apply Finset.sum_le_sum
  intro j hj
  have hσ := cappedRepresentative_pos j
  have hq : 0≤1+φ/cappedRepresentative j := by positivity
  calc
    _ ≤ ((cappedRepresentative j)^(3/2:ℝ)*(1+φ/cappedRepresentative j)^(1/4:ℝ))/(cappedRepresentative j)^β := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hσ.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq _)
      exact Real.rpow_le_rpow (le_min hθ.le hσ.le) (min_le_right _ _) (by norm_num)
    _ = _ := by rw [Real.rpow_sub hσ]; ring

lemma capped_lower_weighted_power_sum {φ κ α : ℝ} (hφ : 0<φ) (hκ : 0<κ) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀i∈S,φ≤κ*cappedRepresentative i) :
    ∑i∈S,φ*(cappedRepresentative i)^(-α) ≤
    (1-((2:ℝ)⁻¹)^α)⁻¹*κ^α*φ^(1-α) := by
  have hsum := capped_inverse_power_sum (div_pos hφ hκ) hα S
    (fun i hi=>(div_le_iff₀ hκ).mpr (by nlinarith only [hS i hi]))
  have he (i : ℕ) : φ*(cappedRepresentative i)^(-α)=
      (κ^α*φ^(1-α))*((φ/κ)/cappedRepresentative i)^α := by
    have hσ := cappedRepresentative_pos i
    rw [Real.rpow_neg hσ.le,Real.rpow_sub hφ,Real.rpow_one,
      Real.div_rpow (div_nonneg hφ.le hκ.le) hσ.le,Real.div_rpow hφ.le hκ.le]
    field_simp [(Real.rpow_pos_of_pos hκ α).ne',(Real.rpow_pos_of_pos hφ α).ne',
      (Real.rpow_pos_of_pos hσ α).ne']
  calc
    _ = (κ^α*φ^(1-α))*(∑i∈S,((φ/κ)/cappedRepresentative i)^α) := by simp_rw [he]; rw [Finset.mul_sum]
    _ ≤ (κ^α*φ^(1-α))*(1-((2:ℝ)⁻¹)^α)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma remaining_good_fixed_receiver_sum {φ K κ β : ℝ} (hφ : 0<φ)
    (hK : 0<K) (hκ : 0<κ) (hβ : 0≤β) (hβ1 : β≤1/2)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,
      (φ/(cappedRepresentative i)^2)*
        (relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β) ≤
    relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*
      κ^(1/2+β)*φ^(1/2-β) := by
  let C := relativeAngularConstant K κ (3/2-β)
  have hC : 0≤C := relativeAngularConstant_nonneg hK.le hκ.le (by linarith)
  have hp (i : ℕ) (hi : i∈Sθ) := relative_source_angle_sum (cappedRepresentative_pos i)
    hφ.le hK hκ.le hβ hβ1 (hθ i hi) (Sσ i) (hσ i hi)
  have he (i : ℕ) : (φ/(cappedRepresentative i)^2)*(C*(cappedRepresentative i)^(3/2-β))=
      C*(φ*(cappedRepresentative i)^(-(1/2+β))) := by
    have hc := cappedRepresentative_pos i
    rw [show -(1/2+β)=3/2-β-2 by ring]
    simp only [Real.rpow_sub hc,Real.rpow_two]
    ring
  have hs := capped_lower_weighted_power_sum hφ hκ (show 0<(1/2:ℝ)+β by linarith) Sθ hθ
  calc
    _ ≤ ∑i∈Sθ,(φ/(cappedRepresentative i)^2)*(C*(cappedRepresentative i)^(3/2-β)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hp i hi) (by positivity)
    _ = C*(∑i∈Sθ,φ*(cappedRepresentative i)^(-(1/2+β))) := by simp_rw [he]; rw [Finset.mul_sum]
    _ ≤ C*((1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*κ^(1/2+β)*φ^(1-(1/2+β))) :=
      mul_le_mul_of_nonneg_left hs hC
    _ = _ := by rw [show (1:ℝ)-(1/2+β)=1/2-β by ring]; dsimp [C]; ring

lemma remaining_magnetic_fixed_receiver_sum {φ K κ β : ℝ} (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (hβ : 0≤β) (hβ1 : β≤1/2)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,
      relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β ≤
    relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(3/2-β))⁻¹ := by
  let C := relativeAngularConstant K κ (3/2-β)
  have hC : 0≤C := relativeAngularConstant_nonneg hK.le hκ (by linarith)
  have hs := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (show 0<(3/2:ℝ)-β by linarith) Sθ (fun _ _=>cappedRepresentative_le_one _)
  rw [Real.one_rpow,mul_one] at hs
  calc
    _ ≤ ∑i∈Sθ,C*(cappedRepresentative i)^(3/2-β) := by
      apply Finset.sum_le_sum
      intro i hi
      exact relative_source_angle_sum (cappedRepresentative_pos i) hφ hK hκ hβ hβ1 (hθ i hi) (Sσ i) (hσ i hi)
    _ = C*(∑i∈Sθ,(cappedRepresentative i)^(3/2-β)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC

lemma square_root_clipped_stability {I P C M A p w σ : ℝ}
    (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hσ : 0<σ) (hσ1 : σ≤1) :
    Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))) ≤
      2+2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))/Real.sqrt σ := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hlam := stabilityLength_pos hP hC hM hp hw hσ (A:=A)
  have hr := sqrt_baseline_clipped_length hI hlam
  rw [sqrt_div_stabilityLength hP.le hC.le hM.le hp.le hw.le hσ.le hI.le] at hr
  have hroot : Real.sqrt σ≤1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hσ1
  have hs : σ≤Real.sqrt σ := by
    nlinarith [Real.sq_sqrt hσ.le,Real.sqrt_nonneg σ]
  have hrate : stabilityRate P C M A p w σ ≤
      C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ := by
    unfold stabilityRate
    rw [Real.sqrt_div (mul_nonneg hA hL)]
    have hdiv : Real.sqrt (A*Real.log (2+P))/Real.sqrt σ≤
        Real.sqrt (A*Real.log (2+P))/σ :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hσ hs
    have he : C*(P/min p w)*(M/σ+Real.sqrt (A*Real.log (2+P))/σ)=
        C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ := by ring
    rw [←he]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hdiv) (by positivity)
  have hX : 0≤Real.sqrt I*stabilityRate P C M A p w σ := by
    unfold stabilityRate
    positivity
  have hsimple : Real.sqrt (2*(1+Real.sqrt I*stabilityRate P C M A p w σ))≤
      2+2*Real.sqrt (Real.sqrt I*stabilityRate P C M A p w σ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg (Real.sqrt I*stabilityRate P C M A p w σ)]
  have hII : Real.sqrt (Real.sqrt I)=(I : ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hI.le]
    congr 1
    norm_num
  have hfac : Real.sqrt (Real.sqrt I*(C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ))=
      Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))/Real.sqrt σ := by
    rw [Real.sqrt_mul (Real.sqrt_nonneg I),Real.sqrt_div (by positivity),
      Real.sqrt_mul (by positivity : 0≤C*(P/min p w)),Real.sqrt_mul hC.le,hII]
    ring
  calc
    _≤Real.sqrt (2*(1+Real.sqrt I*stabilityRate P C M A p w σ)) := Real.sqrt_le_sqrt hr
    _≤2+2*Real.sqrt (Real.sqrt I*stabilityRate P C M A p w σ) := hsimple
    _≤2+2*Real.sqrt (Real.sqrt I*(C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ)) := by gcongr
    _=2+2*(Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))/Real.sqrt σ) := by rw [hfac]
    _≤2+2*(Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))/Real.sqrt σ) := by
      have hadd : Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))≤
          Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [Real.sq_sqrt hM.le,Real.sq_sqrt (Real.sqrt_nonneg (A*Real.log (2+P))),
            mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg (Real.sqrt (A*Real.log (2+P))))]
      gcongr
    _=_ := by ring

def remainingGoodConstant (K κ β : ℝ) : ℝ :=
  relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*κ^(1/2+β)

def remainingMagneticConstant (K κ β : ℝ) : ℝ :=
  relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(3/2-β))⁻¹

lemma remaining_shared_source_angular {φ K κ B g b : ℝ} (hφ : 0<φ)
    (hK : 0<K) (hκ : 0<κ) (hB : 0≤B) (hg : 0≤g) (hb : 0≤b)
    (R : ℕ→ℝ) (hR : ∀j,R j≤2+B/Real.sqrt (cappedRepresentative j))
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,R j*relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
      (g*(φ/(cappedRepresentative i)^2)+b) ≤
    g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
    b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2)) := by
  let G (β : ℝ) := ∑i∈Sθ,∑j∈Sσ i,(φ/(cappedRepresentative i)^2)*
    (relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β)
  let H (β : ℝ) := ∑i∈Sθ,∑j∈Sσ i,
    relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β
  have hG0 : G 0≤remainingGoodConstant K κ 0*Real.sqrt φ := by
    simpa only [G,remainingGoodConstant,add_zero,sub_zero,Real.sqrt_eq_rpow] using
      remaining_good_fixed_receiver_sum hφ hK hκ (by norm_num : (0:ℝ)≤0) (by norm_num) Sθ Sσ hθ hσ
  have hG1 : G (1/2)≤remainingGoodConstant K κ (1/2) := by
    have hh := remaining_good_fixed_receiver_sum hφ hK hκ (by norm_num : (0:ℝ)≤1/2) (by norm_num) Sθ Sσ hθ hσ
    simpa only [G,remainingGoodConstant,sub_self,Real.rpow_zero,mul_one] using hh
  have hH0 : H 0≤remainingMagneticConstant K κ 0 :=
    remaining_magnetic_fixed_receiver_sum hφ.le hK hκ.le (by norm_num) (by norm_num) Sθ Sσ hθ hσ
  have hH1 : H (1/2)≤remainingMagneticConstant K κ (1/2) :=
    remaining_magnetic_fixed_receiver_sum hφ.le hK hκ.le (by norm_num) (by norm_num) Sθ Sσ hθ hσ
  calc
    _≤∑i∈Sθ,∑j∈Sσ i,(2+B/Real.sqrt (cappedRepresentative j))*
      relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
        (g*(φ/(cappedRepresentative i)^2)+b) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hR j)
        (relativeSourceAngle_nonneg (cappedRepresentative_pos i).le hφ.le (cappedRepresentative_pos j))
    _=g*(2*G 0+B*G (1/2))+b*(2*H 0+B*H (1/2)) := by
      simp only [G,H,Real.rpow_zero,div_one,←Real.sqrt_eq_rpow,mul_add,
        Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _≤_ := by
      have hgg := add_le_add (mul_le_mul_of_nonneg_left hG0 (by norm_num : (0:ℝ)≤2))
        (mul_le_mul_of_nonneg_left hG1 hB)
      have hhh := add_le_add (mul_le_mul_of_nonneg_left hH0 (by norm_num : (0:ℝ)≤2))
        (mul_le_mul_of_nonneg_left hH1 hB)
      have hh := add_le_add (mul_le_mul_of_nonneg_left hgg hg) (mul_le_mul_of_nonneg_left hhh hb)
      simpa only [mul_assoc] using hh

lemma remaining_stable_source_angular {I P C M A p w φ K κ g b : ℝ}
    (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hK : 0<K) (hκ : 0<κ)
    (hg : 0≤g) (hb : 0≤b)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    let B := 2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
      (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
    ∑i∈Sθ,∑j∈Sσ i,
      Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w (cappedRepresentative j)/2)))*
        relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
          (g*(φ/(cappedRepresentative i)^2)+b) ≤
    g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
    b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2)) := by
  apply remaining_shared_source_angular hφ hK hκ (by positivity) hg hb _ _ Sθ Sσ hθ hσ
  intro j
  exact square_root_clipped_stability hI hP hC hM hA hp hw (cappedRepresentative_pos j)
    (cappedRepresentative_le_one j)

lemma Admissible.direct_source_shared_short_angles_expanded {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nφ : ℕ) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<M → 0≤A → 0<P → 0<w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ),
      (∀i∈Sθ,cappedRepresentative nφ≤16384*cappedRepresentative i) →
      (∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i ∧
        512≤cappedRepresentative j*sourceRepresentative np ∧ 32≤cappedRepresentative j*w) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun i j nr=>relativeRepresentativeClosedBin T w ![np,i,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      let R₁ := 2*Real.sqrt 16384*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
      (∑i∈Sθ,∑j∈Sσ i,∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B i j nr) z
          ∂physicalBinMeasure V (B i j nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*
        (Kg*(2*remainingGoodConstant 131080 16384 0*Real.sqrt φ+R₁*remainingGoodConstant 131080 16384 (1/2))+
         Kb*(2*remainingMagneticConstant 131080 16384 0+R₁*remainingMagneticConstant 131080 16384 (1/2)))) := by
  have hshortRadius :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        max 1 T*cappedRepresentative (k 3) ≤ I →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative (k 0)
        let θ := cappedRepresentative (k 1)
        let φ := cappedRepresentative (k 2)
        let σ := cappedRepresentative j
        let r := max 1 T*cappedRepresentative (k 3)
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := relativeRepresentativeClosedBin T w k j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let G := (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)).toReal
        let Hf := (magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)).toReal
        let Kg := relativeCauchyConstant Cg E G
        let Kb := relativeCauchyConstant Cb E (2*Hf)
        (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
          ∂physicalBinMeasure V B (Icc a b)) ≤
        ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
          ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r)+
        Kb*min ((I*p^2*ν^2*φ)*Real.sqrt r)
          ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_radius_budget
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
    have hn := hsource s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
    dsimp only at hn ⊢
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let σ := cappedRepresentative j
    let r := max 1 T*cappedRepresentative (k 3)
    let ν := min θ σ
    let κ := 1+φ/σ
    let E := ∫x : Vec,totalEnergy s (0,x)
    let R := Real.sqrt (1+I/len)
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hσ : 0<σ := cappedRepresentative_pos _
    have hν : 0<ν := lt_min hθ hσ
    have hκ : 0≤κ := by dsimp [κ]; positivity
    have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
    have hI : 0<I := hlen.trans_le hlenI
    have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
    have hR : 0≤R := Real.sqrt_nonneg _
    have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let G := goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)
    let Hf := magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)
    have hG : G≠⊤ := ne_top_of_le_ne_top
      (hs.goodFieldBudget_finite X (fun t=>velocity (V t)) 1 (Icc_subset_Icc ha hb) hI)
      (ENNReal.le_tsum (f := fun index=>goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I index) (k 2))
    have hF : Hf≠⊤ := by
      apply ne_top_of_le_ne_top _ ((ENNReal.le_tsum (k 2)).trans
        (hs.shared_magneticFieldBudget F.flow zX 1 hI (by norm_num : (0:ℝ)≤2) hJI))
      finiteness
    have hGe : ENNReal.ofReal (G.toReal*I)=ENNReal.ofReal I*G := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hG,mul_comm]
    have hFe : ENNReal.ofReal ((2*Hf.toReal)*I)=ENNReal.ofReal (2*I)*Hf := by
      rw [show (2*Hf.toReal)*I=(2*I)*Hf.toReal by ring,
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hF]
    have hg := relative_radius_cauchy_scalar hCg hE ENNReal.toReal_nonneg hI hp hν hR hr hφ hκ
      (show 0≤φ/θ^2 by positivity) (Z:=G.toReal)
    dsimp only at hg
    have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
    have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
    have heb : Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ=Real.sqrt I*R*ν*Real.sqrt κ/θ^2 := by
      field_simp [hφ.ne']
    rw [heγ,hea,heb,hGe,hRsq] at hg
    have hbnd := relative_radius_cauchy_scalar hCb hE (show 0≤2*Hf.toReal by positivity) hI hp hν hR hr hφ hκ
      (show 0≤(1:ℝ) by norm_num)
    dsimp only at hbnd
    simp only [mul_one] at hbnd
    rw [hFe,hRsq] at hbnd
    apply hn.trans
    calc
      _ ≤ ENNReal.ofReal (relativeCauchyConstant Cg E G.toReal*
            min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
              ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r))+
          ENNReal.ofReal (relativeCauchyConstant Cb E (2*Hf.toReal)*
            min ((I*p^2*ν^2*φ)*Real.sqrt r)
              ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
        exact add_le_add hg hbnd
      _ = _ := by
        rw [←ENNReal.ofReal_add
          (mul_nonneg (relativeCauchyConstant_nonneg hCg) (by positivity))
          (mul_nonneg (relativeCauchyConstant_nonneg hCb) (by positivity))]

  have hshortRadialSum :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (Kg*D*Real.sqrt
          ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))+
          Kb*D*Real.sqrt ((I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt κ/φ))) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortRadius
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only
    let p := sourceRepresentative np
    let θ := cappedRepresentative nθ
    let φ := cappedRepresentative nφ
    let σ := cappedRepresentative j
    let ν := min θ σ
    let κ := 1+φ/σ
    let E := ∫x : Vec,totalEnergy s (0,x)
    let R := Real.sqrt (1+I/len)
    let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
    let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
    let ag := I*p^2*ν^2*φ^2/θ^2
    let bg := Real.sqrt I*R*ν*Real.sqrt κ/θ^2
    let ab := I*p^2*ν^2*φ
    let bb := Real.sqrt I*R*ν*Real.sqrt κ/φ
    let D := dyadicBalanceConstant (1/2) (1/2)
    have hI : 0<I := hlen.trans_le hlenI
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hσ : 0<σ := cappedRepresentative_pos _
    have hν : 0≤ν := (lt_min hθ hσ).le
    have hag : 0≤ag := by dsimp [ag]; positivity
    have hbg : 0≤bg := by dsimp [bg,R,κ]; positivity
    have hab' : 0≤ab := by dsimp [ab]; positivity
    have hbb : 0≤bb := by dsimp [bb,R,κ]; positivity
    have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
    have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
    have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
    have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
    have hpoint (nr : ℕ) := hsource s T F hs hT h0 zX S ![np,nθ,nφ,nr] j
      a b I len w M A P L massScale Cs hS hS0 ha hb hab hlen hlenI hJI
      hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable
    calc
      _ ≤ ∑'nr : ℕ, (ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative nr))
          (bg/Real.sqrt (max 1 T*cappedRepresentative nr)))+
        ENNReal.ofReal (Kb*min (ab*Real.sqrt (max 1 T*cappedRepresentative nr))
          (bb/Real.sqrt (max 1 T*cappedRepresentative nr)))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        split_ifs with hnr
        · have hn := hpoint nr hnr HX HZ
          dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
            Matrix.cons_val,Fin.reduceFinMk] at hn
          refine hn.trans_eq ?_
          exact ENNReal.ofReal_add (mul_nonneg hKg (by positivity)) (mul_nonneg hKb (by positivity))
        · exact bot_le
      _ ≤ ENNReal.ofReal (Kg*D*Real.sqrt (ag*bg))+
          ENNReal.ofReal (Kb*D*Real.sqrt (ab*bb)) := by
        rw [ENNReal.tsum_add]
        exact add_le_add (capped_sqrt_radius_ennreal_sum hag hbg hH hKg)
          (capped_sqrt_radius_ennreal_sum hab' hbb hH hKb)
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

  have hbalanceFactor {I p ν R κ φ γ : ℝ}
      (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
      (hφ : 0<φ) (hγ : 0≤γ) :
      Real.sqrt ((I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ))=
        (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*γ := by
    have he : (I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)=
        (I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ*γ^2 := by field_simp
    have hIs : Real.sqrt (I*Real.sqrt I)=(I : ℝ)^(3/4:ℝ) := by
      rw [Real.sqrt_mul hI.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hI.le,
        ←Real.rpow_add hI]
      congr 1
      norm_num
    have hνs : Real.sqrt (ν^3)=ν^(3/2:ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_natCast_mul hν]
      norm_num
    have hκs : Real.sqrt (Real.sqrt κ)=κ^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hκ]
      congr 1
      norm_num
    rw [he,Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2),
      Real.sqrt_mul (by positivity : 0≤I*Real.sqrt I),Real.sqrt_sq hp,Real.sqrt_sq hγ,hIs,hνs,hκs]

  have hgoodBalanceFactor {I p ν R κ φ θ : ℝ}
      (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
      (hφ : 0<φ) (hθ : 0<θ) :
      Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))=
        (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*(φ/θ^2) := by
    have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2)=
        (I*p^2*ν^2*φ*(φ/θ^2))*(Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ) := by
      field_simp
    rw [he]
    exact hbalanceFactor hI hp hν hR hκ hφ (by positivity)

  have hshortFactored :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
          relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortRadialSum
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only
    have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only at hn
    have hp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
    have hθ := cappedRepresentative_pos nθ
    have hφ := cappedRepresentative_pos nφ
    have hσ := cappedRepresentative_pos j
    have hκ : 0≤1+cappedRepresentative nφ/cappedRepresentative j := by positivity
    have hb := hbalanceFactor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
      (Real.sqrt_nonneg (1+I/len)) hκ hφ (by norm_num : (0:ℝ)≤1)
    simp only [mul_one] at hb
    rw [hgoodBalanceFactor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
      (Real.sqrt_nonneg _) hκ hφ hθ,hb] at hn
    convert hn using 1
    congr 1
    dsimp [relativeSourceAngle]
    ring

  have hshortClipped :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I w M A P : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 < w →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w σ/2))
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
          relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortFactored
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I w M A P hS hS0 ha hb hab hI hJI
      hM hA hP hw hpσ hwσ HX HZ
    dsimp only
    let p := sourceRepresentative np
    let σ := cappedRepresentative j
    let L := Real.log (2+P)
    let lam := stabilityLength P 16384 M A p w σ
    let len := min I (lam/2)
    let m := min p w/128
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hσ : 0<σ := cappedRepresentative_pos _
    have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hσ
    have hlen : 0<len := lt_min hI (by positivity)
    have hlenI : len≤I := min_le_left _ _
    have hlenlam : 2*len≤lam := by
      have hh : len≤lam/2 := min_le_right _ _
      linarith only [hh]
    have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
    have hmq : m≤p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hmw : m≤w/8 := by
      have hh : min p w≤w := min_le_right _ _
      dsimp [m]
      linarith only [hh,hw]
    have hstable : 2*len≤(128*(P/m)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
      dsimp only [m,L]
      rw [stability_massScale_identity]
      convert hlenlam using 1; norm_num [lam]
    exact hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP (Real.log_nonneg (by linarith)) hm hw
      (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortClipped
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nφ a b I w M A P hS hS0 ha hb hab hI hJI hM hA hP hw HX HZ
    Sθ Sσ hθ hσ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nφ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E
    (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
  let Kb := relativeCauchyConstant Cb E
    (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let R (j : ℕ) := Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w (cappedRepresentative j)/2)))
  let U (i j : ℕ) := R j*relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
    (Kg*(φ/(cappedRepresentative i)^2)+Kb)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hU (i j : ℕ) : 0≤U i j := by
    dsimp only [U]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (relativeSourceAngle_nonneg
      (cappedRepresentative_pos i).le hφ.le (cappedRepresentative_pos j))) (by positivity)
  have hn := remaining_stable_source_angular hI hP (by norm_num : (0:ℝ)<16384) hM hA hp hw hφ
    (by norm_num : (0:ℝ)<131080) (by norm_num : (0:ℝ)<16384) hKg hKb Sθ Sσ hθ
      (fun i hi j hj=>(hσ i hi j hj).1)
  calc
    _≤∑i∈Sθ,∑j∈Sσ i,ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*U i j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hsource s T F hs hT h0 zX S np i nφ j a b I w M A P hS hS0 ha hb hab
        hI hJI hM hA hP hw (hσ i hi j hj).2.1 (hσ i hi j hj).2.2 HX HZ
      dsimp only at hh
      simpa only [U,R,D,Kg,Kb,p,φ,E,mul_assoc] using hh
    _=ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*(∑i∈Sθ,∑j∈Sσ i,U i j)) := by
      rw [Finset.mul_sum]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
        exact fun j _=>mul_nonneg (by positivity) (hU i j)
      · intro i hi
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _=>hU i j))
    _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn (by positivity))

lemma capped_inverse_square_floor_sum {p : ℝ} (hp : 0<p) (S : Finset ℕ)
    (hS : ∀nt∈S,1/p≤cappedRepresentative nt) :
    (∑nt∈S,1/(p*(cappedRepresentative nt)^2))≤2*p := by
  have hh := capped_inverse_power_sum (one_div_pos.mpr hp) (by norm_num : (0:ℝ)<2) S hS
  norm_num only [Real.rpow_two,inv_pow] at hh
  norm_num at hh
  have he (nt : ℕ) : 1/(p*(cappedRepresentative nt)^2)=p*((1/p)/cappedRepresentative nt)^2 := by
    have ht := (cappedRepresentative_pos nt).ne'
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hh' := mul_le_mul_of_nonneg_left hh hp.le
  simp only [one_div] at *
  nlinarith

lemma capped_inverse_square_floor_tsum {p : ℝ} (hp : 0<p) :
    (∑'nt : ℕ,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then
      1/(p*(cappedRepresentative nt)^2) else 0))≤ENNReal.ofReal (2*p) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun nt=>1/p≤cappedRepresentative nt)
  have he : (∑nt∈S,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then
      1/(p*(cappedRepresentative nt)^2) else 0))=
      ∑nt∈U,ENNReal.ofReal (1/(p*(cappedRepresentative nt)^2)) := by
    simp only [U,Finset.sum_filter,apply_ite,ENNReal.ofReal_zero]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun nt _=>by positivity)]
  exact ENNReal.ofReal_le_ofReal (capped_inverse_square_floor_sum hp U
    (fun nt hnt=>(Finset.mem_filter.mp hnt).2))

lemma small_transport_coefficient {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ) (_hφ : 0<φ)
    (hsmall : θ≤φ/16) :
    128*(θ+φ)/((p/128)^2*θ^3)≤4194304*φ/(p^2*θ^3) := by
  have hd : 0<p^2*θ^3 := by positivity
  have he : 128*(θ+φ)/((p/128)^2*θ^3)=2097152*(θ+φ)/(p^2*θ^3) := by ring
  rw [he]
  apply (div_le_div_iff_of_pos_right hd).mpr
  nlinarith

lemma small_transport_near_scalar {I h p θ φ : ℝ} (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (ht : 0<θ) (hf : 0<φ) (ht1 : θ≤1) (hf1 : φ≤1) :
    (4194304*φ/(p^2*θ^3))*(I*h*p^3*θ^2*φ^2)≤
      (4194304*I*h*p^2*φ^2)*(1/(p*θ^2)) := by
  have hx : φ*θ≤1 := by nlinarith [mul_le_mul_of_nonneg_left ht1 hf.le]
  calc
    _=(4194304*I*h*p^2*φ^2)*(1/(p*θ^2))*(φ*θ) := by field_simp
    _≤(4194304*I*h*p^2*φ^2)*(1/(p*θ^2))*1 :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _=_ := mul_one _

lemma small_transport_exception_model_sum {P I p : ℝ} (hP : 0<P) (hI : 0≤I) (hp : 0<p) :
    (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
      if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0)≤
      ENNReal.ofReal (33554432*I*p^3/P^2) := by
  have hc : 0≤4194304*I*p^2 := by positivity
  have hr (nf nt : ℕ) : (∑'nr : ℕ,if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
        (1/(p*(cappedRepresentative nt)^2))) else 0)≤
        ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)))*
          ENNReal.ofReal (2/P^2) := by
    have hc' : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)) := by positivity
    have he (nr : ℕ) : (if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0)=
          ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)))*
            ENNReal.ofReal (if cappedRepresentative nr≤1/P^2 then cappedRepresentative nr else 0) := by
      split_ifs with h
      · rw [←ENNReal.ofReal_mul hc']
        congr 1
        ring
      · simp
    simp_rw [he,ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl ((capped_linear_tail_sum (by positivity : 0<(1:ℝ)/P^2)).trans_eq (by congr 1; ring))
  have ht (nf : ℕ) : (∑'nt : ℕ,∑'nr : ℕ,
      if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0)≤
      ENNReal.ofReal (16777216*I*p^3/P^2*(cappedRepresentative nf)^2) := by
    have hc' : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2) := by positivity
    calc
      _≤ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2))*
          (∑'nt : ℕ,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then 1/(p*(cappedRepresentative nt)^2) else 0)) := by
        rw [←ENNReal.tsum_mul_left]
        apply ENNReal.tsum_le_tsum
        intro nt
        split_ifs with hnt
        · apply (hr nf nt).trans_eq
          rw [←ENNReal.ofReal_mul (by positivity : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2))),←ENNReal.ofReal_mul hc']
          congr 1
          ring
        · simp
      _≤ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2))*ENNReal.ofReal (2*p) :=
        mul_le_mul' le_rfl (capped_inverse_square_floor_tsum hp)
      _=_ := by rw [←ENNReal.ofReal_mul hc']; congr 1; ring
  have hsq : (∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2))≤2 := by
    have hh := capped_square_tail_sum (by norm_num : (0:ℝ)<1)
    simpa only [ite_eq_left (cappedRepresentative_le_one _),one_pow,ENNReal.ofReal_ofNat,mul_one] using hh
  calc
    _≤∑'nf : ℕ,ENNReal.ofReal (16777216*I*p^3/P^2*(cappedRepresentative nf)^2) := ENNReal.tsum_le_tsum ht
    _=ENNReal.ofReal (16777216*I*p^3/P^2)*(∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2)) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0≤16777216*I*p^3/P^2),ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal (16777216*I*p^3/P^2)*2 := mul_le_mul' le_rfl hsq
    _=_ := by rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by positivity : 0≤16777216*I*p^3/P^2)]; congr 1; ring

def smallTransportCoefficient (k : Fin 4→ℕ) : ℝ :=
  4194304*cappedRepresentative (k 2)/((sourceRepresentative (k 0))^2*(cappedRepresentative (k 1))^3)

lemma smallTransportCoefficient_nonneg (k : Fin 4→ℕ) : 0 ≤ smallTransportCoefficient k := by
  have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  unfold smallTransportCoefficient
  positivity

lemma physicalDirectTransportDensity_representative_small {s : Solution} {X V : ℝ→Vec}
    {T w a b : ℝ} (hs : EnergyPrefix s T) (ha : 0≤a) (hb : b≤T)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    (z : ConeCoordinate) (hz : z∈physicalBinBase V (representativeClosedBin T w k) (Icc a b)) :
    physicalDirectTransportDensity s X V (representativeClosedBin T w k) z≤
      ENNReal.ofReal (smallTransportCoefficient k)*
        physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
  have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  have hrad : 0<z.1-z.2.1 := (representativeClosedBin_radius_pos T w k).trans_le hz.2.2.1.1
  have hh := physicalDirectTransportDensity_bound (s:=s) (X:=X) (V:=V) hrad
    (show 0<sourceRepresentative (k 0)/128 by positivity) ht hf.le
    (B:=representativeClosedBin T w k) le_rfl le_rfl le_rfl hz.2.2.2.2.2
    (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans ((Icc_subset_Icc ha hb) hz.1).2⟩ _)
  exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (small_transport_coefficient hp ht hf hsmall)) le_rfl)

lemma PhaseFlowOn.directTransport_representative_small {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (k : Fin 4→ℕ) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (smallTransportCoefficient k)*representativeCentralCost s F zX w k a b := by
  have hV := ((F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))).snd.measurable
  unfold representativeCentralCost
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) measurableSet_Icc)] with z hz
  exact physicalDirectTransportDensity_representative_small hs ha hb k hsmall z hz

lemma Admissible.small_transport_regular_radial {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nt nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative nt≤cappedRepresentative nf/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nr : ℕ,ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
        representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*Real.sqrt I*representativeSharedRadius s F zX P M A w a b I (np,nf)*
        cappedRepresentative nf/(sourceRepresentative np*(cappedRepresentative nt)^2)) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_central_shared T₀
  refine ⟨25165824*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nt nf a b I w hzX ha hb hI hJI hw hsmall HZ
  let p := sourceRepresentative np
  let θ := cappedRepresentative nt
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  let c := 4194304*φ/(p^2*θ^3)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have ht : 0<θ := cappedRepresentative_pos nt
  have hf : 0<φ := cappedRepresentative_pos nf
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hc : 0≤c := by dsimp [c]; positivity
  change (∑'nr : ℕ,ENNReal.ofReal c*representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b)≤_
  rw [ENNReal.tsum_mul_left]
  have hr : (∑'nr : ℕ,representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal C*ENNReal.ofReal (6*Real.sqrt I*R*p*θ) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min (I*cappedRepresentative nr*p^3*θ^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hsmall HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min (I*cappedRepresentative nr*p^3*θ^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤_ := mul_le_mul' le_rfl (central_shared_radial_sum hI hR hp ht hf)
  apply (mul_le_mul' le_rfl hr).trans_eq
  rw [←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul hc]
  congr 1
  dsimp only [c,R,p,θ,φ] at *
  field_simp
  ring

lemma Admissible.small_transport_exception_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative np≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
          ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
            representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*(sourceRepresentative np)^3/P^2) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_central_near T₀
  refine ⟨33554432*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
        ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
          representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) := by
    by_cases ht : 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16
    · rw [ite_eq_left ht,ite_eq_left ht.1]
      by_cases hr : regularCentralIndex P M A I w ![np,nt,nf,nr]
      · simp only [representativeExceptionCentralCost,ite_eq_left hr,mul_zero]
        exact bot_le
      · have hreg : ¬(512/min p w<cappedRepresentative nf ∨
            min I (stabilityLength P 16384 M A p w (cappedRepresentative nf))<cappedRepresentative nr) := by
          simpa [regularCentralIndex,p] using hr
        have hf : cappedRepresentative nf≤512/min p w := le_of_not_gt (not_or.mp hreg).1
        have hnr : cappedRepresentative nr≤1/P^2 :=
          ((le_of_not_gt (not_or.mp hreg).2).trans (min_le_right _ _)).trans
            (small_deficit_stabilityLength hP hM hp hw (cappedRepresentative_pos _) hf)
        rw [ite_eq_left hnr,representativeExceptionCentralCost,ite_eq_right hr]
        have hc := smallTransportCoefficient_nonneg ![np,nt,nf,nr]
        apply (mul_le_mul' le_rfl (hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI)).trans
        rw [←ENNReal.ofReal_mul hc,←ENNReal.ofReal_mul hCn]
        apply ENNReal.ofReal_le_ofReal
        have hn := mul_le_mul_of_nonneg_left (small_transport_near_scalar hI.le
          (cappedRepresentative_pos nr).le hp (cappedRepresentative_pos nt) (cappedRepresentative_pos nf)
          (cappedRepresentative_le_one _) (cappedRepresentative_le_one _)) hCn
        simpa only [smallTransportCoefficient,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk,
          p,mul_left_comm,mul_assoc] using hn
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
            (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
            (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (33554432*I*p^3/P^2) :=
      mul_le_mul' le_rfl (small_transport_exception_model_sum hP hI.le hp)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring

lemma Admissible.small_transport_regular_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative np≤cappedRepresentative nt ∧
        cappedRepresentative nt≤cappedRepresentative nf/16 then
        ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
          representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt I*representativeSharedRadius s F zX P M A w a b I (np,nf)*
          sourceRepresentative np*cappedRepresentative nf) := by
  obtain ⟨C,hC,hbound⟩ := hd.small_transport_regular_radial T₀
  refine ⟨2*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw HZ
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hc : 0≤C*Real.sqrt I*R*φ := by positivity
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
      ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
        representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (C*Real.sqrt I*R*φ)*
        (∑'nt : ℕ,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then 1/(p*(cappedRepresentative nt)^2) else 0)) := by
    rw [←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro nt
    by_cases ht : 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16
    · simp only [ite_eq_left ht,ite_eq_left ht.1]
      apply (hbound M A P hM hA hP s T F hs hT hTT zX np nt nf a b I w
        hzX ha hb hI hJI hw ht.2 HZ).trans_eq
      rw [←ENNReal.ofReal_mul hc]
      congr 1
      dsimp only [R,φ,p]
      ring
    · simp only [ite_eq_right ht,tsum_zero]
      exact bot_le
  apply hsum.trans
  calc
    _≤ENNReal.ofReal (C*Real.sqrt I*R*φ)*ENNReal.ofReal (2*p) :=
      mul_le_mul' le_rfl (capped_inverse_square_floor_tsum hp)
    _=_ := by rw [←ENNReal.ofReal_mul hc]; congr 1; ring


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.small_transport_regular_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
          representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.small_transport_regular_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
          representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
          representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P hM hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn hCc
      simpa only [mul_assoc] using hh)



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma sourceRepresentative_cube_sum {P : ℝ} (hP : 0≤P) (S : Finset ℕ)
    (hS : ∀np∈S,sourceRepresentative np≤P) :
    (∑np∈S,(sourceRepresentative np)^3)≤2*P^3 := by
  have hp (np : ℕ) : 0 ≤ sourceRepresentative np := by unfold sourceRepresentative; positivity
  calc
    _≤∑np∈S,P^2*sourceRepresentative np := by
      apply Finset.sum_le_sum
      intro np hn
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hp np) (hS np hn) 2) (hp np)
      nlinarith only [hh]
    _=P^2*(∑np∈S,sourceRepresentative np) := (Finset.mul_sum ..).symm
    _≤P^2*(2*P) := mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP S hS) (sq_nonneg P)
    _=2*P^3 := by ring

lemma Admissible.small_transport_exception_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
            representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*I*P) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.small_transport_exception_triple_sum T₀
  refine ⟨2*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX a b I w ha hb hI hJI hw
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if 1/sourceRepresentative np≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
      ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
        representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0
  have hc : 0≤Cn*I/P^2 := by positivity
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
          representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal (Cn*I*(sourceRepresentative np)^3/P^2) := by
      apply Finset.sum_le_sum
      intro np hn
      exact hnear M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
    _=ENNReal.ofReal ((Cn*I/P^2)*(∑np∈U,(sourceRepresentative np)^3)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun np _=>by unfold sourceRepresentative; positivity)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro np hn
      ring
    _≤ENNReal.ofReal ((Cn*I/P^2)*(2*P^3)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sourceRepresentative_cube_sum hP.le U hU) hc)
    _=_ := by congr 1; field_simp



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma tsum_representativeSmallSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(representativeSmallSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧
          cappedRepresentative nt≤cappedRepresentative n.2/16 then f ![n.1,nt,n.2,nr] else 0) n := by
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2
  · rw [indicator_of_mem (show n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2} from hn)]
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈representativeSmallSector P) ↔
        1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧ _ ∧ _) ↔ _
      simp only [hn.1,true_and,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simp only [indicator_apply,hi]
  · rw [indicator_of_notMem (show n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2} from hn)]
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    intro hk
    have hc := representativeSmallSector_subset_centralIndexSector P hk
    exact hn ⟨hc.1,hc.2.1⟩

lemma Admissible.small_transport_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∑'k : Fin 4→ℕ,(representativeSmallSector P).indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectTransportDensity s X V (representativeClosedBin T w k) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hregular⟩ := hd.small_transport_regular_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.small_transport_exception_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  let R := representativeSmallSector P
  let c := fun k=>ENNReal.ofReal (smallTransportCoefficient k)
  let g := fun k=>c k*representativeRegularCentralCost s F zX P M A I w k a b
  let e := fun k=>c k*representativeExceptionCentralCost s F zX P M A I w k a b
  have hdom : (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b)) k)≤
      (∑'k,R.indicator g k)+(∑'k,R.indicator e k) := by
    rw [←ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      apply (F.directTransport_representative_small hs.energyPrefix hT zX k ha hb hk.2.2).trans_eq
      rw [central_cost_eq_regular_add_exception (P:=P) (M:=M) (A:=A) (I:=I),mul_add]
    · simp only [indicator_of_notMem hk,add_zero,le_refl]
  have hr : (∑'k,R.indicator g k)≤ENNReal.ofReal (Cr*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    exact hregular M A P (zero_lt_one.trans_le hM) hA hP hL s T F hs hT hTT zX a b I w
      hzX ha hb hI hJI hw hwP HZ
  have he : (∑'k,R.indicator e k)≤ENNReal.ofReal (Ce*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    apply (hexception M A P hM (zero_lt_one.trans_le hP) s T F hs hT hTT zX a b I w ha hb hI hJI hw).trans
    apply ENNReal.ofReal_le_ofReal
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    have hip : I*P≤P*Real.sqrt I := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (zero_le_one.trans hP)
    have hh : I*P≤B := hip.trans (le_add_of_nonneg_right (by positivity))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hCe
  apply (hdom.trans (add_le_add hr he)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]
  congr 1
  ring

end RVM

end

end OAI
