import OAI.Dynamics.StandardMap.BridgeMean

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def unitClip (x : ℝ) : ℝ := max 0 (min 1 x)
lemma unitClip_mem (x : ℝ) : unitClip x∈Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma unitClip_eq {x : ℝ} (hx : x∈Icc (0:ℝ) 1) : unitClip x=x := by
  dsimp [unitClip]; rw [min_eq_right hx.2,max_eq_right hx.1]
lemma unitClip_lipschitz : LipschitzWith 1 unitClip := by
  exact ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_min 1).const_max 0
lemma bounded_square_lipschitz {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) : |a^2-b^2|≤2*|a-b| := by
  have hab : |a+b|≤2 := (abs_add_le a b).trans (by linarith)
  rw [show a^2-b^2=(a-b)*(a+b) by ring,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg (a-b))]
noncomputable def testObservation (x : Fin 3 → ℝ) : ℝ :=
  x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2
lemma testObservation_lipschitz : LipschitzWith 6 testObservation := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc (j : Fin 3) : |x j-y j|≤dist x y := by
    simpa only [Real.dist_eq,one_mul,NNReal.coe_one] using (LipschitzWith.eval j).dist_le_mul x y
  have hd (j : Fin 3) : |unitClip (x j)-unitClip (y j)|≤dist x y := by
    have hh := unitClip_lipschitz.dist_le_mul (x j) (y j)
    simp only [Real.dist_eq,one_mul,NNReal.coe_one] at hh
    exact hh.trans (hc j)
  have hxy (z : Fin 3 → ℝ) : |unitClip (z 1)-unitClip (z 2)|≤1 := by
    rw [abs_le]
    have h1 := unitClip_mem (z 1)
    have h2 := unitClip_mem (z 2)
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hdiff : |(unitClip (x 1)-unitClip (x 2))-(unitClip (y 1)-unitClip (y 2))|≤2*dist x y := by
    calc
      _ = |(unitClip (x 1)-unitClip (y 1))-(unitClip (x 2)-unitClip (y 2))| := by congr 1; ring
      _ ≤ |unitClip (x 1)-unitClip (y 1)|+|unitClip (x 2)-unitClip (y 2)| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (unitClip (x 1)-unitClip (y 1)) 0 (unitClip (x 2)-unitClip (y 2))
      _ ≤ _ := by linarith [hd 1,hd 2]
  have hsq := (bounded_square_lipschitz (hxy x) (hxy y)).trans (mul_le_mul_of_nonneg_left hdiff (by norm_num))
  have hlin : |(x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2)|≤2*dist x y := by
    calc
      _ = |(x 0-y 0)-((x 1-y 1)+(x 2-y 2))/2| := by congr 1; ring
      _ ≤ |x 0-y 0|+|((x 1-y 1)+(x 2-y 2))/2| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (x 0-y 0) 0 (((x 1-y 1)+(x 2-y 2))/2)
      _ = |x 0-y 0|+|(x 1-y 1)+(x 2-y 2)|/2 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ _ := by linarith [abs_add_le (x 1-y 1) (x 2-y 2),hc 0,hc 1,hc 2]
  rw [Real.dist_eq]
  change |(x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2)-
    (y 0-(y 1+y 2)/2+(unitClip (y 1)-unitClip (y 2))^2)|≤(6:ℝ)*dist x y
  have hab := abs_add_le ((x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2))
    ((unitClip (x 1)-unitClip (x 2))^2-(unitClip (y 1)-unitClip (y 2))^2)
  have he : (x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2)-
      (y 0-(y 1+y 2)/2+(unitClip (y 1)-unitClip (y 2))^2)=
    ((x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2))+
    ((unitClip (x 1)-unitClip (x 2))^2-(unitClip (y 1)-unitClip (y 2))^2) := by ring
  rw [he]
  linarith
noncomputable def testLeft (s t : DyadicTime) : Fin 3 → DyadicTime := ![s,s,dyadicMid s t]
noncomputable def testRight (s t : DyadicTime) : Fin 3 → DyadicTime := ![t,dyadicMid s t,t]
lemma testObservation_eq_arrayTest (j : ArrayTestIndex) (d : DistanceArray)
    (h1 : arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d∈Icc (0:ℝ) 1)
    (h2 : arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d∈Icc (0:ℝ) 1) :
    testObservation (fun i => arrayShortfall (testLeft j.val.1 j.val.2 i) (testRight j.val.1 j.val.2 i) d)=arrayTest j d := by
  change arrayShortfall j.val.1 j.val.2 d-
    (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d+arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d)/2+
    (unitClip (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)-unitClip (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d))^2=_
  rw [unitClip_eq h1,unitClip_eq h2]
  rfl
end StandardMapEntropy

end OAI
