import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScreenNumeric

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

theorem AtomicCutHistory.append_normalized {J n k : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a q : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) (hP : 1 ≤ P) (ha : 0<a) (hq : 1 ≤ q)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2)
    (T : AtomicCutHistory S ψ k) (hT : ∀ i, AtomicScaleWindow a q (T.target i))
    (y : Space) (hy : AtomicScaleWindow a q y) :
    ∃ U : AtomicCutHistory S ψ (k+1), U.target=Fin.snoc T.target y ∧
      (∀ i, AtomicScaleWindow a q (U.target i)) ∧
      (∀ G : ℝ, 0 ≤ G →
        (∀ c v, ‖v-U.center c‖ ≤ 2*atomicCellScale (U.center c) →
          U.ensemble.rawSquare S v (atomicCellScale v) ≤ (screenFieldUnit δ P a*G)^2) →
        (Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/screenFieldUnit δ P a)^2 ≤
          16*ballTrialCoefficient*(4*q)^8*
            (1+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+
              3*(Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh}):ℝ)*G+
              (Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh}):ℝ)^3)) := by
  have hy0 := hy.nonzero ha
  have hq0 : 0<q := by linarith
  obtain ⟨U,ht,hgain⟩ := T.append hatom hm hE hstate hy0
  have hU (i) : AtomicScaleWindow a q (U.target i) := by
    rw [ht]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [Fin.snoc_last] using hy
    · simpa only [Fin.snoc_castSucc] using hT i
  refine ⟨U,ht,hU,?_⟩
  intro G hG hraw
  let Q := 4*q
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hQ0 : 0<Q := by linarith
  have hyQ : AtomicScaleWindow a Q y := hy.enlarge ha.le (by dsimp [Q]; linarith)
  have hUQ (i) : AtomicScaleWindow a Q (U.target i) := (hU i).enlarge ha.le (by dsimp [Q]; linarith)
  have hcQ (c) : AtomicScaleWindow a Q (U.center c) := by
    exact ((hU c.1).mesh hq0.le c.2.property).enlarge ha.le (by dsimp [Q]; linarith)
  have hp0 : 0 ≤ P := by linarith
  have he : 0<screenEnergy δ a := screenEnergy_pos δ ha
  have hPQ : 1 ≤ P*Q^7 := one_le_mul_of_one_le_of_one_le hP (one_le_pow₀ hQ)
  have hδe : δ ≤ P*Q^7*screenEnergy δ a :=
    (screenEnergy_ge_offset hδ ha).trans (le_mul_of_one_le_left he.le hPQ)
  have HI (i) : atomicIMS ψ (U.target i) ≤ atomicIMSConstant*P*Q^7*screenEnergy δ a := by
    apply (atomicIMS_le_units ψ hm hδ hP hc (U.nonzero i)).trans
    convert mul_le_mul_of_nonneg_left ((hUQ i).energy ha hQ hδ)
      (mul_nonneg atomicIMSConstant_nonneg hp0) using 1
    ring
  have hisum : (∑ i, atomicIMS ψ (U.target i)) ≤ (k+1:ℕ)*atomicIMSConstant*P*Q^7*screenEnergy δ a := by
    have H := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => HI i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using H
  have hbase : (screenBaseMass (atomicCellScale y))^2/atomicCellScale y ≤ screenEnergy δ (atomicCellScale y) := by
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (screenBaseMass_nonneg _) (screenMass_ge_base _ _) 2)
      (atomicCellScale_nonneg _)
  have henergy : screenEnergy δ (atomicCellScale y) ≤ P*Q^7*screenEnergy δ a :=
    calc
      _ ≤ Q^7*screenEnergy δ a := hyQ.energy ha hQ hδ
      _ ≤ P*(Q^7*screenEnergy δ a) := le_mul_of_one_le_left (mul_nonneg (pow_nonneg hQ0.le _) he.le) hP
      _ = _ := by ring
  have hbase' : 4*ballTrialCoefficient*(screenBaseMass (atomicCellScale y))^2/atomicCellScale y ≤
      4*ballTrialCoefficient*P*Q^7*screenEnergy δ a := by
    have H := mul_le_mul_of_nonneg_left (hbase.trans henergy) (show 0 ≤ 4*ballTrialCoefficient by positivity [ballTrialCoefficient_pos])
    simpa only [mul_div_assoc,mul_assoc] using H
  have hcost := atomic_cell_cost_units ψ hδ hP ha hQ hG U.center hcQ hc
  have HG := hgain ((screenFieldUnit δ P a*G)^2) hraw
  let L : ℝ := Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh})
  have HG' : atomicCellScale y/(16*ballTrialCoefficient)*T.ensemble.rawSquare S y (atomicCellScale y) ≤
      P*Q^7*screenEnergy δ a*(1+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+3*L*G+L^3) := by
    dsimp [L]
    nlinarith [hδe,hisum,hbase',hcost]
  exact screening_gain_normalized ha (atomicCellScale_pos hy0) hQ0 ballTrialCoefficient_pos
    (screenFieldUnit_pos hP ha) (T.ensemble.rawSquare_nonneg S y _) hyQ.1
    (screenFieldUnit_square hp0 ha) HG'

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def atomicRecursionA : ℝ := max 1 (16*ballTrialCoefficient*
  (1+atomicIMSConstant+4*ballTrialCoefficient+
    3*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)+
    (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)^3))

def atomicRecursionC : ℝ := atomicRecursionA*524288

lemma atomicRecursionC_ge_four : 4 ≤ atomicRecursionC := by
  have h : 1 ≤ atomicRecursionA := le_max_left _ _
  unfold atomicRecursionC
  linarith

lemma AtomicCutHistory.rawSquare_le_next_sup {J n k j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {a w : ℝ} (ha : 0<a) (hw : 0<w) (hk : k≤j)
    (U : AtomicCutHistory S ψ (k+1))
    (hU : ∀ i, AtomicScaleWindow a (4^j) (U.target i))
    (c) (v : Space) (hv : ‖v-U.center c‖ ≤ 2*atomicCellScale (U.center c)) :
    U.ensemble.rawSquare S v (atomicCellScale v) ≤
      (w*atomicRawSup S ψ a w (j+1))^2 := by
  have hq : (4:ℝ)^j ≤ 4^(j+1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0:ℝ)≤4 by norm_num) j]
  have htargets (i) : AtomicScaleWindow a (4^(j+1)) (U.target i) :=
    (hU i).enlarge ha.le hq
  have hvw : AtomicScaleWindow a (4^(j+1)) v := by
    have H := (hU c.1).mesh_near (by positivity) c.2.property hv
    simpa only [pow_succ,mul_comm (4:ℝ)] using H
  have H : Real.sqrt (U.ensemble.rawSquare S v (atomicCellScale v))/w ≤
      atomicRawSup S ψ a w (j+1) :=
    le_csSup (atomicRawValues_bdd S hatom ψ hm ha hw (j+1))
      (Set.mem_insert_of_mem _ ⟨k+1,Nat.add_le_add_right hk 1,U,htargets,v,hvw,rfl⟩)
  have HH := (div_le_iff₀ hw).mp H
  rw [mul_comm] at HH
  exact ((Real.sqrt_le_iff).mp HH).2

lemma atomicRawValues_recursion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    ∀ r∈atomicRawValues S ψ a (screenFieldUnit δ P a) j,
      r^2 ≤ atomicRecursionC^(j+1)*(1+atomicRawSup S ψ a (screenFieldUnit δ P a) (j+1)) := by
  let w := screenFieldUnit δ P a
  have hw : 0<w := screenFieldUnit_pos hP ha
  let G := atomicRawSup S ψ a w (j+1)
  have hG : 0≤G := atomicRawSup_nonneg S hatom ψ hm ha hw (j+1)
  have hC : 0≤atomicRecursionC := le_trans (by norm_num) atomicRecursionC_ge_four
  intro r hr
  rcases hr with (rfl|⟨k,hk,T,hT,y,hy,rfl⟩)
  · simpa only [zero_pow (by omega : 2≠0)] using mul_nonneg (pow_nonneg hC (j+1)) (by linarith : 0≤1+G)
  obtain ⟨U,ht,hU,hgain⟩ := T.append_normalized S hatom ψ hm hE hstate hδ hP ha
    (one_le_pow₀ (by norm_num : (1:ℝ)≤4)) hc hT y hy
  have HG := hgain G hG (U.rawSquare_le_next_sup S hatom ψ hm ha hw hk hU)
  let M : ℝ := Fintype.card {z : Space // z∈atomicPatchMesh}
  let L : ℝ := Fintype.card (Fin (k+1) × {z : Space // z∈atomicPatchMesh})
  have hLM : L ≤ (j+1:ℕ)*M := by
    dsimp [L,M]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (Nat.cast_nonneg _)
  have Hpoly := screening_polynomial_bound atomicIMSConstant_nonneg ballTrialCoefficient_pos.le
    (show 0≤M by positivity) hG (Nat.cast_nonneg (k+1))
    (show 0≤L by positivity) (show (1:ℝ)≤(j+1:ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
    (show ((k+1:ℕ):ℝ)≤(j+1:ℕ) by exact_mod_cast Nat.add_le_add_right hk 1) hLM
  have hA : 16*ballTrialCoefficient*(1+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3) ≤
      atomicRecursionA := le_max_right _ _
  calc
    _ ≤ 16*ballTrialCoefficient*(4*4^j)^8*
        (1+(k+1:ℕ)*atomicIMSConstant+4*ballTrialCoefficient+3*L*G+L^3) := HG
    _ ≤ 16*ballTrialCoefficient*(4*4^j)^8*
        ((1+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3)*(j+1:ℕ)^3*(1+G)) :=
      mul_le_mul_of_nonneg_left Hpoly (by positivity [ballTrialCoefficient_pos])
    _ = (16*ballTrialCoefficient*(1+atomicIMSConstant+4*ballTrialCoefficient+3*M+M^3))*
        ((4:ℝ)^(j+1))^8*(j+1:ℕ)^3*(1+G) := by rw [pow_succ]; ring
    _ ≤ atomicRecursionA*((4:ℝ)^(j+1))^8*(j+1:ℕ)^3*(1+G) := by
      gcongr
    _ ≤ atomicRecursionC^(j+1)*(1+G) :=
      mul_le_mul_of_nonneg_right (screening_exponential_majorant (le_max_left _ _) j) (by linarith)

theorem atomicRawSup_recursion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    (atomicRawSup S ψ a (screenFieldUnit δ P a) j)^2 ≤
      atomicRecursionC^(j+1)*(1+atomicRawSup S ψ a (screenFieldUnit δ P a) (j+1)) := by
  let B := atomicRecursionC^(j+1)*(1+atomicRawSup S ψ a (screenFieldUnit δ P a) (j+1))
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have hnonneg := atomicRawSup_nonneg S hatom ψ hm ha hw j
  have hbound : atomicRawSup S ψ a (screenFieldUnit δ P a) j ≤ Real.sqrt B := by
    apply csSup_le (atomicRawValues_nonempty _ _ _ _ _)
    intro r hr
    exact Real.le_sqrt_of_sq_le (atomicRawValues_recursion S hatom ψ hm hE hstate hδ hP ha hc j r hr)
  have hB : 0≤B := by
    apply mul_nonneg (pow_nonneg (le_trans (by norm_num) atomicRecursionC_ge_four) _)
    linarith [atomicRawSup_nonneg S hatom ψ hm ha hw (j+1)]
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans_eq (Real.sq_sqrt hB)

end Coulomb

end

end OAI
