import Mathlib
import OAI.Analysis.CoulombRadii.Screening.InnerCap

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma exists_inner_shell_mesh : ∃ M : ℕ, ∀ {u : ℝ}, 0<u → ∃ z : Fin M → Space,
    (∀ i, u≤‖z i‖ ∧ ‖z i‖≤2*u) ∧
    (∀ w : Space, u≤‖w‖ → ‖w‖≤2*u → ∃ i, ‖w-z i‖≤atomicCellScale (z i)) := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (α:=1) (β:=2) (by norm_num)
  let e := Fintype.equivFin {z : Space // z∈t}
  refine ⟨Fintype.card {z : Space // z∈t},?_⟩
  intro u hu
  refine ⟨(fun i => u • (e.symm i).val),?_,?_⟩
  · intro i
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    have H := ht (e.symm i).val (e.symm i).property
    constructor <;> nlinarith [H.1,H.2]
  · intro w hw1 hw2
    have hn : ‖u⁻¹ • w‖=‖w‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    obtain ⟨v,hv,Hv⟩ := hcover (u⁻¹ • w)
      (by rw [hn]; exact (one_le_div hu).mpr hw1)
      (by rw [hn]; exact (div_le_iff₀ hu).mpr hw2)
    refine ⟨e ⟨v,hv⟩,?_⟩
    simp only [Equiv.symm_apply_apply,atomicCellScale_smul hu.le]
    have he : w-u • v=u • (u⁻¹ • w-v) := by simp [smul_sub,smul_smul,hu.ne']
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    exact mul_le_mul_of_nonneg_left Hv.le hu.le

def innerMeshCap {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) : ℝ :=
  Real.sqrt (∑ i, (innerLocalCap S v x h (z i) (atomicCellScale (z i)))^2)
lemma innerMeshCap_nonneg {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) :
    0 ≤ innerMeshCap S v x h z := Real.sqrt_nonneg _
lemma innerMeshCap_sq {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) :
    (innerMeshCap S v x h z)^2=∑ i, (innerLocalCap S v x h (z i) (atomicCellScale (z i)))^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
lemma innerLocalCap_le_mesh {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) (i : Fin M) :
    innerLocalCap S v x h (z i) (atomicCellScale (z i)) ≤ innerMeshCap S v x h z := by
  apply (sq_le_sq₀ (innerLocalCap_nonneg _ _ _ _ _ _) (innerMeshCap_nonneg _ _ _ _ _)).mp
  rw [innerMeshCap_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (innerLocalCap S v x h (z j) (atomicCellScale (z j)))) (Finset.mem_univ i)
lemma innerMeshCap_normalized_slice_aestronglyMeasurable {J m k M : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (s : Spins m) (h : ℝ) (z : Fin M → Space) :
    AEStronglyMeasurable (fun x => innerMeshCap S (v.coreSlice s x).normalized x h z) volume := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    (innerLocalCap_normalized_slice_aestronglyMeasurable S v s h _ _).pow 2)
lemma innerMeshCap_bound {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) (hz : ∀ i, z i≠0)
    (hnuc : ∀ i j, 4*atomicCellScale (z i)≤‖S.position j-z i‖) :
    innerMeshCap S v x h z ≤ Real.sqrt (∑ i, 8*(totalCharge S/(2*atomicCellScale (z i)))^2) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i hi
  have H := innerLocalCap_le S v x h (z i) (atomicCellScale_pos (hz i)) (hnuc i)
  exact (pow_le_pow_left₀ (innerLocalCap_nonneg _ _ _ _ _ _) H 2).trans_eq (Real.sq_sqrt (by positivity))
lemma innerMeshCap_weight_integrable {J m k M : ℕ} (S : Nuclei J) (v : H1Vector (m+k))
    (s : Spins m) (h : ℝ) (z : Fin M → Space) (hz : ∀ i, z i≠0)
    (hnuc : ∀ i j, 4*atomicCellScale (z i)≤‖S.position j-z i‖) (q : ℕ) :
    Integrable (fun x => mass (v.coreSlice s x)*(innerMeshCap S (v.coreSlice s x).normalized x h z)^q) := by
  apply (mass_coreSlice_integrable v s).mul_bdd ((innerMeshCap_normalized_slice_aestronglyMeasurable S v s h z).pow q)
  filter_upwards [] with x
  change ‖(innerMeshCap S (v.coreSlice s x).normalized x h z)^q‖ ≤
    (Real.sqrt (∑ i, 8*(totalCharge S/(2*atomicCellScale (z i)))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (innerMeshCap_nonneg _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (innerMeshCap_nonneg _ _ _ _ _) (innerMeshCap_bound S _ x h z hz hnuc) q

namespace RecordedEnsemble
variable {n J : ℕ}

structure InnerEnvelope (T : RecordedEnsemble n) (S : Nuclei J) (h u : ℝ) where
  value : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ
  nonneg : ∀ p s x, 0≤value p s x
  measurable : ∀ p s, AEStronglyMeasurable (value p s) volume
  integrable : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*value p s x)
  square_integrable : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(value p s x)^2)
  dominates : ∀ p s x w, u≤‖w‖ → ‖w‖≤2*u →
    max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0 ≤ value p s x

theorem exists_inner_shell_envelope : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (T : RecordedEnsemble n) {u h K : ℝ}, 0<u → h≤u/4 → 0≤K →
      (∀ w : Space, u/2≤‖w‖ → ‖w‖≤4*u → Real.sqrt (T.innerSquare S h w)≤K) →
      ∃ M : T.InnerEnvelope S h u, T.dataRMS M.value ≤ C*K := by
  obtain ⟨Q,HQ⟩ := exists_inner_shell_mesh
  refine ⟨Real.sqrt (8*(Q:ℝ)),Real.sqrt_nonneg _,?_⟩
  intro J n S hatom T u h K hu hh hK hpoint
  obtain ⟨z,hzbound,hcover⟩ := HQ hu
  have hz i : z i≠0 := norm_pos_iff.mp (hu.trans_le (hzbound i).1)
  have hnuc i j : 4*atomicCellScale (z i)≤‖S.position j-z i‖ := by
    rw [hatom j,zero_sub,norm_neg]
    unfold atomicCellScale
    linarith [norm_nonneg (z i)]
  have hcore i q (hq : q∈Metric.ball (0:Space) h) : 4*atomicCellScale (z i)≤‖q-z i‖ := by
    have hn : ‖q‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hq
    have H : ‖z i‖≤‖q-z i‖+‖q‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle (z i) q 0
    unfold atomicCellScale
    linarith [(hzbound i).1]
  let M : T.InnerEnvelope S h u := {
    value := fun p s x => innerMeshCap S ((T.vector p).coreSlice s x).normalized x h z
    nonneg := fun p s x => innerMeshCap_nonneg _ _ _ _ _
    measurable := fun p s => innerMeshCap_normalized_slice_aestronglyMeasurable S (T.vector p) s h z
    integrable := fun p s => by simpa only [pow_one] using innerMeshCap_weight_integrable S (T.vector p) s h z hz hnuc 1
    square_integrable := fun p s => innerMeshCap_weight_integrable S (T.vector p) s h z hz hnuc 2
    dominates := fun p s x w hw1 hw2 => by
      obtain ⟨i,hi⟩ := hcover w hw1 hw2
      exact (innerLocalCap_dominates S _ x h (z i) w (atomicCellScale_pos (hz i)) hi (hcore i) (hnuc i)).trans
        (innerLocalCap_le_mesh S _ x h z i) }
  refine ⟨M,?_⟩
  have hwbound i w (hw : ‖w-z i‖≤2*atomicCellScale (z i)) : u/2≤‖w‖ ∧ ‖w‖≤4*u := by
    have H1 : ‖z i‖≤‖w-z i‖+‖w‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle (z i) w 0
    have H2 : ‖w‖≤‖w-z i‖+‖z i‖ := by simpa only [dist_eq_norm,sub_zero] using dist_triangle w (z i) 0
    unfold atomicCellScale at hw
    constructor <;> linarith [(hzbound i).1,(hzbound i).2]
  have hsep i w (hw : ‖w-z i‖≤2*atomicCellScale (z i)) q (hq : q∈Metric.ball (0:Space) h) : u/4≤‖q-w‖ := by
    have hn : ‖q‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hq
    have H : ‖w‖≤‖q-w‖+‖q‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle w q 0
    linarith [(hwbound i w hw).1]
  have hic i : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h (z i) (atomicCellScale (z i)))^2))≤8*K^2 := by
    apply T.innerLocalCap_second_moment S h (z i) (atomicCellScale_pos (hz i)) (show 0<u/4 by positivity)
      (hnuc i) (hsep i)
    intro w hw
    have H := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpoint w (hwbound i w hw).1 (hwbound i w hw).2) 2
    simpa only [Real.sq_sqrt (T.innerSquare_nonneg S h w)] using H
  have he : (T.dataRMS M.value)^2=∑ i, ∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h (z i) (atomicCellScale (z i)))^2) := by
    rw [T.dataRMS_sq]
    simp only [M,innerMeshCap_sq,sliceExpectation,Finset.mul_sum]
    conv_lhs => arg 2; ext p; arg 2; ext s; rw [integral_finsetSum _ (fun i _ =>
      innerLocalCap_weight_integrable S (T.vector p) s h (z i) (atomicCellScale_pos (hz i)) (hnuc i) 2)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hic i)
  rw [←he] at H
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  apply (sq_le_sq₀ (T.dataRMS_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hK)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤8*Q)]
  nlinarith

end RecordedEnsemble
end Coulomb
end

end

end OAI
