import Mathlib
import OAI.Analysis.CoulombRadii.Packets.AnnularIMS
import OAI.Analysis.CoulombRadii.Packets.InnerMeshCap
import OAI.Analysis.CoulombRadii.FieldAnalysis.DyadicInnerRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem exists_atomic_deletion_envelope : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ,
      ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
        T.CoreSupported (imsShell 0 ((2:ℝ)^ell*t))ᶜ ∧
        T.OutSupported {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)} ∧
        T.totalMass=mass ψ ∧ T.totalForm S ≤ form S ψ+annularIMSCost ψ ((2:ℝ)^ell*t) ∧
        ∃ M : T.InnerEnvelope S (t/4) ((2:ℝ)^ell*t),
          T.dataRMS M.value ≤ C*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  obtain ⟨Ci,hCi,Hi⟩ := exists_atomic_annular_IMS_bound
  obtain ⟨Cf,hCf,Hf⟩ := annular_dyadic_inner_field Ci hCi
  obtain ⟨Cm,hCm,Hm⟩ := RecordedEnsemble.exists_inner_shell_envelope
  refine ⟨Cm*Cf,mul_nonneg hCm hCf,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell
  have hu : 0 < (2:ℝ)^ell*t := by positivity
  obtain ⟨T,hc,hf,ho,hcs,hos,hmas,he⟩ := exists_annular_recorded_ensemble S ψ hψ hu
  have hcost := Hi S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hu
  have Hpoint := Hf S hatom ψ hψ hm hE hstate ht ell T hc hf hos hmas (he.trans (add_le_add le_rfl hcost))
  have hpow : (1:ℝ) ≤ 2^ell := one_le_pow₀ (by norm_num)
  have hh : t/4 ≤ ((2:ℝ)^ell*t)/4 := by nlinarith
  have hK : 0 ≤ Cf*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
    exact div_nonneg (mul_nonneg (mul_nonneg hCf (screenMass_pos _ _).le) (by positivity)) hu.le
  obtain ⟨M,hM⟩ := Hm S hatom T hu hh hK Hpoint
  refine ⟨T,hc,hf,ho,hcs,hos,hmas,he,M,?_⟩
  exact hM.trans_eq (by ring)

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def deletionShell (t : ℝ) (j : ℕ) : Set Space :=
  {x | (2:ℝ)^j*t ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(j+1)*t}

def deletionShellWeight (t : ℝ) (w : Space → ℝ) (j : ℕ) : Space → ℝ :=
  (deletionShell t j).indicator w

lemma measurableSet_deletionShell (t : ℝ) (j : ℕ) : MeasurableSet (deletionShell t j) :=
  ((isClosed_le continuous_const continuous_norm).measurableSet).inter
    ((isOpen_lt continuous_norm continuous_const).measurableSet)

lemma deletionShellWeight_measurable {w : Space → ℝ} (hw : Measurable w) (t : ℝ) (j : ℕ) :
    Measurable (deletionShellWeight t w j) := hw.indicator (measurableSet_deletionShell t j)

lemma deletionShellWeight_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (t : ℝ) (j : ℕ) (y : Space) :
    0 ≤ deletionShellWeight t w j y := by
  exact Set.indicator_nonneg (fun y _ => hw y) y

lemma deletionShellWeight_le_one {w : Space → ℝ} (hw : ∀ y, w y ≤ 1) (t : ℝ) (j : ℕ) (y : Space) :
    deletionShellWeight t w j y ≤ 1 := by
  unfold deletionShellWeight
  by_cases hy : y∈deletionShell t j
  · rw [indicator_of_mem hy]; exact hw y
  · rw [indicator_of_notMem hy]; norm_num

lemma deletionShellWeight_supported (t : ℝ) (w : Space → ℝ) (j : ℕ) (y : Space)
    (hy : y∉imsShell 0 ((2:ℝ)^j*t)) : deletionShellWeight t w j y=0 := by
  apply indicator_of_notMem
  intro H
  apply hy
  simp only [imsShell,mem_ofPred_eq,sub_zero]
  refine ⟨H.1,?_⟩
  have : (2:ℝ)^(j+1)*t=2*((2:ℝ)^j*t) := by rw [pow_succ]; ring
  rw [←this]
  exact H.2.le

lemma deletionShellWeight_sum {t : ℝ} (ht : 0<t) (w : Space → ℝ) (k : ℕ) (y : Space) :
    (∑ j ∈ Finset.range k, deletionShellWeight t w j y)=
      if t ≤ ‖y‖ ∧ ‖y‖ < (2:ℝ)^k*t then w y else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,ih]
    have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have htk : t ≤ (2:ℝ)^k*t := by nlinarith
    have hnext : (2:ℝ)^k*t ≤ (2:ℝ)^(k+1)*t := by rw [pow_succ]; nlinarith
    simp only [deletionShellWeight,Set.indicator_apply,deletionShell,mem_ofPred_eq]
    split_ifs <;> simp_all <;> try omega
    all_goals nlinarith [mul_le_mul_of_nonneg_right hp ht.le, mul_le_mul_of_nonneg_right hnext ht.le]

lemma deletionShellWeight_sum_bound {t : ℝ} (ht : 0<t) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (k : ℕ) (y : Space) :
    |∑ j ∈ Finset.range k, deletionShellWeight t w j y| ≤ 1 := by
  rw [deletionShellWeight_sum ht]
  split_ifs
  · exact hw y
  · norm_num

lemma deletion_geometric_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j) ≤ 4 := by
  have he : (∑ j ∈ Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j)=
      4-(2*(k:ℝ)+4)*(1/2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [Finset.sum_range_succ,ih,pow_succ,Nat.cast_add,Nat.cast_one]; ring
  rw [he]
  have H : 0 ≤ (2*(k:ℝ)+4)*(1/2:ℝ)^k := by positivity
  linarith

end Coulomb
end

end

end OAI
