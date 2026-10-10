import Mathlib
import OAI.Probability.SKBarriers.Gaussian.SmoothFamily

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

abbrev ReplicaConfig (n d : ℕ) := Fin d → Config n

def replicaEnergy {n d : ℕ} (J : Disorder n) (s : ReplicaConfig n d) : ℝ :=
  ∑ a, hamiltonian J (s a)

def restrictedPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n) : ℝ :=
  ∑ s ∈ S, Real.exp (β*replicaEnergy J s)

def restrictedLogPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n) : ℝ :=
  Real.log (restrictedPartition β S J)

def replicaRow {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n)
    (s : ReplicaConfig n d) : ℝ := Real.exp (β*replicaEnergy J s)/restrictedPartition β S J

def replicaMarginal {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n)
    (x : Config n) : ℝ := ∑ s ∈ S, ∑ a : Fin d, if s a = x then replicaRow β S J s/(d:ℝ) else 0

theorem restrictedPartition_pos {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : 0 < restrictedPartition β S J :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hS

theorem replicaRow_nonneg {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) (s : ReplicaConfig n d) : 0 ≤ replicaRow β S J s :=
  div_nonneg (Real.exp_nonneg _) (restrictedPartition_pos β hS J).le

theorem replicaRow_sum {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : ∑ s ∈ S, replicaRow β S J s = 1 := by
  simp only [replicaRow,← Finset.sum_div]
  exact div_self (restrictedPartition_pos β hS J).ne'

theorem replicaMarginal_nonneg {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) (x : Config n) : 0 ≤ replicaMarginal β S J x := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact div_nonneg (replicaRow_nonneg β hS J s) (by positivity)
  · rfl

theorem replicaMarginal_sum {n d : ℕ} (hd : 0 < d) (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : ∑ x, replicaMarginal β S J x = 1 := by
  have H (s : ReplicaConfig n d) :
      (∑ x : Config n, ∑ a : Fin d, if s a = x then replicaRow β S J s/(d:ℝ) else 0) =
        replicaRow β S J s := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  unfold replicaMarginal
  rw [Finset.sum_comm]
  simp_rw [H]
  exact replicaRow_sum β hS J

theorem replicaMarginal_energy {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d))
    (J K : Disorder n) :
    ∑ x, replicaMarginal β S J x*hamiltonian K x =
      (∑ s ∈ S, replicaRow β S J s*replicaEnergy K s)/(d:ℝ) := by
  have H (s : ReplicaConfig n d) :
      (∑ x : Config n, ∑ a : Fin d, (if s a = x then replicaRow β S J s/(d:ℝ) else 0)*
        hamiltonian K x) = replicaRow β S J s*replicaEnergy K s/(d:ℝ) := by
    rw [Finset.sum_comm]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    unfold replicaEnergy
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold replicaMarginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [H]
  rw [Finset.sum_div]

theorem continuous_replicaEnergy {n d : ℕ} (s : ReplicaConfig n d) :
    Continuous (fun J : Disorder n => replicaEnergy J s) :=
  continuous_finsetSum _ (fun a _ => continuous_hamiltonian (s a))

theorem continuous_restrictedPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Continuous (restrictedPartition β S) :=
  continuous_finsetSum _ (fun s _ => (Real.continuous_exp.comp ((continuous_replicaEnergy s).const_mul β)))

theorem continuous_restrictedLogPartition {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) : Continuous (restrictedLogPartition β S) :=
  (continuous_restrictedPartition β S).log (fun J => (restrictedPartition_pos β hS J).ne')

theorem continuous_replicaRow {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (s : ReplicaConfig n d) : Continuous (fun J => replicaRow β S J s) :=
  (Real.continuous_exp.comp ((continuous_replicaEnergy s).const_mul β)).div (continuous_restrictedPartition β S)
    (fun J => (restrictedPartition_pos β hS J).ne')

theorem continuous_replicaMarginal {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (x : Config n) : Continuous (fun J => replicaMarginal β S J x) := by
  apply continuous_finsetSum
  intro s _
  apply continuous_finsetSum
  intro a _
  by_cases h : s a = x
  · simp only [ite_eq_left h]
    exact (continuous_replicaRow β hS s).div_const _
  · simp only [ite_eq_right h]
    exact continuous_const

theorem restrictedLogPartition_hasDerivAt {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : ℝ → Disorder n) (K : Disorder n) (t : ℝ)
    (hJ : ∀ x, HasDerivAt (fun u => hamiltonian (J u) x) (hamiltonian K x) t) :
    HasDerivAt (fun u => restrictedLogPartition β S (J u))
      (β*∑ s ∈ S, replicaRow β S (J t) s*replicaEnergy K s) t := by
  have he (s : ReplicaConfig n d) :
      HasDerivAt (fun u => replicaEnergy (J u) s) (replicaEnergy K s) t :=
    HasDerivAt.fun_sum (fun a _ => hJ (s a))
  have hp : HasDerivAt (fun u => restrictedPartition β S (J u))
      (∑ s ∈ S, Real.exp (β*replicaEnergy (J t) s)*(β*replicaEnergy K s)) t :=
    HasDerivAt.fun_sum (fun s _ => ((he s).const_mul β).exp)
  have hl := hp.log (restrictedPartition_pos β hS (J t)).ne'
  apply hl.congr_deriv
  simp only [replicaRow,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

@[instance_reducible] def restrictedModel {n d : ℕ} (hd : 0 < d) (S : Finset (ReplicaConfig n d))
    (hS : S.Nonempty) : SmoothFamily.Model n where
  logPartition γ := restrictedLogPartition (γ/(d:ℝ)) S
  gibbs γ := replicaMarginal (γ/(d:ℝ)) S
  gibbs_nonneg γ := replicaMarginal_nonneg _ hS
  gibbs_sum γ := replicaMarginal_sum hd _ hS
  continuous_gibbs γ := continuous_replicaMarginal _ hS
  continuous_logPartition γ := continuous_restrictedLogPartition _ hS
  hasDerivAt γ J K t hJ := by
    have H := restrictedLogPartition_hasDerivAt (γ/(d:ℝ)) hS J K t hJ
    apply H.congr_deriv
    rw [replicaMarginal_energy]
    ring

end SK.Analytic

end
end

end

end OAI
