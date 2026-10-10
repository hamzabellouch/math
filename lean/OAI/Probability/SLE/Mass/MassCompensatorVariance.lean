import OAI.Probability.SLE.Mass.MassCompensatorMesh
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.CondVar

namespace OAI

/-! Orthogonality and variance bounds for the discrete potential
compensator used in the prescribed moment coefficients. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

section Centered
variable (m : MeasurableSpace Ω) (hm : m ≤ mΩ)

include hm in
lemma centered_mass_increment_condExp (X : Ω → ℝ) (hX : MemLp X 2 P) :
    P[X-P[X|m]|m] =ᵐ[P] 0 := by
  have hi := hX.integrable one_le_two
  have h := condExp_sub hi (integrable_condExp (μ := P) (m := m) (f := X)) m
  rw [condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp] at h
  simpa only [sub_self] using h

include hm in
lemma integral_mul_centered_mass_increment
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hYm : StronglyMeasurable[m] Y) :
    (∫ ω, Y ω*(X ω-P[X|m] ω) ∂P)=0 := by
  have hZ : MemLp (X-P[X|m]) 2 P := hX.sub (hX.condExp one_le_two)
  have hprod : Integrable (Y*(X-P[X|m])) P := memLp_one_iff_integrable.mp (hY.mul hZ)
  have he := condExp_mul_of_stronglyMeasurable_left hYm hprod (hZ.integrable one_le_two)
  have hz := centered_mass_increment_condExp (mΩ := mΩ) P m hm X hX
  have he0 : P[Y*(X-P[X|m])|m] =ᵐ[P] 0 := by
    filter_upwards [he,hz] with ω hp hz
    simp only [Pi.mul_apply,Pi.zero_apply,hz,mul_zero] at hp ⊢
    exact hp
  calc
    _ = ∫ ω, P[Y*(X-P[X|m])|m] ω ∂P := (integral_condExp hm).symm
    _ = 0 := by simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae he0

include hm in
lemma centered_mass_increment_variance_le (X : Ω → ℝ) (hX : MemLp X 2 P) :
    (∫ ω, (X ω-P[X|m] ω)^2 ∂P) ≤ ∫ ω, X ω^2 ∂P := by
  have hZ : Integrable (fun ω => (X ω-P[X|m] ω)^2) P :=
    (hX.sub (hX.condExp one_le_two)).integrable_sq
  have he := setIntegral_condVar (hm := hm) hZ (MeasurableSet.univ : MeasurableSet[m] univ)
  simp only [Measure.restrict_univ] at he
  rw [← he]
  calc
    _ ≤ ∫ ω, P[X^2|m] ω ∂P :=
      integral_mono_ae integrable_condVar integrable_condExp (condVar_ae_le_condExp_sq hm hX)
    _ = _ := integral_condExp hm

end Centered

lemma martingale_square_submartingale
    {ι : Type*} [Preorder ι] (ℱ : Filtration ι mΩ)
    (M : ι → Ω → ℝ) (hM : Martingale M ℱ P) (h2 : ∀ i, MemLp (M i) 2 P) :
    Submartingale (fun i ω => M i ω^2) ℱ P := by
  refine ⟨fun i => (hM.stronglyMeasurable i).pow 2,?_,fun i => (h2 i).integrable_sq⟩
  intro i j hij
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le i) (h2 j)
  have hn : 0 ≤ᵐ[P] condVar (ℱ i) (M j) P :=
    condExp_nonneg (ae_of_all _ (fun ω => sq_nonneg (M j ω-P[M j|ℱ i] ω)))
  filter_upwards [hv,hn,hM.condExp_ae_eq hij] with ω hv hn he
  simp only [Pi.sub_apply,Pi.pow_apply] at hv
  rw [he] at hv
  change 0 ≤ condVar (ℱ i) (M j) P ω at hn
  change condVar (ℱ i) (M j) P ω = P[fun ω => M j ω^2|ℱ i] ω - M i ω^2 at hv
  linarith

lemma martingale_square_maximal_ineq
    (ℱ : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ)
    (hM : Martingale M ℱ P) (h2 : ∀ i, MemLp (M i) 2 P)
    (ε : ℝ≥0) (N : ℕ) :
    (ε:ℝ≥0∞) * P {ω | (ε:ℝ) ≤ (Finset.range (N+1)).sup'
      Finset.nonempty_range_add_one (fun j => M j ω^2)} ≤
      ENNReal.ofReal (∫ ω, M N ω^2 ∂P) := by
  have hsub := martingale_square_submartingale P ℱ M hM h2
  have h := maximal_ineq hsub (fun i ω => sq_nonneg (M i ω)) (ε := ε) N
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  exact setIntegral_le_integral (h2 N).integrable_sq (ae_of_all _ (fun ω => sq_nonneg (M N ω)))

noncomputable def centeredMassPartialSum (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, (D i ω - condExp (ℱ i) P (D i) ω)

omit [IsProbabilityMeasure P] in
lemma centeredMassPartialSum_memLp (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P) (n : ℕ) :
    MemLp (centeredMassPartialSum P ℱ D n) 2 P :=
  memLp_finsetSum _ (fun i _ => (hD i).sub ((hD i).condExp one_le_two))

omit [IsProbabilityMeasure P] in
lemma centeredMassPartialSum_stronglyMeasurable
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (centeredMassPartialSum P ℱ D n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hle : i+1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  exact ((hD i).mono (ℱ.mono hle)).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_of_lt (Finset.mem_range.mp hi))))

lemma centeredMassPartialSum_variance
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (hDm : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i)) (n : ℕ) :
    (∫ ω, centeredMassPartialSum P ℱ D n ω^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (D i ω-P[D i|ℱ i] ω)^2 ∂P := by
  induction n with
  | zero => simp [centeredMassPartialSum]
  | succ n ih =>
    have hS := centeredMassPartialSum_memLp P ℱ D hD n
    have hX : MemLp (D n-P[D n|ℱ n]) 2 P := (hD n).sub ((hD n).condExp one_le_two)
    have hSX : Integrable (fun ω => centeredMassPartialSum P ℱ D n ω*
        (D n ω-P[D n|ℱ n] ω)) P := memLp_one_iff_integrable.mp (hS.mul hX)
    have hcross := integral_mul_centered_mass_increment P (ℱ n) (ℱ.le n)
      (D n) (centeredMassPartialSum P ℱ D n) (hD n) hS
      (centeredMassPartialSum_stronglyMeasurable P ℱ D hDm n)
    have he : (fun ω => centeredMassPartialSum P ℱ D (n+1) ω^2) =
        (fun ω => centeredMassPartialSum P ℱ D n ω^2+
          2*(centeredMassPartialSum P ℱ D n ω*(D n ω-P[D n|ℱ n] ω))+
          (D n ω-P[D n|ℱ n] ω)^2) := by
      funext ω
      simp only [centeredMassPartialSum,Finset.sum_range_succ]
      ring
    have hi₁ := integral_add (hS.integrable_sq.add (hSX.const_mul 2)) hX.integrable_sq
    have hi₂ := integral_add hS.integrable_sq (hSX.const_mul 2)
    simp only [Pi.add_apply,Pi.sub_apply] at hi₁ hi₂
    rw [he,hi₁,hi₂,integral_const_mul,hcross,mul_zero,add_zero,ih,Finset.sum_range_succ]

lemma centeredMassPartialSum_variance_le
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (hDm : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i)) (n : ℕ) :
    (∫ ω, centeredMassPartialSum P ℱ D n ω^2 ∂P) ≤
      ∫ ω, ∑ i ∈ Finset.range n, D i ω^2 ∂P := by
  rw [centeredMassPartialSum_variance P ℱ D hD hDm n,
    integral_finsetSum _ (fun i _ => (hD i).integrable_sq)]
  exact Finset.sum_le_sum (fun i _ => centered_mass_increment_variance_le P (ℱ i) (ℱ.le i) (D i) (hD i))

lemma centeredMassPartialSum_martingale
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (hDm : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i)) :
    Martingale (centeredMassPartialSum P ℱ D) ℱ P := by
  let A : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, D i ω
  have hAm : StronglyAdapted ℱ A := by
    intro n
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (hDm i).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  have hAI (n : ℕ) : Integrable (A n) P :=
    (memLp_finsetSum _ (fun i _ => hD i)).integrable one_le_two
  have hd (i : ℕ) : A (i+1)-A i=D i := by
    funext ω
    simp only [A,Finset.sum_range_succ,Pi.sub_apply,add_sub_cancel_left]
  have he : martingalePart A ℱ P = centeredMassPartialSum P ℱ D := by
    rw [martingalePart_eq_sum]
    funext n ω
    simp only [Pi.add_apply,Finset.sum_apply,Pi.sub_apply]
    change A 0 ω+(∑ i ∈ Finset.range n,
      ((A (i+1)-A i) ω-condExp (ℱ i) P (A (i+1)-A i) ω)) = _
    simp only [hd]
    simp only [A,Finset.range_zero,Finset.sum_empty,zero_add,centeredMassPartialSum]
  simpa only [he] using martingale_martingalePart hAm hAI

/-- A maximal estimate valid at every selected grid index, without
requiring that the selected index itself be a stopping time. -/
theorem centeredMassPartialSum_maximal_error
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (hDm : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i)) (ε : ℝ≥0) (N : ℕ) :
    (ε:ℝ≥0∞)*P {ω | (ε:ℝ) ≤ (Finset.range (N+1)).sup'
      Finset.nonempty_range_add_one (fun j => centeredMassPartialSum P ℱ D j ω^2)} ≤
        ENNReal.ofReal (∫ ω, ∑ i ∈ Finset.range N, D i ω^2 ∂P) := by
  exact (martingale_square_maximal_ineq P ℱ (centeredMassPartialSum P ℱ D)
    (centeredMassPartialSum_martingale P ℱ D hD hDm)
    (centeredMassPartialSum_memLp P ℱ D hD) ε N).trans
      (ENNReal.ofReal_le_ofReal (centeredMassPartialSum_variance_le P ℱ D hD hDm N))

end SLEExactGauge

end

end OAI
