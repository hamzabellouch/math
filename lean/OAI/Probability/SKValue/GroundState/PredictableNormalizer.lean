import Mathlib
import OAI.Probability.SKValue.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

lemma independent_of_coordinate_not_in {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) {j : ι} (hj : j ∉ S) {F : (ι → ℝ) → β}
    (hF : Measurable F)
    (hdep : ∀ x y, (∀ i ∈ S, x i=y i) → F x=F y) :
    IndepFun F (fun x ↦ x j) (Measure.pi μ) := by
  let fill : (S → ℝ) → ι → ℝ := fun x i ↦ if hi : i ∈ S then x ⟨i,hi⟩ else 0
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [fill, dite_eq_left hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simp only [fill, dite_eq_right hi]
      exact measurable_const
  have hid : ∀ x : ι → ℝ, F (fill (fun i : S ↦ x i)) = F x := by
    intro x
    apply hdep
    intro i hi
    simp [fill,hi]
  have hST : Disjoint S {j} := by simpa using hj
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi μ) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have H := (hind.indepFun_finset S {j} hST (fun i ↦ measurable_pi_apply i)).comp
    (hF.comp hfill) (measurable_pi_apply (⟨j,by simp⟩ : ({j} : Finset ι)))
  simpa only [Function.comp_def, hid] using H

lemma measurable_coordinate (N j : ℕ) : Measurable (coordinate N j) :=
  measurable_pi_apply _

lemma coordinate_eq_apply {N j : ℕ} (hj : j < N+1) (z : Fin (N+1) → ℝ) :
    coordinate N j z = z ⟨j,hj⟩ := by
  simp [coordinate, Nat.mod_eq_of_lt hj]

lemma euler_depends_on_past (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z z' : Fin (N+1) → ℝ)
    (h : ∀ i < j, coordinate N i z=coordinate N i z') :
    euler T N γ u z j=euler T N γ u z' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi ↦ h i (by omega))
    simp only [euler, hp,h j (by omega)]

lemma measurable_euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hU : ∀ k < N, Measurable (u (meshTime T N k))) :
    ∀ j ≤ N, Measurable (fun z ↦ euler T N γ u z j) := by
  intro j hj
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hjN : j < N := by omega
    have hy := ih (by omega)
    have hz := measurable_coordinate N j
    have hu := (hU j hjN).comp hy
    simp only [euler]
    fun_prop

lemma euler_coefficient_independent {T : ℝ} {N j : ℕ} {γ : ℝ → ℝ}
    {u a : ℝ → ℝ → ℝ} (hj : j < N+1)
    (hU : ∀ k < N, Measurable (u (meshTime T N k)))
    (hA : Measurable (a (meshTime T N j))) :
    IndepFun (fun z ↦ a (meshTime T N j) (euler T N γ u z j))
      (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  let S : Finset (Fin (N+1)) := Finset.univ.filter (fun i ↦ (i : ℕ)<j)
  have hjS : (⟨j,hj⟩ : Fin (N+1)) ∉ S := by simp [S]
  have hF : Measurable (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) :=
    hA.comp (measurable_euler T N γ u hU j (by omega))
  have h := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    S hjS hF
    (fun z z' heq ↦ by
      apply congrArg (a (meshTime T N j))
      apply euler_depends_on_past T N γ u j z z'
      intro i hi
      have hiN : i < N+1 := hi.trans hj
      rw [coordinate_eq_apply hiN,coordinate_eq_apply hiN]
      apply heq
      simp [S,hi])
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

noncomputable def predictableNormalizer (H : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  (Real.sqrt (∫ ω, (H ω)^2 ∂μ))⁻¹

noncomputable def normalizedIncrement (H Z : Ω → ℝ) (μ : Measure Ω) : Ω → ℝ :=
  fun ω ↦ predictableNormalizer H μ * H ω * Z ω

lemma predictableNormalizer_pos {H : Ω → ℝ}
    (hHpos : 0 < ∫ ω, (H ω)^2 ∂μ) :
    0 < predictableNormalizer H μ := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr hHpos)

lemma normalizedIncrement_mean {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    ∫ ω, normalizedIncrement H Z μ ω ∂μ = 0 := by
  simp only [normalizedIncrement, mul_assoc]
  rw [integral_const_mul]
  have hi := hind.integral_mul_eq_mul_integral hH hZ.aemeasurable.aestronglyMeasurable
  change (∫ ω, H ω * Z ω ∂μ) = _ at hi
  rw [hi, gaussian_mean hZ, mul_zero, mul_zero]

lemma normalizedIncrement_second_moment {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) (hHpos : 0 < ∫ ω, (H ω)^2 ∂μ) :
    ∫ ω, (normalizedIncrement H Z μ ω)^2 ∂μ = 1 := by
  have hind2 : IndepFun (fun ω ↦ (H ω)^2) (fun ω ↦ (Z ω)^2) μ :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind2.integral_mul_eq_mul_integral
    (hH.fun_pow 2)
    (hZ.aemeasurable.aestronglyMeasurable.fun_pow 2)
  change (∫ ω, (H ω)^2 * (Z ω)^2 ∂μ) =
    (∫ ω, (H ω)^2 ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hi
  simp only [normalizedIncrement, mul_pow, mul_assoc]
  rw [integral_const_mul, hi, gaussian_second_moment hZ, mul_one]
  simp only [predictableNormalizer, inv_pow, Real.sq_sqrt (le_of_lt hHpos)]
  exact inv_mul_cancel₀ (ne_of_gt hHpos)

lemma normalizedIncrement_memLp_two {H Z : Ω → ℝ}
    (hH : MemLp H 2 μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    MemLp (normalizedIncrement H Z μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((hH.aestronglyMeasurable.const_mul _).mul hZ.aemeasurable.aestronglyMeasurable)).2
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
     hH.integrable_sq (gaussian_memLp hZ 2 (by norm_num)).integrable_sq
  have hj := hi.const_mul (predictableNormalizer H μ ^ 2)
  simpa only [normalizedIncrement, Pi.mul_apply, mul_pow, mul_assoc, Function.comp_def, id_eq] using hj

lemma normalizedIncrement_gaussian_coefficient {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    ∫ ω, normalizedIncrement H Z μ ω * Z ω ∂μ =
      predictableNormalizer H μ * ∫ ω, H ω ∂μ := by
  have hind2 : IndepFun H (fun ω ↦ (Z ω)^2) μ :=
    hind.comp measurable_id (measurable_id.pow_const 2)
  have hi := hind2.integral_mul_eq_mul_integral hH
    (hZ.aemeasurable.aestronglyMeasurable.fun_pow 2)
  change (∫ ω, H ω * (Z ω)^2 ∂μ) =
    (∫ ω, H ω ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hi
  simp only [normalizedIncrement, mul_assoc, ← pow_two]
  rw [integral_const_mul, hi, gaussian_second_moment hZ, mul_one]

lemma predictable_product_mean_zero {H K Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hK : AEStronglyMeasurable K μ)
    (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun (fun ω ↦ H ω * K ω) Z μ) :
    ∫ ω, K ω * normalizedIncrement H Z μ ω ∂μ = 0 := by
  have hi := hind.integral_mul_eq_mul_integral (hH.mul hK)
    hZ.aemeasurable.aestronglyMeasurable
  change (∫ ω, (H ω * K ω) * Z ω ∂μ) = _ at hi
  calc
    _ = predictableNormalizer H μ * ∫ ω, (H ω * K ω) * Z ω ∂μ := by
      rw [← integral_const_mul]
      congr 1
      ext ω
      simp only [normalizedIncrement]
      ring
    _ = 0 := by rw [hi, gaussian_mean hZ, mul_zero, mul_zero]

lemma coordinate_hasLaw (N j : ℕ) :
    HasLaw (coordinate N j) (gaussianReal 0 1) (gaussianProduct (Fin (N+1))) :=
  (measurePreserving_eval (fun _ : Fin (N+1) ↦ standardGaussian)
    ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).hasLaw

def DependsBefore {N : ℕ} {β : Type*} (j : ℕ) (F : (Fin (N+1) → ℝ) → β) : Prop :=
  ∀ z z', (∀ i : Fin (N+1), (i : ℕ)<j → z i=z' i) → F z=F z'

lemma DependsBefore.independent {N j : ℕ} {β : Type*} [MeasurableSpace β] (hj : j<N+1)
    {F : (Fin (N+1) → ℝ) → β} (hF : DependsBefore j F) (hm : Measurable F) :
    IndepFun F (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  have H := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    (Finset.univ.filter (fun i : Fin (N+1) ↦ (i : ℕ)<j))
    (j := ⟨j,hj⟩) (by simp) hm (fun z z' heq ↦ hF z z' (by simpa using heq))
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact H

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

lemma DependsBefore.prodMk {N j : ℕ} {β β' : Type*}
    {F : (Fin (N+1) → ℝ) → β} {G : (Fin (N+1) → ℝ) → β'}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ (F z,G z)) := by
  intro z z' h
  exact Prod.ext (hF z z' h) (hG z z' h)

lemma DependsBefore.mul {N j : ℕ} {F G : (Fin (N+1) → ℝ) → ℝ}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ F z * G z) := by
  intro z z' h
  dsimp only
  rw [hF z z' h, hG z z' h]

lemma eulerCoefficient_dependsBefore (T : ℝ) {N j : ℕ} (hj : j≤N)
    (γ : ℝ → ℝ) (u a : ℝ → ℝ → ℝ) :
    DependsBefore j (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) := by
  intro z z' h
  apply congrArg (a (meshTime T N j))
  apply euler_depends_on_past
  intro i hi
  have hiN : i<N+1 := by omega
  rw [coordinate_eq_apply hiN, coordinate_eq_apply hiN]
  exact h ⟨i,hiN⟩ hi

lemma normalizedIncrement_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hH : DependsBefore j H) :
    DependsBefore (j+1) (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) := by
  intro z z' h
  have heq := hH.mono (Nat.le_succ j) z z' h
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  simp only [normalizedIncrement,heq,hz]

lemma measurable_normalizedIncrement {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hH : Measurable H) :
    Measurable (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) :=
  (hH.const_mul _).mul (measurable_coordinate N j)

lemma normalizedIncrements_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ} (hHm : Measurable H) (hKm : Measurable K)
    (hH : DependsBefore i H) (hK : DependsBefore j K) :
    ∫ z, normalizedIncrement H (coordinate N i) (gaussianProduct (Fin (N+1))) z *
      normalizedIncrement K (coordinate N j) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1)) = 0 := by
  have hi : i<N+1 := hij.trans hj
  have hprev := (normalizedIncrement_dependsBefore hi hH).mono (by omega : i+1≤j)
  exact predictable_product_mean_zero hKm.aestronglyMeasurable
    (measurable_normalizedIncrement hHm).aestronglyMeasurable (coordinate_hasLaw N j)
    ((hK.mul hprev).independent hj
      (hKm.mul (measurable_normalizedIncrement hHm)))

lemma euler_normalized_increment_properties {T : ℝ} {N j : ℕ} {γ : ℝ → ℝ}
    {u a : ℝ → ℝ → ℝ} (hj : j<N+1)
    (hU : ∀ k<N, Measurable (u (meshTime T N k)))
    (hA : Measurable (a (meshTime T N j)))
    (hpos : 0 < ∫ z, (a (meshTime T N j) (euler T N γ u z j))^2
      ∂gaussianProduct (Fin (N+1))) :
    let H := fun z ↦ a (meshTime T N j) (euler T N γ u z j)
    let μ := gaussianProduct (Fin (N+1))
    0 < predictableNormalizer H μ ∧
    (∫ z, normalizedIncrement H (coordinate N j) μ z ∂μ)=0 ∧
    (∫ z, (normalizedIncrement H (coordinate N j) μ z)^2 ∂μ)=1 := by
  dsimp only
  have hm := hA.comp (measurable_euler T N γ u hU j (by omega))
  have hind := euler_coefficient_independent (γ := γ) hj hU hA
  exact ⟨predictableNormalizer_pos hpos,
    normalizedIncrement_mean hm.aestronglyMeasurable (coordinate_hasLaw N j) hind,
    normalizedIncrement_second_moment hm.aestronglyMeasurable (coordinate_hasLaw N j) hind hpos⟩

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
