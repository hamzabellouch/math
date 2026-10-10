import OAI.InformationTheory.PhotonNumber.Minimum

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric
open EntropyPhotonNumber
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem column_metric_bound (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ∧
    (∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ ‖Z‖^2 := by
  have hn (j : J) : ‖Z (b j)‖^2 ≤ ‖Z‖^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) 
    simpa only [b.orthonormal.norm_eq_one, mul_one] using Z.le_opNorm (b j)
  have hsum : Summable (fun j => p j*‖Z (b j)‖^2) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hp j).le (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hn j) (hp j).le) (hs.summable.mul_right (‖Z‖^2))
  have he (j : J) : HasSum (fun i => p j*‖inner ℂ (b i) (Z (b j))‖^2)
      (p j*‖Z (b j)‖^2) := (QuantumTrace.basis_hasSum_norm_sq b (Z (b j))).mul_left (p j)
  have hadd : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2) := by
    apply (summable_prod_of_nonneg (fun a => mul_nonneg (hp a.1).le (sq_nonneg _))).mpr
    exact ⟨fun j => (he j).summable, by simpa only [(he _).tsum_eq] using hsum⟩
  refine ⟨hadd.prod_symm, ?_⟩
  calc
    (∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) =
        ∑' a : J × J, p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2 :=
      by simpa only [Equiv.prodComm_apply, Prod.swap] using
        (Equiv.prodComm J J).tsum_eq (fun a : J × J => p a.1*‖inner ℂ (b a.2) (Z (b a.1))‖^2)
    _ = ∑' j, p j*‖Z (b j)‖^2 := by rw [hadd.tsum_prod]; simp only [(he _).tsum_eq]
    _ ≤ ∑' j, p j*‖Z‖^2 := hsum.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left (hn j) (hp j).le) (hs.summable.mul_right _)
    _ = ‖Z‖^2 := by rw [tsum_mul_right, hs.tsum_eq, one_mul]

theorem bounded_matrix_bound (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) (t : ℝ) (ht : 0<t) (Z : E →L[ℂ] E) :
    (∑' a : J × J, metricCoefficient t (p a.1) (p a.2)*
      ‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ (h t/2*(2*t+1))*‖Z‖^2 := by
  have hc := column_metric_bound b p hp hs Z
  have hca := column_metric_bound b p hp hs Z.adjoint
  have hr : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ∧
      (∑' a : J × J, p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) ≤ ‖Z‖^2 := by
    constructor
    · simpa only [Prod.swap, ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
        using hca.1.prod_symm
    · have he := (Equiv.prodComm J J).tsum_eq
        (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z.adjoint (b a.2))‖^2)
      have hb := hca.2
      rw [← he] at hb
      simpa only [Equiv.prodComm_apply, Prod.swap, ContinuousLinearMap.adjoint_inner_right,
        norm_inner_symm, LinearIsometryEquiv.norm_map] using hb
  have hh := bounded_matrix_summable b p hp hs.summable t ht Z
  have hb := (((hr.1.mul_left t).add (hc.1.mul_left (t+1))).mul_left (h t/2))
  calc
    _ ≤ ∑' a : J × J, h t/2*(t*(p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2)+
        (t+1)*(p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2)) := by
      apply hh.tsum_le_tsum _ hb
      intro a
      have ha := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
        (mul_pos (by positivity : 0<t+1) (hp a.2))
      have hm : metricCoefficient t (p a.1) (p a.2) =
          h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
        rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
      rw [hm]
      have he := mul_le_mul_of_nonneg_left ha (h_pos ht).le
      nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg ‖inner ℂ (b a.1) (Z (b a.2))‖)]
    _ = h t/2*(t*(∑' a : J × J, p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2)+
        (t+1)*(∑' a : J × J, p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2)) := by
      rw [tsum_mul_left, (hr.1.mul_left t).tsum_add (hc.1.mul_left (t+1)),
        tsum_mul_left, tsum_mul_left]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hr.2 ht.le
      have h₂ := mul_le_mul_of_nonneg_left hc.2 (by linarith : 0≤t+1)
      have hc0 : 0 ≤ h t/2 := div_nonneg (h_pos ht).le (by norm_num)
      have h₃ := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hc0
      nlinarith
end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem full_defect_on_observable (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n)
    (Z : Fock n →L[ℂ] Fock n) :
    defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
      (G.centeredMatrix_defect_summable hk t j) (G.observableVector t ht Z)=
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z := by
  exact (defectVector_pairing t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable hk t j)
    (fun a => inner ℂ (G.basis a.1) (Z (G.basis a.2)))
    (bounded_matrix_summable G.basis G.probability G.probability_pos
      G.probability_sum.summable t ht Z)).unique
    (weakDefect_spectral G.basis G.probability G.probability_pos G.spectralColumns
      G.spectralColumns_summable G.spectralColumns_inverse t j (G.annihilationMean j) Z)

theorem observableVector_bound (t : ℝ) (ht : 0<t) (Z : Fock n →L[ℂ] Fock n) :
    ‖G.observableVector t ht Z‖^2 ≤ (h t/2*(2*t+1))*‖Z‖^2 := by
  rw [observableVector, matrixVector, weightedVector_norm_sq]
  exact bounded_matrix_bound G.basis G.probability G.probability_pos G.probability_sum t ht Z

theorem weakDefect_bound (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n)
    (Z : Fock n →L[ℂ] Fock n) :
    ‖weakDefect t G.spectralColumns j (G.annihilationMean j) Z‖^2 ≤
      ‖G.defect hk t ht j‖^2*((h t/2*(2*t+1))*‖Z‖^2) := by
  let F := defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
      (G.centeredMatrix_defect_summable hk t j)
  have hn : ‖F‖=‖G.defect hk t ht j‖ := by
    symm
    exact defectFunctional_restrict_norm t ht G.probability G.probability_pos
      (G.centeredMatrix j) _ _
      (defectVector_mem_centeredSpace t ht G.probability G.probability_pos
        G.probability_sum.summable (G.centeredMatrix j) _ (G.centeredMatrix_mean_zero j))
  rw [← G.full_defect_on_observable hk t ht j Z]
  calc
    _ ≤ (‖F‖*‖G.observableVector t ht Z‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (F.le_opNorm _) 2
    _ = ‖G.defect hk t ht j‖^2*‖G.observableVector t ht Z‖^2 := by rw [mul_pow, hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left (G.observableVector_bound t ht Z) (sq_nonneg _)
end EntropyPhotonNumber.GibbsData

namespace ThermalRecurrence

section
variable {J : Type*} [Fintype J] [DecidableEq J]

def lower (p : J → ℕ) (j : J) : J → ℕ := Function.update p j (p j-1)

omit [Fintype J] in
@[simp] theorem lower_same (p : J → ℕ) (j : J) : lower p j j = p j-1 := by simp [lower]

theorem lower_sum {p : J → ℕ} {j : J} (hp : 0 < p j) :
    (∑ k, lower p j k) + 1 = ∑ k, p k := by
  rw [show (∑ k, lower p j k) = (p j-1) + ∑ k ∈ Finset.univ.erase j, p k by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [lower_same]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  omega

def Balance (r : ℝ) (M : (J → ℕ) → (J → ℕ) → ℂ) : Prop :=
  ∀ j p b, 0 < p j →
    ((r+1)*Real.sqrt (p j : ℝ)) • M p b =
      (r*Real.sqrt (b j : ℝ)) • M (lower p j) (lower b j)

omit [Fintype J] in

theorem entry_zero_of_lt {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    (j : J) {p b : J → ℕ} (hp : b j < p j) : M p b = 0 := by
  have hall (m : ℕ) : ∀ (p b : J → ℕ), b j = m → b j < p j → M p b = 0 := by
    induction m with
    | zero =>
      intro p b hb hpb
      have hpj : 0 < (p j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hz := hM j p b (by omega)
      have hne : (r+1)*Real.sqrt (p j : ℝ) ≠ 0 := by positivity
      simp only [hb, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_smul] at hz
      exact (smul_eq_zero.mp hz).resolve_left hne
    | succ m ih =>
      intro p b hb hpb
      have hprev := ih (lower p j) (lower b j) (by simp [hb]) (by simp; omega)
      have hpj : 0 < (p j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hz := hM j p b (by omega)
      rw [hprev, smul_zero] at hz
      exact (smul_eq_zero.mp hz).resolve_left (by positivity)
  exact hall (b j) p b rfl hp

omit [Fintype J] in

theorem off_diagonal_zero {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    (hstar : ∀ p b, M b p = conj (M p b)) {p b : J → ℕ} (hne : p ≠ b) : M p b = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  rcases lt_or_gt_of_ne hj with h | h
  · have hb := entry_zero_of_lt hr hM j h
    rw [hstar] at hb
    simpa using congrArg conj hb
  · exact entry_zero_of_lt hr hM j h

omit [Fintype J] in

theorem diagonal_step {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M)
    {p : J → ℕ} {j : J} (hp : 0 < p j) :
    M p p = (r/(r+1)) • M (lower p j) (lower p j) := by
  have hh := hM j p p hp
  have ha : (r+1)*Real.sqrt (p j:ℝ) ≠ 0 := by positivity
  have he : ((r+1)*Real.sqrt (p j:ℝ)) •
      ((r/(r+1)) • M (lower p j) (lower p j)) =
        (r*Real.sqrt (p j:ℝ)) • M (lower p j) (lower p j) := by
    rw [smul_smul]
    congr 1
    field_simp
  apply (smul_right_injective _ ha)
  exact hh.trans he.symm

theorem diagonal_formula {r : ℝ} (hr : 0 < r)
    {M : (J → ℕ) → (J → ℕ) → ℂ} (hM : Balance r M) (p : J → ℕ) :
    M p p = (r/(r+1))^(∑ j, p j) • M 0 0 := by
  have hall (m : ℕ) : ∀ p : J → ℕ, (∑ j, p j) = m →
      M p p = (r/(r+1))^m • M 0 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hp
      by_cases hzero : p = 0
      · subst p
        simp at hp
        subst m
        simp
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp hzero
        change p j ≠ 0 at hj
        have hj0 : 0 < p j := Nat.pos_of_ne_zero hj
        have hsum := lower_sum hj0
        rw [hp] at hsum
        rw [diagonal_step hr hM hj0, ih (∑ k, lower p j k) (by omega) (lower p j) rfl,
          smul_smul, ← pow_succ']
        rw [hsum]
  exact hall _ p rfl

end

theorem thermalWeight_eq (n : ℕ) (r : ℝ) (p : Fin n → ℕ) :
    QuantumTrace.thermalWeight n r p = (r+1)⁻¹^n * (r/(r+1))^(∑ j, p j) := by
  simp [QuantumTrace.thermalWeight, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem unique_thermal_matrix (n : ℕ) {r : ℝ} (hr : 0 < r)
    {M : (Fin n → ℕ) → (Fin n → ℕ) → ℂ} (hM : Balance r M)
    (hstar : ∀ p b, M b p = conj (M p b))
    (htrace : HasSum (fun p => (M p p).re) 1) (p b : Fin n → ℕ) :
    M p b = if p = b then (QuantumTrace.thermalWeight n r p : ℂ) else 0 := by
  let c : ℂ := (r+1)^n • M 0 0
  have hr1 : r+1 ≠ 0 := by positivity
  have hc0 : c.im = 0 := by
    have he := congrArg Complex.im (hstar 0 0)
    dsimp [c]
    simp only [Complex.conj_im] at he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    have hz : (M 0 0).im = 0 := by linarith
    rw [hz, mul_zero]
  have hf (a : Fin n → ℕ) : M a a = QuantumTrace.thermalWeight n r a • c := by
    have hw : QuantumTrace.thermalWeight n r a * (r+1)^n =
        (r/(r+1))^(∑ j, a j) := by
      rw [thermalWeight_eq n r a, inv_pow]
      field_simp
    calc
      M a a = (r/(r+1))^(∑ j, a j) • M 0 0 := diagonal_formula hr hM a
      _ = (QuantumTrace.thermalWeight n r a * (r+1)^n) • M 0 0 := by rw [hw]
      _ = QuantumTrace.thermalWeight n r a • c := (smul_smul _ _ _).symm
  have hs := ((QuantumTrace.hasSum_thermalWeight n hr).mul_right c.re)
  have hc1 : c.re = 1 := by
    have hefun : (fun a : Fin n → ℕ => (M a a).re) =
        (fun a => QuantumTrace.thermalWeight n r a * c.re) := by
      funext a
      rw [hf]
      simp
    rw [hefun] at htrace
    simpa only [one_mul] using hs.unique htrace
  have hc : c = 1 := Complex.ext hc1 hc0
  by_cases he : p = b
  · subst b
    rw [ite_eq_left rfl, hf, hc]
    simp
  · rw [ite_eq_right he]
    exact off_diagonal_zero hr hM hstar he

end ThermalRecurrence

namespace EntropyPhotonNumber
open Filter Topology Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ}

theorem entry_tendsto {ρ : ℕ → State n} {σ : State n}
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op)) (a b : NumberIndex n) :
    Tendsto (fun m => entry (ρ m).op a b) atTop (𝓝 (entry σ.op a b)) :=
  tendsto_const_nhds.inner
    (((ContinuousLinearMap.apply ℂ (Fock n) (numberKet b)).continuous.tendsto _).comp he)

theorem state_entry_star (ρ : State n) (a b : NumberIndex n) :
    entry ρ.op b a=conj (entry ρ.op a b) := by
  change inner ℂ (numberKet b) (ρ.op (numberKet a))= _
  calc
    _ = inner ℂ (ρ.op (numberKet b)) (numberKet a) :=
      (ρ.positive.isSymmetric (numberKet b) (numberKet a)).symm
    _ = _ := (inner_conj_symm _ _).symm

theorem weakDefect_tendsto {ρ : ℕ → State n} {k : ℕ → ℝ}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t) (j : Fin n)
    (hq : Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0))
    (Z : Fock n →L[ℂ] Fock n) :
    Tendsto (fun m => weakDefect t (G m).spectralColumns j ((G m).annihilationMean j) Z)
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => ‖weakDefect t (G m).spectralColumns j
      ((G m).annihilationMean j) Z‖^2) atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => sq_nonneg _)
      (fun m => (G m).weakDefect_bound (hk m) t ht j Z)
      (by simpa only [zero_pow (by decide : 2≠0), zero_mul] using
        (hq.pow 2).mul_const ((h t/2*(2*t+1))*‖Z‖^2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

theorem thermal_limit_entries {ρ : ℕ → State n} {k : ℕ → ℝ} {σ : State n}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t)
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op))
    (hμ : ∀ j, Tendsto (fun m => (G m).annihilationMean j) atTop (𝓝 0))
    (hq : ∀ j, Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0))
    (p b : NumberIndex n) :
    entry σ.op p b = if p=b then (QuantumTrace.thermalWeight n t p:ℂ) else 0 := by
  have hz (j : Fin n) (a b : NumberIndex n) :
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry σ.op b (up j a)-
        (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry σ.op (down j b) a=0 := by
    have hl := weakDefect_tendsto G hk t ht j (hq j) (numberMatrixUnit a b)
    simp only [(G _).weakDefect_numberMatrixUnit] at hl
    have hr := (((entry_tendsto he b (up j a)).const_mul
      ((t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ))).sub
      ((entry_tendsto he (down j b) a).const_mul ((t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)))).sub
      ((Complex.continuous_conj.tendsto 0 |>.comp (hμ j)).mul (entry_tendsto he b a))
    have hh := tendsto_nhds_unique hr hl
    simpa only [map_zero, zero_mul, sub_zero] using hh
  have hb : ThermalRecurrence.Balance t (entry σ.op) := by
    intro j p b hp
    have hh := congrArg conj (hz j (down j p) b)
    have hdown : (down j p j:ℝ)+1=p j := by
      simp only [down, Function.update_self]
      exact_mod_cast Nat.sub_add_cancel hp
    have hlow (a : NumberIndex n) : ThermalRecurrence.lower a j=down j a := rfl
    simp only [map_sub, map_mul, map_add, map_one, Complex.conj_ofReal, map_zero,
      ← state_entry_star, up_down j p hp, hdown] at hh
    simpa only [hlow, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_one, mul_assoc] using sub_eq_zero.mp hh
  exact ThermalRecurrence.unique_thermal_matrix n ht hb (state_entry_star σ) σ.trace_one p b
end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder

theorem thermalState_energy (n : ℕ) (r : ℝ) (hr : 0<r) :
    energy (thermalState n r hr)=(n:ℝ)*r := by
  let X := WeightedColumns.canonical (thermalState n r hr) (thermalState_finiteMoment n 6 r hr)
  rw [← X.sum_lowerEnergy]
  simp only [X.thermal_lowerEnergy r hr (Regularization.thermal_state_diagonal r hr),
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem thermalState_entropy (n : ℕ) (r : ℝ) (hr : 0<r) :
    entropy (thermalState n r hr)=(n:ℝ)*g r := by
  have hE : Summable (fun k : NumberIndex n => (∑ j, (k j:ℝ))*thermalWeight n r k) := by
    simpa only [FiniteEnergy,thermalState,diagonalState_diagonal,totalNumber,Nat.cast_sum] using
      thermalState_finiteEnergy n r hr
  have hs := tsum_thermal_crossEntropy (hasSum_thermalWeight n hr) hE hr
  have he : (∑' k : NumberIndex n, (∑ j, (k j:ℝ))*thermalWeight n r k)=(n:ℝ)*r := by
    simpa only [energy,thermalState,diagonalState_diagonal,totalNumber,Nat.cast_sum] using
      thermalState_energy n r hr
  rw [he] at hs
  rw [thermalState,diagonalState_entropy]
  have hh : (∑' k : NumberIndex n, Real.negMulLog (thermalWeight n r k))=
      ∑' k : NumberIndex n, thermalWeight n r k*(-Real.log (thermalWeight n r k)) := by
    apply tsum_congr
    intro k
    simp only [Real.negMulLog_def]
    ring
  rw [hh,hs]
  unfold g
  rw [Real.log_div (by linarith : r+1≠0) hr.ne']
  ring

theorem thermal_beamOutput {n : ℕ} (η a b : ℝ) (hη : η∈Set.Icc 0 1)
    (ha : 0<a) (hb : 0<b) (hc : 0<η*a+(1-η)*b) :
    beamOutput η hη (thermalState n a ha) (thermalState n b hb)=
      thermalState n (η*a+(1-η)*b) hc := by
  let ρ := thermalState n a ha
  let σ := thermalState n b hb
  let τ := beamOutput η hη ρ σ
  let X := WeightedColumns.canonical ρ (thermalState_finiteMoment n 6 a ha)
  let Y := WeightedColumns.canonical σ (thermalState_finiteMoment n 6 b hb)
  let T := WeightedColumns.canonical τ (beamOutput_finiteMoment η hη
    (thermalState_finiteMoment n 6 a ha) (thermalState_finiteMoment n 6 b hb))
  let c := η*a+(1-η)*b
  have hz (j : Fin n) (p q : NumberIndex n) :
      (c+1:ℂ)*(Real.sqrt ((p j:ℝ)+1):ℂ)*entry τ.op q (up j p)-
        (c:ℂ)*(Real.sqrt (q j:ℝ):ℂ)*entry τ.op (down j q) p=0 := by
    have hh := physical_product_weak η a b hη ρ σ τ (beamOutput_spec _ _ _ _) j
      X.vector Y.vector T.vector X.summable Y.summable T.summable X.normalized Y.normalized
      X.density Y.density T.density (numberMatrixUnit p q)
    rw [X.thermal_weak_zero a ha (Regularization.thermal_state_diagonal a ha),
      Y.thermal_weak_zero b hb (Regularization.thermal_state_diagonal b hb),mul_zero,mul_zero,add_zero] at hh
    have hw := WeightedGenerator.weakDefect_numberMatrixUnit c T.vector T.summable τ T.base_density j 0 p q
    rw [WeightedGenerator.weakDefect_uncentered c T.vector T.summable j 0,
      map_zero,zero_mul,sub_zero] at hw
    simpa only [map_zero,zero_mul,sub_zero] using hw.symm.trans hh
  have hbalance : ThermalRecurrence.Balance c (entry τ.op) := by
    intro j p q hp
    have hh := congrArg conj (hz j (down j p) q)
    have hdown : (down j p j:ℝ)+1=p j := by
      simp only [down,Function.update_self]
      exact_mod_cast Nat.sub_add_cancel hp
    have hlow (k : NumberIndex n) : ThermalRecurrence.lower k j=down j k := rfl
    simp only [map_sub,map_mul,map_add,map_one,Complex.conj_ofReal,map_zero,
      ← state_entry_star,up_down j p hp,hdown] at hh
    simpa only [hlow,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_one,mul_assoc] using sub_eq_zero.mp hh
  apply State.ext_op
  apply entry_ext
  intro p q
  exact (ThermalRecurrence.unique_thermal_matrix n hc hbalance (state_entry_star τ) τ.trace_one p q).trans
    (Regularization.thermal_state_diagonal c hc p q).symm

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
theorem output_thermal (ζ : ℝ) (hζ : 0<ζ) :
    (P.reg n ζ hζ).output (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)=
      thermalState n P.r0 P.r0_pos := by
  have hm : 0<P.η*P.r1+(1-P.η)*P.r2 := add_pos (mul_pos P.hη.1 P.hr1)
    (mul_pos (sub_pos.mpr P.hη.2) P.hr2)
  have hh : P.raw (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)=
      thermalState n P.r0 P.r0_pos := by
    unfold raw middle
    rw [thermal_beamOutput P.η P.r1 P.r2 P.η_mem P.hr1 P.hr2 hm]
    exact thermal_beamOutput P.θ _ P.d P.θ_mem hm P.hd P.r0_pos
  apply State.ext_op
  rw [P.output_op,hh]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [add_apply,smul_apply]
  rw [← add_smul]
  norm_num
end ThermalSetup
end

section
open QuantumTrace Annihilation Filter ThermalMetric

theorem op_mem_energySet {n : ℕ} {ρ : State n} {E : ℝ}
    (hρ : FiniteEnergy ρ) (hb : energy ρ≤E) : ρ.op∈energySet (numberBasis n) E := by
  refine ⟨ρ.positive,trace_one_numberBasis ρ,?_,?_⟩
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hρ
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hb

theorem pair_energy_subsequence {n : ℕ} {ρ σ : ℕ → State n} {E : ℝ}
    (hρ : ∀ m, FiniteEnergy (ρ m)) (hσ : ∀ m, FiniteEnergy (σ m))
    (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ (α β : State n), FiniteEnergy α ∧ FiniteEnergy β ∧ energy α≤E ∧ energy β≤E ∧
      ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 α.op) ∧
        Tendsto (fun m => (σ (f m)).op) atTop (𝓝 β.op) := by
  have hc := (energySet_isCompact (numberBasis n) E).prod (energySet_isCompact (numberBasis n) E)
  obtain ⟨p,hp,f,hf,hlim⟩ := hc.tendsto_subseq (fun m =>
    (show ((ρ m).op,(σ m).op)∈energySet (numberBasis n) E ×ˢ energySet (numberBasis n) E from
      ⟨op_mem_energySet (hρ m) (hbρ m),op_mem_energySet (hσ m) (hbσ m)⟩))
  let α : State n := ⟨p.1,hp.1.1,by simpa only [numberBasis_apply,entry] using hp.1.2.1⟩
  let β : State n := ⟨p.2,hp.2.1,by simpa only [numberBasis_apply,entry] using hp.2.2.1⟩
  refine ⟨α,β,?_,?_,?_,?_,f,hf,?_,?_⟩
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,α] using hp.1.2.2.1
  · simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,β] using hp.2.2.2.1
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,α] using hp.1.2.2.2
  · simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply,β] using hp.2.2.2.2
  · simpa only [Function.comp_def,α] using (continuous_fst.tendsto p).comp hlim
  · simpa only [Function.comp_def,β] using (continuous_snd.tendsto p).comp hlim

theorem thermal_limit_state {n : ℕ} {ρ : ℕ → State n} {k : ℕ → ℝ} {σ : State n}
    (G : ∀ m, GibbsData n (k m) (ρ m)) (hk : ∀ m, 0<k m)
    (t : ℝ) (ht : 0<t)
    (he : Tendsto (fun m => (ρ m).op) atTop (𝓝 σ.op))
    (hμ : ∀ j, Tendsto (fun m => (G m).annihilationMean j) atTop (𝓝 0))
    (hq : ∀ j, Tendsto (fun m => ‖(G m).defect (hk m) t ht j‖) atTop (𝓝 0)) :
    σ=thermalState n t ht := by
  apply State.ext_op
  apply entry_ext
  intro p b
  exact (thermal_limit_entries G hk t ht he hμ hq p b).trans
    (Regularization.thermal_state_diagonal t ht p b).symm

theorem component_tendsto_zero {n : ℕ} {v : ℕ → Fin n → ℝ} {B : ℕ → ℝ}
    {w : ℝ} (hw : 0<w) (hv : ∀ m j, 0≤v m j)
    (hb : ∀ m, w*(∑ j, (v m j)^2)≤B m) (hB : Tendsto B atTop (𝓝 0))
    (j : Fin n) : Tendsto (fun m => v m j) atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => (v m j)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (fun m => (show (v m j)^2≤B m/w from (le_div_iff₀ hw).mpr ?_))
      (by simpa only [zero_div] using hB.div_const w)
    have hh := Finset.single_le_sum (fun i (_hi : i∈(Finset.univ : Finset (Fin n))) => sq_nonneg (v m i))
      (Finset.mem_univ j)
    nlinarith [mul_le_mul_of_nonneg_left hh hw.le,hb m]
  simpa only [Function.comp_def,Real.sqrt_sq (hv _ _),Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

theorem weighted_pair_components {w u a b c d B : ℝ} (hw : 0≤w) (hu : 0≤u)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hh : w*(a+b)+u*(c+d)≤B) : w*a≤B ∧ w*b≤B ∧ u*c≤B ∧ u*d≤B := by
  have hwa := mul_nonneg hw ha
  have hwb := mul_nonneg hw hb
  have huc := mul_nonneg hu hc
  have hud := mul_nonneg hu hd
  simp only [mul_add] at hh
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem four_components_tendsto_zero {n : ℕ} {q1 q2 μ1 μ2 : ℕ → Fin n → ℝ}
    {w1 w2 : ℝ} (hw1 : 0<w1) (hw2 : 0<w2) {B : ℕ → ℝ}
    (hq1 : ∀ m j, 0≤q1 m j) (hq2 : ∀ m j, 0≤q2 m j)
    (hμ1 : ∀ m j, 0≤μ1 m j) (hμ2 : ∀ m j, 0≤μ2 m j)
    (hb : ∀ m, w1*((∑ j, (q1 m j)^2)+(∑ j, (μ1 m j)^2))+
      w2*((∑ j, (q2 m j)^2)+(∑ j, (μ2 m j)^2))≤B m)
    (hB : Tendsto B atTop (𝓝 0)) :
    (∀ j, Tendsto (fun m => q1 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => q2 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => μ1 m j) atTop (𝓝 0)) ∧
    (∀ j, Tendsto (fun m => μ2 m j) atTop (𝓝 0)) := by
  have hn (v : ℕ → Fin n → ℝ) (m) : 0≤∑ j, (v m j)^2 :=
    Finset.sum_nonneg (fun _j _ => sq_nonneg _)
  have hh (m) := weighted_pair_components hw1.le hw2.le
    (hn q1 m) (hn μ1 m) (hn q2 m) (hn μ2 m) (hb m)
  exact ⟨component_tendsto_zero hw1 hq1 (fun m => (hh m).1) hB,
    component_tendsto_zero hw2 hq2 (fun m => (hh m).2.2.1) hB,
    component_tendsto_zero hw1 hμ1 (fun m => (hh m).2.1) hB,
    component_tendsto_zero hw2 hμ2 (fun m => (hh m).2.2.2) hB⟩

theorem pair_thermal_subsequence {n : ℕ} {ρ σ : ℕ → State n} {k1 k2 : ℕ → ℝ}
    (G1 : ∀ m, GibbsData n (k1 m) (ρ m)) (G2 : ∀ m, GibbsData n (k2 m) (σ m))
    (hk1 : ∀ m, 0<k1 m) (hk2 : ∀ m, 0<k2 m) (r1 r2 : ℝ) (hr1 : 0<r1) (hr2 : 0<r2)
    (hq1 : ∀ j, Tendsto (fun m => ‖(G1 m).defect (hk1 m) r1 hr1 j‖) atTop (𝓝 0))
    (hq2 : ∀ j, Tendsto (fun m => ‖(G2 m).defect (hk2 m) r2 hr2 j‖) atTop (𝓝 0))
    (hμ1 : ∀ j, Tendsto (fun m => ‖(G1 m).annihilationMean j‖) atTop (𝓝 0))
    (hμ2 : ∀ j, Tendsto (fun m => ‖(G2 m).annihilationMean j‖) atTop (𝓝 0))
    (hρ : ∀ m, FiniteEnergy (ρ m)) (hσ : ∀ m, FiniteEnergy (σ m))
    {E : ℝ} (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 (thermalState n r1 hr1).op) ∧
      Tendsto (fun m => (σ (f m)).op) atTop (𝓝 (thermalState n r2 hr2).op) := by
  obtain ⟨α,β,_hα,_hβ,_hbα,_hbβ,f,hf,hlim1,hlim2⟩ := pair_energy_subsequence hρ hσ hbρ hbσ
  have he1 := thermal_limit_state (fun m => G1 (f m)) (fun m => hk1 (f m)) r1 hr1 hlim1
    (fun j => (tendsto_zero_iff_norm_tendsto_zero.mpr (hμ1 j)).comp hf.tendsto_atTop)
    (fun j => (hq1 j).comp hf.tendsto_atTop)
  have he2 := thermal_limit_state (fun m => G2 (f m)) (fun m => hk2 (f m)) r2 hr2 hlim2
    (fun j => (tendsto_zero_iff_norm_tendsto_zero.mpr (hμ2 j)).comp hf.tendsto_atTop)
    (fun j => (hq2 j).comp hf.tendsto_atTop)
  exact ⟨f,hf,by simpa only [he1] using hlim1,by simpa only [he2] using hlim2⟩

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
theorem minimum_thermal_subsequence {ζ : ℕ → ℝ} (hζ : ∀ m, 0<ζ m)
    (hzlim : Tendsto ζ atTop (𝓝 0)) {ρ σ : ℕ → State n}
    (h4ρ : ∀ m, FiniteMoment 4 (ρ m)) (h4σ : ∀ m, FiniteMoment 4 (σ m))
    (hmin : ∀ m ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n (ζ m) (hζ m)).objective (ρ m) (σ m)≤(P.reg n (ζ m) (hζ m)).objective ρ' σ')
    {E : ℝ} (hbρ : ∀ m, energy (ρ m)≤E) (hbσ : ∀ m, energy (σ m)≤E) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun m => (ρ (f m)).op) atTop (𝓝 (thermalState n P.r1 P.hr1).op) ∧
      Tendsto (fun m => (σ (f m)).op) atTop (𝓝 (thermalState n P.r2 P.hr2).op) := by
  obtain ⟨C,_hC,hdec⟩ := P.uniform_minimum_decay (n:=n)
  choose G1 G2 hG using fun m => hdec (ζ m) (hζ m) (ρ m) (σ m) (h4ρ m) (h4σ m) (hmin m)
  let k1 := fun m => ζ m/((1+P.ε)*P.w1/h P.r1)
  let k2 := fun m => ζ m/((1+P.ε)*P.w2/h P.r2)
  have hk1 (m) : 0<k1 m := div_pos (hζ m) (P.reg n (ζ m) (hζ m)).ha1
  have hk2 (m) : 0<k2 m := div_pos (hζ m) (P.reg n (ζ m) (hζ m)).ha2
  have hB : Tendsto (fun m => C*ζ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using hzlim.const_mul C
  obtain ⟨hq1,hq2,hμ1,hμ2⟩ := four_components_tendsto_zero (q1:=fun m j => ‖(G1 m).defect (hk1 m) P.r1 P.hr1 j‖)
    (q2:=fun m j => ‖(G2 m).defect (hk2 m) P.r2 P.hr2 j‖)
    (μ1:=fun m j => ‖(G1 m).annihilationMean j‖)
    (μ2:=fun m j => ‖(G2 m).annihilationMean j‖) P.w1_pos P.w2_pos
    (fun m j => norm_nonneg ((G1 m).defect (hk1 m) P.r1 P.hr1 j))
    (fun m j => norm_nonneg ((G2 m).defect (hk2 m) P.r2 P.hr2 j))
    (fun m j => norm_nonneg ((G1 m).annihilationMean j))
    (fun m j => norm_nonneg ((G2 m).annihilationMean j)) hG hB
  exact pair_thermal_subsequence G1 G2 hk1 hk2 P.r1 P.r2 P.hr1 P.hr2 hq1 hq2 hμ1 hμ2
    (fun m => finiteMoment_finiteEnergy (by decide : 1≤4) (h4ρ m))
    (fun m => finiteMoment_finiteEnergy (by decide : 1≤4) (h4σ m)) hbρ hbσ
end ThermalSetup
end

open QuantumTrace ThermalMetric Filter

def thermalRelative {n : ℕ} (r : ℝ) (ρ : State n) : ℝ :=
  n*Real.log (r+1)+h r*energy ρ-entropy ρ

theorem thermalRelative_nonneg {n : ℕ} {r : ℝ} (hr : 0<r) {ρ : State n}
    (hρ : FiniteEnergy ρ) : 0≤thermalRelative r ρ := by
  have hh := entropy_le_thermal_crossEntropy (numberBasis n) ρ.positive
    (trace_one_numberBasis ρ)
    (by simpa only [FiniteEnergy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hρ) hr
  rw [← entropy_eq_quantumTrace] at hh
  have hh' : entropy ρ≤n*Real.log (r+1)+energy ρ*Real.log ((r+1)/r) := by
    simpa only [energy,totalNumber,Nat.cast_sum,entry,numberBasis_apply] using hh
  rw [Real.log_div (by linarith : r+1≠0) hr.ne'] at hh'
  unfold thermalRelative h
  nlinarith

namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)
def out (ρ σ : State n) : State n := (P.reg n 1 zero_lt_one).output ρ σ

def entropyPart (ρ σ : State n) : ℝ :=
  (entropy (P.out ρ σ)-n*g P.r0)/h P.r0-
    P.w1*(entropy ρ-n*g P.r1)/h P.r1-P.w2*(entropy σ-n*g P.r2)/h P.r2

def penalty (ρ σ : State n) : ℝ :=
  P.ε*(P.w1/h P.r1*thermalRelative P.r1 ρ+P.w2/h P.r2*thermalRelative P.r2 σ)

def offset (n : ℕ) : ℝ :=
  -n*g P.r0/h P.r0+P.w1*n*g P.r1/h P.r1+P.w2*n*g P.r2/h P.r2+
    P.ε*(P.w1/h P.r1*(n*Real.log (P.r1+1))+P.w2/h P.r2*(n*Real.log (P.r2+1)))

theorem objective_offset (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    (P.reg n ζ hζ).objective ρ σ+P.offset n=
      P.entropyPart ρ σ+P.penalty ρ σ+ζ*(numberMoment 4 ρ+numberMoment 4 σ) := by
  unfold Regularization.objective entropyPart penalty offset thermalRelative
  change (1/h P.r0)*entropy (P.out ρ σ)-((1+P.ε)*P.w1/h P.r1)*entropy ρ-
    ((1+P.ε)*P.w2/h P.r2)*entropy σ+(P.ε*P.w1*energy ρ+ζ*numberMoment 4 ρ)+
    (P.ε*P.w2*energy σ+ζ*numberMoment 4 σ)+_= _
  field_simp [(h_pos P.hr1).ne', (h_pos P.hr2).ne', (h_pos P.r0_pos).ne']
  ring

theorem penalty_nonneg {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    0≤P.penalty ρ σ :=
  mul_nonneg P.hε.le (add_nonneg
    (mul_nonneg (div_pos P.w1_pos (h_pos P.hr1)).le (thermalRelative_nonneg P.hr1 hρ))
    (mul_nonneg (div_pos P.w2_pos (h_pos P.hr2)).le (thermalRelative_nonneg P.hr2 hσ)))

theorem entropyPart_tendsto {A : Type*} {l : Filter A} {ρ σ : A → State n}
    {E : ℝ} (hρ : ∀ a, FiniteEnergy (ρ a)) (hσ : ∀ a, FiniteEnergy (σ a))
    (hbρ : ∀ a, energy (ρ a)≤E) (hbσ : ∀ a, energy (σ a)≤E)
    (hlimρ : Tendsto (fun a => (ρ a).op) l (𝓝 (thermalState n P.r1 P.hr1).op))
    (hlimσ : Tendsto (fun a => (σ a).op) l (𝓝 (thermalState n P.r2 P.hr2).op)) :
    Tendsto (fun a => P.entropyPart (ρ a) (σ a)) l (𝓝 0) := by
  let E' := max E (max ((n:ℝ)*P.r1) ((n:ℝ)*P.r2))
  have hb1 (a) : energy (ρ a)≤E' := (hbρ a).trans (le_max_left _ _)
  have hb2 (a) : energy (σ a)≤E' := (hbσ a).trans (le_max_left _ _)
  have hc1 : energy (thermalState n P.r1 P.hr1)≤E' := by
    rw [thermalState_energy]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hc2 : energy (thermalState n P.r2 P.hr2)≤E' := by
    rw [thermalState_energy]; exact (le_max_right _ _).trans (le_max_right _ _)
  have h1 := tendsto_entropy hρ (thermalState_finiteEnergy n _ P.hr1) hb1 hc1 hlimρ
  have h2 := tendsto_entropy hσ (thermalState_finiteEnergy n _ P.hr2) hb2 hc2 hlimσ
  let R := P.reg n 1 zero_lt_one
  have h0 : Tendsto (fun a => entropy (P.out (ρ a) (σ a))) l
      (𝓝 (entropy (P.out (thermalState n P.r1 P.hr1) (thermalState n P.r2 P.hr2)))) := by
    apply tendsto_entropy (E:=E'+E'+energy R.τD+energy R.τ0)
      (fun a => regularizedOutput_finiteEnergy R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0 (hρ a) (hσ a))
      (regularizedOutput_finiteEnergy R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0
        (thermalState_finiteEnergy n _ P.hr1) (thermalState_finiteEnergy n _ P.hr2))
    · intro a
      exact (regularizedOutput_energy_bound R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0 (hρ a) (hσ a)).trans
        (by linarith [hb1 a,hb2 a])
    · exact (regularizedOutput_energy_bound R.η R.δ R.κ R.hη R.hδ R.hκ R.finiteD R.finite0
        (thermalState_finiteEnergy n _ P.hr1) (thermalState_finiteEnergy n _ P.hr2)).trans
        (by linarith)
    · exact tendsto_regularizedOutput R.η R.δ R.κ R.hη R.hδ R.hκ R.τD R.τ0 hlimρ hlimσ
  have he := (((h0.sub_const (n*g P.r0)).div_const (h P.r0)).sub
    ((h1.sub_const (n*g P.r1)).const_mul P.w1 |>.div_const (h P.r1))).sub
    ((h2.sub_const (n*g P.r2)).const_mul P.w2 |>.div_const (h P.r2))
  simpa only [out,P.output_thermal,thermalState_entropy,sub_self,mul_zero,zero_div,entropyPart] using he

theorem base_nonnegative {ρw σw : State n} (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    0≤P.entropyPart ρw σw+P.penalty ρw σw := by
  let ζ : ℕ → ℝ := fun m => 1/((m:ℝ)+1)
  have hζ (m) : 0<ζ m := by dsimp [ζ]; positivity
  have hζ1 (m) : ζ m≤1 := by
    dsimp [ζ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hzlim : Tendsto ζ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose ρ σ h4ρ h4σ hminw hmin using fun m => (P.reg n (ζ m) (hζ m)).exists_minimum ρw σw hw1 hw2
  have hρ (m) := finiteMoment_finiteEnergy (by decide : 1≤4) (h4ρ m)
  have hσ (m) := finiteMoment_finiteEnergy (by decide : 1≤4) (h4σ m)
  let R := P.reg n 1 zero_lt_one
  let C := R.objective ρw σw
  have hbmin (m) : (P.reg n (ζ m) (hζ m)).objective (ρ m) (σ m)≤C := by
    apply (hminw m).trans
    have hzm := mul_le_mul_of_nonneg_right (hζ1 m)
      (add_nonneg (numberMoment_nonneg 4 ρw) (numberMoment_nonneg 4 σw))
    have h1 := P.objective_offset (ζ m) (hζ m) ρw σw
    have h2 := P.objective_offset 1 zero_lt_one ρw σw
    dsimp [C,R]
    linarith
  let E := max (2*(C+R.entropyConstant)/R.b1) (2*(C+R.entropyConstant)/R.b2)
  have hbρ (m) : energy (ρ m)≤E := by
    have hh := (P.reg n (ζ m) (hζ m)).sublevel_bounds C (ρ m) (σ m) (hρ m) (hσ m) (hbmin m)
    exact hh.2.1.trans (le_max_left _ _)
  have hbσ (m) : energy (σ m)≤E := by
    have hh := (P.reg n (ζ m) (hζ m)).sublevel_bounds C (ρ m) (σ m) (hρ m) (hσ m) (hbmin m)
    exact hh.2.2.1.trans (le_max_right _ _)
  obtain ⟨f,hf,hlim1,hlim2⟩ := P.minimum_thermal_subsequence hζ hzlim h4ρ h4σ hmin hbρ hbσ
  have he := P.entropyPart_tendsto (fun m => hρ (f m)) (fun m => hσ (f m))
    (fun m => hbρ (f m)) (fun m => hbσ (f m)) hlim1 hlim2
  have hu : Tendsto (fun m => P.entropyPart ρw σw+P.penalty ρw σw+
      ζ (f m)*(numberMoment 4 ρw+numberMoment 4 σw)) atTop
      (𝓝 (P.entropyPart ρw σw+P.penalty ρw σw)) := by
    simpa only [zero_mul,add_zero,Function.comp_apply] using
      ((hzlim.comp hf.tendsto_atTop).mul_const (numberMoment 4 ρw+numberMoment 4 σw)).const_add
        (P.entropyPart ρw σw+P.penalty ρw σw)
  apply le_of_tendsto_of_tendsto he hu
  filter_upwards [] with m
  have hp := P.penalty_nonneg (hρ (f m)) (hσ (f m))
  have hm := mul_nonneg (hζ (f m)).le
    (add_nonneg (numberMoment_nonneg 4 (ρ (f m))) (numberMoment_nonneg 4 (σ (f m))))
  have h1 := P.objective_offset (ζ (f m)) (hζ (f m)) (ρ (f m)) (σ (f m))
  have h2 := P.objective_offset (ζ (f m)) (hζ (f m)) ρw σw
  linarith [hminw (f m)]
end ThermalSetup
end EntropyPhotonNumber

end

end OAI
