import OAI.NumberTheory.DirichletL.Inversion.InitialProfile
import OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
import OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source (w : ℝ → ℂ) (c h x : ℝ) :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping (w : ℝ → ℂ) {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = logPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem clippedTest_support_of_freshColumns (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N h : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hZ : 1 < Z)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    Function.support (clippedTest w (Z^(max 0 N-N)) h) ⊆ Set.Icc (a/b) b := by
  obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hs := InverseClippingProfiles.clipped_positive_support w a b _ ha hc hcb hw
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

theorem canonical_row_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem canonical_row_nonzero_freshColumns
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ)
    (hn : finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X ≠ 0) : (freshColumns p pool w X).Nonempty := by
  by_contra he
  exact hn (canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m f k
    slots lists a w X h (Finset.not_nonempty_iff_eq_empty.mp he))

theorem canonical_row_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

def columnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

theorem columnEnergy_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold columnEnergy
  simp_rw [canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _ slots lists a w hZ N h]

theorem canonical_pair_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ h₁) (Z^N) *
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ (-h₂)) (Z^N)) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) h₁) (Z^(max 0 N)) *
      star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) (-h₂)) (Z^(max 0 N)))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

theorem canonical_pair_clipping_left_conjugate
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ (-h₁)) (Z^N)) *
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ h₂) (Z^N) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) (-h₁)) (Z^(max 0 N))) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) h₂) (Z^(max 0 N))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

def normalizedColumnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N V h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hp hcop hg pool Ψ m slots lists a labels rows D w hZ N h]
  exact columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows D
    _ _ hZ _

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

theorem leftHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

def clippingPhase (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) : ℂ :=
  logPhase (leftHeight z+rightHeight z) (Real.log c)

theorem clippingPhase_norm (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) :
    ‖clippingPhase c z‖ = 1 := logPhase_norm _ _

theorem clippingPhase_continuous (c : ℝ) : Continuous (clippingPhase c) := by
  unfold clippingPhase leftHeight rightHeight logPhase
  fun_prop

theorem fresh_pair_mode_clipping (w₁ w₂ : ℝ → ℂ)
    {Z q₁ q₂ : ℝ} (hZ : 0 < Z) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (N : ℝ) (y : Fin 6 → ℝ) (z : Frequency × (Fin 6 → ℝ))
    (hy₁ : y 4 = Real.log (q₁/Z^N)) (hy₂ : y 5 = Real.log (q₂/Z^N)) :
    (w₁ (q₁/Z^N)*star (w₂ (q₂/Z^N))) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y z.1 z.2 =
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
      clippingPhase (Z^(max 0 N-N)) z *
      (clippedTest w₁ (Z^(max 0 N-N)) (leftHeight z) (q₁/Z^(max 0 N)) *
      star (clippedTest w₂ (Z^(max 0 N-N)) (-rightHeight z) (q₂/Z^(max 0 N)))) := by
  rw [second_mode_split,← leftHeight_eq,← rightHeight_eq,hy₁,hy₂]
  have h1 := child_test_clipping w₁ hZ hq₁ N (leftHeight z)
  have h2 := child_test_clipping w₂ hZ hq₂ N (-rightHeight z)
  calc
    _ = secondOuterPhase
        (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
        (childLogTest w₁ (leftHeight z) (q₁/Z^N) *
          star (childLogTest w₂ (-rightHeight z) (q₂/Z^N))) := by
      simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg]
      ring
    _ = _ := by
      rw [h1,h2]
      simp only [clippingPhase,star_mul,SecondPassIntegration.logPhase_conjugate,
        neg_neg,logPhase_add_frequency]
      ring

theorem child_height_moment_bound (K : ℕ) (z : Frequency × (Fin 6 → ℝ)) :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

def retainedCutoffs (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![ψ 0,ψ 1,ψ 2,ψ 3,w₁,w₂]

theorem retainedCutoffs_nonzero (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (x : Fin 6 → ℝ) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, retainedCutoffs ψ w₁ w₂ i (x i) ≠ 0 := by
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  intro i
  fin_cases i <;> simp only [retainedCutoffs]
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2
  · exact h₁
  · exact h₂

theorem larger_windows_one (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (Ω : Fin 6 → ℝ → ℂ)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, Ω i (Real.exp (Real.log (x i))) = 1 := by
  intro i
  rw [Real.exp_log (hx i)]
  exact hΩ i (x i) (retainedCutoffs_nonzero ψ w₁ w₂ x ho h₁ h₂ i)

theorem retained_physical_kernel_restore
    (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (ψ : Fin 4 → ℝ → ℂ) (Ω : Fin 6 → ℝ → ℂ)
    (a b A₀ B₀ A₂ B₂ : ℝ) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hW₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hψ₀ : ∀ x, ψ 0 x ≠ 0 → x ∈ Set.Icc A₀ B₀)
    (hψ₂ : ∀ x, ψ 2 x ≠ 0 → x ∈ Set.Icc A₂ B₂)
    (hw₁ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₁ x = 1)
    (hw₂ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₂ x = 1)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    let x := InverseInitialProfile.relativeNorm q Z D B v θ H
    outerCutoff ψ x * InverseInitialProfile.physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(InverseInitialProfile.prefactorCenter m D B θ+3*η) : ℝ) *
        outerCutoff ψ x * (w₁ (x 4)*w₂ (x 5)) *
        InverseInitialProfile.normalizedProfile W₁ W₂ Φ (fun i y => Ω i (Real.exp y))
          (Z^(InverseInitialProfile.radialCenter m H θ D B)) (η*Real.log Z)
          (InverseInitialProfile.relativeLog q Z D B v θ H) := by
  dsimp only
  let x := InverseInitialProfile.relativeNorm q Z D B v θ H
  have hx : ∀ i, 0 < x i := InverseInitialProfile.relativeNorm_pos q hq hZ D B v θ H
  by_cases ho : outerCutoff ψ x = 0
  · change outerCutoff ψ x * _ = _ * outerCutoff ψ x * _ * _
    simp only [ho,zero_mul,mul_zero]
  have hc : ψ 0 (x 0) ≠ 0 := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).1 |> mul_ne_zero_iff.mp).1
  have hs : ψ 2 (x 2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2
  have h1 : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1 :=
    fresh_window_eq_one W₁ w₁ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 4)
      hW₁ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 4).le hw₁
  have h2 : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1 :=
    fresh_window_eq_one W₂ w₂ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 5)
      hW₂ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 5).le hw₂
  have hcut : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 →
      ∀ i, Ω i (Real.exp (InverseInitialProfile.relativeLog q Z D B v θ H i)) = 1 := by
    intro hleft hright
    exact larger_windows_one ψ w₁ w₂ Ω hΩ x hx ho hleft hright
  have he := InverseInitialProfile.initial_kernel_restore W₁ W₂ w₁ w₂ Φ
    (fun i y => Ω i (Real.exp y)) hZ D B v m θ H η q hq h1 h2 hcut
  rw [he]
  ring

end SevenEighths.InverseInitialClippedColumns

end

end OAI
