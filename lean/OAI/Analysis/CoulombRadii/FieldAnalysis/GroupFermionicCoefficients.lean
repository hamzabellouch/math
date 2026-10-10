import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Translate

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter
open scoped Convolution
open ContinuousLinearMap

def GroupFermionicCoefficients {n : ℕ} {ι : Type*} (g : Fin n → ι)
    (f : (Fin n → SpinMode) → ℂ) : Prop :=
  ∀ p : Equiv.Perm (Fin n), g ∘ p = g → ∀ a,
    f (a ∘ p) = ((p.sign : ℤ) : ℂ) * f a

lemma GroupFermionicCoefficients.vanish_of_repeat {n : ℕ} {ι : Type*}
    {g : Fin n → ι} {f : (Fin n → SpinMode) → ℂ}
    (hf : GroupFermionicCoefficients g f) {a : Fin n → SpinMode}
    {i j : Fin n} (hne : i ≠ j) (hg : g i = g j) (ha : a i = a j) : f a = 0 := by
  classical
  have hgp : g ∘ Equiv.swap i j = g := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using hg.symm
    by_cases hj : k = j
    · subst k; simpa using hg
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have hap : a ∘ Equiv.swap i j = a := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using ha.symm
    by_cases hj : k = j
    · subst k; simpa using ha
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have H := hf (Equiv.swap i j) hgp a
  rw [hap, Equiv.Perm.sign_swap hne] at H
  norm_num at H
  linear_combination (1/2 : ℂ) * H

noncomputable def groupNeumannLower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (b : ℝ) : ℝ :=
  ∑ k : ι, (b⁻¹)^2 *
    (thomasFermiCoefficient * (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (4/3 : ℝ))

lemma grouped_neumann_spectral_lower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (a : Fin n → SpinMode)
    (hinj : Function.Injective (fun i => (g i, a i))) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b ≤ cubeSpectralWeight b a := by
  classical
  rw [cubeSpectralWeight_eq_neumann, groupNeumannLower]
  have hlocal (k : ι) :
      (b⁻¹)^2 * (thomasFermiCoefficient *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) *
        (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (4/3 : ℝ)) ≤
      ∑ i : {i : Fin n // g i = k},
        (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
    let E := Fintype.equivFin {i : Fin n // g i = k}
    have hai : Function.Injective (fun i : {i : Fin n // g i = k} => a i) := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact Prod.ext (i.property.trans j.property.symm) hij
    have H := neumann_kinetic_sum_lower (fun i => a (E.symm i))
      (hai.comp E.symm.injective) hb
    rw [Equiv.sum_comp E.symm (fun i => (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2)] at H
    exact H
  calc
    _ ≤ ∑ k : ι, ∑ i : {i : Fin n // g i = k},
        (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = ∑ i : Fin n, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
      simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
        (Equiv.sum_comp (Equiv.sigmaFiberEquiv g)
          (fun i => (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2))

lemma GroupFermionicCoefficients.spectral_lower {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {g : Fin n → ι} {f : (Fin n → SpinMode) → ℂ}
    (hf : GroupFermionicCoefficients g f) {b : ℝ} (hb : 0 < b)
    (hs : Summable (fun a => ‖f a‖^2))
    (he : Summable (fun a => cubeSpectralWeight b a * ‖f a‖^2)) :
    groupNeumannLower g b * (∑' a, ‖f a‖^2) ≤
      ∑' a, cubeSpectralWeight b a * ‖f a‖^2 := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hs.mul_left _) he
  intro a
  by_cases hz : f a = 0
  · simp [hz]
  have hai : Function.Injective (fun i => (g i,a i)) := by
    intro i j hij
    by_contra hne
    exact hz (hf.vanish_of_repeat hne (congrArg Prod.fst hij) (congrArg Prod.snd hij))
  exact mul_le_mul_of_nonneg_right (grouped_neumann_spectral_lower g a hai hb) (sq_nonneg _)

def GroupAntisymmetric {n : ℕ} (ψ : H1Vector n) {ι : Type*} (g : Fin n → ι) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)), g ∘ p = g → ∀ (s : Spins n),
    ∀ᵐ x ∂volume,
      ψ.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ) * ψ.value s x

lemma cubeFermionCoefficient_group_antisymmetric {n : ℕ} {ψ : H1Vector n}
    {ι : Type*} {g : Fin n → ι}
    (hψ : GroupAntisymmetric ψ g) (b : ℝ) :
    GroupFermionicCoefficients g (cubeFermionCoefficient ψ b) := by
  intro p hgp a
  let e := Equiv.prodCongr p.symm (Equiv.refl (Fin 3))
  have hlabel : (cubeLabelEquiv n (a ∘ p)).2 = (cubeLabelEquiv n a).2 ∘ e.symm := rfl
  have hspin : (cubeLabelEquiv n (a ∘ p)).1 = (cubeLabelEquiv n a).1 ∘ p := rfl
  have hpos (x : (Fin n × Fin 3) → ℝ) :
      WithLp.toLp 2 (reindexCube e x) = permute p (WithLp.toLp 2 x) := by
    ext ij
    simp only [reindexCube_apply, e, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.symm_symm, Equiv.refl_symm]
    rfl
  unfold cubeFermionCoefficient
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun x => star (finiteCubeMode b (cubeLabelEquiv n (a ∘ p)).2 x) *
      ψ.value (cubeLabelEquiv n (a ∘ p)).1 (WithLp.toLp 2 x))]
  simp_rw [hlabel, finiteCubeMode_reindex, hspin, hpos]
  rw [← integral_const_mul]
  apply integral_congr_ae
  have ha := (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae
    (hψ p hgp (cubeLabelEquiv n a).1)
  filter_upwards [ha.filter_mono (ae_mono (finiteCubeMeasure_le_volume b))] with x hx
  rw [hx]
  ring

lemma grouped_fermionic_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {g : Fin n → ι}
    (hψ : GroupAntisymmetric ψ g) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b * cubeMass ψ b ≤ cubeKinetic ψ b := by
  rw [← cubeFermionCoefficient_parseval ψ hb]
  exact (GroupFermionicCoefficients.spectral_lower
    (cubeFermionCoefficient_group_antisymmetric hψ b) hb
    (cubeFermionCoefficient_summable ψ hb)
    (cubeFermionCoefficient_energy_summable hn ψ hb)).trans
      (cubeFermionCoefficient_energy_le hn ψ hb)

lemma translate_group_antisymmetric {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) {ι : Type*} (g : Fin n → ι) (center : ι → Space) :
    GroupAntisymmetric (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) g := by
  intro p hgp s
  let c : Configuration n := WithLp.toLp 2 (fun ij => center (g ij.1) ij.2)
  have hpc : permute p c = c := by
    ext ij
    change center (g (p ij.1)) ij.2 = center (g ij.1) ij.2
    exact congrArg (fun k => center k ij.2) (congrFun hgp ij.1)
  have ha := (measurePreserving_add_right (volume : Measure (Configuration n)) c).quasiMeasurePreserving.ae
    (hψ p s)
  filter_upwards [ha] with x hx
  simpa only [H1Vector.translate, permute_add, hpc] using hx

lemma assigned_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) (center : ι → Space) {b : ℝ} (hb : 0 < b) :
    groupNeumannLower g b *
      cubeMass (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) b ≤
      cubeKinetic (ψ.translate (WithLp.toLp 2 (fun ij => center (g ij.1) ij.2))) b :=
  grouped_fermionic_cube_kinetic_lower hn _ (translate_group_antisymmetric hψ g center) hb

section GridTiling
variable {I : Type*} [Fintype I]

def gridBox (b : ℝ) (k : I → ℤ) : Set (I → ℝ) :=
  Set.univ.pi (fun i => Ioc (b * (k i : ℝ)) (b * ((k i : ℝ)+1)))

lemma gridBox_measurable (b : ℝ) (k : I → ℤ) : MeasurableSet (gridBox b k) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

omit [Fintype I] in
lemma gridBox_disjoint {b : ℝ} (hb : 0 < b) :
    Pairwise (fun k l : I → ℤ => Disjoint (gridBox b k) (gridBox b l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hxl
  apply hkl
  funext i
  have hk := (Set.mem_univ_pi.mp hx) i
  have hl := (Set.mem_univ_pi.mp hxl) i
  have h1 : (k i : ℝ) < (l i : ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hb).mp (hk.1.trans_le hl.2)
  have h2 : (l i : ℝ) < (k i : ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hb).mp (hl.1.trans_le hk.2)
  have h1' : k i < l i + 1 := by exact_mod_cast h1
  have h2' : l i < k i + 1 := by exact_mod_cast h2
  omega

omit [Fintype I] in
lemma gridBox_iUnion {b : ℝ} (hb : 0 < b) :
    (⋃ k : I → ℤ, gridBox b k) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨fun i => ⌈x i / b⌉ - 1, ?_⟩
  apply Set.mem_univ_pi.mpr
  intro i
  have hL := Int.ceil_lt_add_one (x i / b)
  have hU := Int.le_ceil (x i / b)
  constructor
  · have h : (⌈x i/b⌉ : ℝ)-1 < x i/b := by linarith
    have hh := (lt_div_iff₀ hb).mp h
    push_cast
    nlinarith
  · have hh := (div_le_iff₀ hb).mp hU
    push_cast
    nlinarith

lemma finiteCubeMeasure_eq_restrict (b : ℝ) :
    finiteCubeMeasure b I = volume.restrict (Set.univ.pi (fun _ : I => Ioc 0 b)) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

omit [Fintype I] in
lemma gridBox_preimage_add (b : ℝ) (k : I → ℤ) :
    (fun x : I → ℝ => x + (fun i => b*(k i : ℝ))) ⁻¹' gridBox b k =
      Set.univ.pi (fun _ : I => Ioc 0 b) := by
  ext x
  simp only [Set.mem_preimage, gridBox, Set.mem_univ_pi, Pi.add_apply, mem_Ioc]
  apply forall_congr'
  intro i
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gridBox_integral_eq_cube (b : ℝ) (k : I → ℤ) (f : (I → ℝ) → ℝ) :
    (∫ x in gridBox b k, f x) =
      ∫ x, f (x + (fun i => b*(k i : ℝ))) ∂(finiteCubeMeasure b I) := by
  have mp := (measurePreserving_add_right (volume : Measure (I → ℝ))
    (fun i => b*(k i : ℝ))).restrict_preimage (gridBox_measurable b k)
  rw [gridBox_preimage_add, ← finiteCubeMeasure_eq_restrict] at mp
  exact (mp.integral_comp (MeasurableEquiv.addRight _).measurableEmbedding f).symm

lemma gridBox_hasSum_integral {b : ℝ} (hb : 0 < b) {f : (I → ℝ) → ℝ}
    (hf : Integrable f) :
    HasSum (fun k : I → ℤ => ∫ x, f (x+(fun i => b*(k i : ℝ)))
      ∂(finiteCubeMeasure b I)) (∫ x, f x) := by
  have H := hasSum_integral_iUnion (gridBox_measurable b) (gridBox_disjoint hb)
    (hf.integrableOn (s := ⋃ k : I → ℤ, gridBox b k))
  simp_rw [gridBox_integral_eq_cube] at H
  simpa only [gridBox_iUnion hb, Measure.restrict_univ] using H

end GridTiling

lemma sum_fiber_card {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) :
    (∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ)) = n := by
  have H : (∑ k : ι, Fintype.card {i : Fin n // g i = k}) = n := by
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv g),
      Fintype.card_fin]
  exact_mod_cast H

lemma sum_power_le_power_sum {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, w i ^ p) ≤ (∑ i, w i) ^ p := by
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have he (x : ℝ) (hx : 0 ≤ x) : x^p = x*x^(p-1) := by
    conv_lhs => rw [show p = 1+(p-1) by ring]
    rw [Real.rpow_add_of_nonneg hx (by norm_num) (by linarith), Real.rpow_one]
  simp_rw [he _ (hw _)]
  rw [he _ hs]
  calc
    _ ≤ ∑ i, w i * (∑ j, w j)^(p-1) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact Real.rpow_le_rpow (hw i)
        (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)) (by linarith)
    _ = _ := (Finset.sum_mul ..).symm

lemma sum_fiber_power_le {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) {p : ℝ} (hp : 1 ≤ p) :
    (∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ)^p) ≤ (n : ℝ)^p := by
  simpa only [sum_fiber_card] using
    sum_power_le_power_sum
      (fun k => (Fintype.card {i : Fin n // g i = k} : ℝ)) (fun _ => Nat.cast_nonneg _) hp

lemma thomasFermiCoefficient_pos : 0 < thomasFermiCoefficient := by
  unfold thomasFermiCoefficient
  positivity

lemma neumannBoundary_nonneg : 0 ≤ neumannBoundary := by
  unfold neumannBoundary
  positivity

noncomputable def groupLeadingCount {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : ℝ :=
  ∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ)

lemma groupLeadingCount_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : 0 ≤ groupLeadingCount g :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma groupLeadingCount_le {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : groupLeadingCount g ≤ (n : ℝ)^(5/3 : ℝ) :=
  sum_fiber_power_le g (by norm_num)

lemma groupNeumannLower_uniform {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (b : ℝ) :
    (b⁻¹)^2 * thomasFermiCoefficient * groupLeadingCount g -
      (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ) ≤
      groupNeumannLower g b := by
  unfold groupNeumannLower groupLeadingCount
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
  have H := sum_fiber_power_le g (p := (4/3 : ℝ)) (by norm_num)
  have hC : 0 ≤ ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary)) := by
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) neumannBoundary_nonneg)
  nlinarith [mul_le_mul_of_nonneg_left H hC]

abbrev GridAssignment (n : ℕ) := (Fin n × Fin 3) → ℤ

def gridCell {n : ℕ} (k : GridAssignment n) (i : Fin n) : Fin 3 → ℤ :=
  fun j => k (i,j)

noncomputable def gridLeadingCount {n : ℕ} (k : GridAssignment n) : ℝ :=
  groupLeadingCount (Set.rangeFactorization (gridCell k))

noncomputable def gridShift {n : ℕ} (b : ℝ) (k : GridAssignment n) : Configuration n :=
  WithLp.toLp 2 (fun ij => b*(k ij : ℝ))

lemma grid_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (k : GridAssignment n) :
    ((b⁻¹)^2 * thomasFermiCoefficient * gridLeadingCount k -
      (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) *
      cubeMass (ψ.translate (gridShift b k)) b ≤
      cubeKinetic (ψ.translate (gridShift b k)) b := by
  let g := Set.rangeFactorization (gridCell k)
  let center : Set.range (gridCell k) → Space := fun u =>
    WithLp.toLp 2 (fun j => b*(u.val j : ℝ))
  have hm : 0 ≤ cubeMass (ψ.translate (gridShift b k)) b :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right (groupNeumannLower_uniform g b) hm).trans
    (assigned_cube_kinetic_lower hn ψ hψ g center hb)

lemma gridShift_hasSum_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    {f : Configuration n → ℝ} (hf : Integrable f) :
    HasSum (fun k : GridAssignment n =>
        ∫ x, f (WithLp.toLp 2 x + gridShift b k)
          ∂(finiteCubeMeasure b (Fin n × Fin 3))) (∫ x, f x) := by
  have H := gridBox_hasSum_integral hb
    ((PiLp.volume_preserving_toLp (Fin n × Fin 3)).integrable_comp_of_integrable hf)
  have he := (PiLp.volume_preserving_toLp (Fin n × Fin 3)).integral_comp
    ((PiLp.homeomorph 2 (fun _ : Fin n × Fin 3 => ℝ)).symm.measurableEmbedding) f
  simpa only [Function.comp_apply, WithLp.toLp_add, gridShift, he] using H

lemma grid_hasSum_mass {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    HasSum (fun k : GridAssignment n => cubeMass (ψ.translate (gridShift b k)) b)
      (mass ψ) := by
  unfold cubeMass mass
  exact hasSum_sum (fun s _ => gridShift_hasSum_integral hb
    ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide)))

lemma grid_hasSum_kinetic {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    HasSum (fun k : GridAssignment n => cubeKinetic (ψ.translate (gridShift b k)) b)
      (kinetic ψ) := by
  unfold cubeKinetic kinetic
  exact (hasSum_sum (fun s _ => hasSum_sum (fun i _ => gridShift_hasSum_integral hb
    ((ψ.partial_L2 s i).integrable_norm_pow (p := 2) (by decide))))).mul_left (1/2 : ℝ)

end Coulomb

end

end OAI
