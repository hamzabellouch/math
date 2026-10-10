import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SliceLp
import OAI.Analysis.CoulombIonization.Fermionic.CountableTests

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
section
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma smooth_test_product {φ : E → ℝ} {ψ : F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p : E × F => φ p.1 * ψ p.2) ∧
    HasCompactSupport (fun p : E × F => φ p.1 * ψ p.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd), ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (hcφ.prod hcψ)
  rintro ⟨x,y⟩ hxy
  exact ⟨subset_tsupport _ ((mul_ne_zero_iff.mp hxy).1),
    subset_tsupport _ ((mul_ne_zero_iff.mp hxy).2)⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma lineDeriv_test_product {φ : E → ℝ} {ψ : F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (v : E) (p : E × F) :
    lineDeriv ℝ (fun p : E × F => φ p.1 * ψ p.2) p (v,0) =
      lineDeriv ℝ φ p.1 v * ψ p.2 := by
  have h1 := (hφ.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 := (hψ.differentiable (by simp) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have hh := ((h1.mul h2).hasLineDerivAt (v,0)).lineDeriv
  have he : (φ ∘ Prod.fst * ψ ∘ Prod.snd) = (fun p : E × F => φ p.1 * ψ p.2) := rfl
  rw [he] at hh
  rw [(hφ.differentiable (by simp) p.1).lineDeriv_eq_fderiv]
  simpa [Function.comp_def, Pi.mul_apply, mul_comm] using hh

lemma weak_slice_fixed_test {v : E} {f g : E × F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) (hfg : IsWeakDerivative (v,0) f g)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    ∀ᵐ y, (∫ x, f (x,y) * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, g (x,y) * (φ x : ℂ)) := by
  have h1 := partial_pairing_memLp hf (fun x => lineDeriv ℝ φ x v)
    (test_deriv_memLp hφ hcφ v)
  have h2 := partial_pairing_memLp hg φ (test_memLp hφ hcφ)
  apply ae_eq_of_integral_contDiff_smul_eq
    (h1.locallyIntegrable (by norm_num)) ((h2.neg).locallyIntegrable (by norm_num))
  intro ψ hψ hcψ
  obtain ⟨ht, hct⟩ := smooth_test_product hφ hcφ hψ hcψ
  have hi1 := hf.integrable_mul (test_deriv_memLp ht hct (v,0))
  have hi2 := hg.integrable_mul (test_memLp ht hct)
  have he := hfg _ ht hct
  simp only [lineDeriv_test_product hφ hψ] at hi1 he
  have hp1 := integral_prod_symm _ hi1
  have hp2 := integral_prod_symm _ hi2
  simp only [Pi.mul_apply] at hp1 hp2
  rw [Measure.volume_eq_prod E F, hp1, hp2] at he
  simp only [Complex.ofReal_mul, ← mul_assoc, integral_mul_const] at he
  simp only [Complex.real_smul, Pi.neg_apply, mul_neg, integral_neg]
  simpa only [mul_comm] using he

theorem IsWeakDerivative.slice_left {v : E} {f g : E × F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) (hfg : IsWeakDerivative (v,0) f g) :
    ∀ᵐ y, IsWeakDerivative v (fun x => f (x,y)) (fun x => g (x,y)) := by
  obtain ⟨S, hS, htests⟩ := countable_weak_derivative_tests v
  have hall : ∀ᵐ y, ∀ φ ∈ S,
      (∫ x, f (x,y) * Complex.ofReal (lineDeriv ℝ φ.val x v)) =
        -(∫ x, g (x,y) * (φ.val x : ℂ)) := by
    apply (ae_ball_iff hS).mpr
    intro φ _
    exact weak_slice_fixed_test hf hg hfg φ.property.1 φ.property.2
  filter_upwards [memLp_slice_left hf, memLp_slice_left hg, hall] with y hyf hyg hy
  exact htests _ _ hyf hyg hy

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

section ChangeVariables
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace F] [BorelSpace F]

lemma IsWeakDerivative.pullback {v : F} {w : E} {f g : F → ℂ}
    (hw : IsWeakDerivative v f g) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e) (hv : e w = v) :
    IsWeakDerivative w (f ∘ e) (g ∘ e) := by
  intro φ hφ hcφ
  let ψ : F → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm.toHomeomorph
  have hev : e.symm v = w := by rw [← hv, e.symm_apply_apply]
  have hd (x : E) : lineDeriv ℝ ψ (e x) v = lineDeriv ℝ φ x w := by
    rw [(hψ.differentiable (by simp) (e x)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp
      (e x) e.symm.hasFDerivAt
    have hh' := congrArg (fun A : F →L[ℝ] ℝ => A v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply, hev] using hh'
  have hi1 := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => f x * Complex.ofReal (lineDeriv ℝ ψ x v))
  have hi2 := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => g x * (ψ x : ℂ))
  have hh := hw ψ hψ hcψ
  rw [← hi1, ← hi2] at hh
  simpa only [hd, ψ, Function.comp_apply, e.symm_apply_apply] using hh

end ChangeVariables

def joinLists {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) : Fin (N+M) → α :=
  Sum.elim x y ∘ finSumFinEquiv.symm

@[simp] lemma joinLists_left {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α)
    (i : Fin N) : joinLists x y (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [joinLists]

@[simp] lemma joinLists_right {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α)
    (i : Fin M) : joinLists x y (finSumFinEquiv (Sum.inr i)) = y i := by
  simp [joinLists]

def configurationJoin (N M : ℕ) :
    (Configuration N × Configuration M) ≃L[ℝ] Configuration (N+M) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin N) (Fin M) (fun _ => Space)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (N+M) => Space) finSumFinEquiv)

lemma configurationJoin_apply {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    configurationJoin N M (x,y) = joinLists x y := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (N+M) => Space) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Space)).symm (x,y))
      (finSumFinEquiv j) = Sum.elim x y (finSumFinEquiv.symm (finSumFinEquiv j))
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  cases j <;> rfl

lemma configurationJoin_preserving (N M : ℕ) : MeasurePreserving (configurationJoin N M) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (N+M) => Space) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin M => Space))

lemma configurationJoin_direction {N M : ℕ} (i : Fin N) (a : Fin 3) :
    configurationJoin N M (direction i a,0) = direction (finSumFinEquiv (Sum.inl i)) a := by
  rw [configurationJoin_apply]
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => rw [joinLists_left]; simp [direction, Pi.single_apply]
  | inr j =>
    rw [joinLists_right]
    have hn : finSumFinEquiv (Sum.inr j) ≠ finSumFinEquiv (Sum.inl i) :=
      fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
    simp only [direction, Pi.single_apply, ite_eq_right hn, Pi.zero_apply]

def corePerm {N : ℕ} (M : ℕ) (π : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N+M)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr π (Equiv.refl (Fin M)))

lemma corePerm_sign {N : ℕ} (M : ℕ) (π : Equiv.Perm (Fin N)) :
    Equiv.Perm.sign (corePerm M π) = Equiv.Perm.sign π := by
  simp [corePerm, Equiv.Perm.sign_sumCongr]

lemma joinLists_corePerm {α : Type*} {N M : ℕ}
    (x : Fin N → α) (y : Fin M → α) (π : Equiv.Perm (Fin N)) :
    joinLists x y ∘ corePerm M π = joinLists (x ∘ π) y := by
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp [joinLists, corePerm, Equiv.permCongr, Function.comp_def]

def coreSlice {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M) (y : Configuration M) :
    FormVector N where
  value s x := ψ.value (joinLists s t) (joinLists x y)
  gradient s i a x := ψ.gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a (joinLists x y)

def SobolevFermion {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a, IsWeakDerivative (direction i a) (ψ.value s) (ψ.gradient s i a)) ∧
  (∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
    ψ.value (s ∘ π) (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x))

lemma FormAdmissible.sobolevFermion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    SobolevFermion ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.1, hψ.2.2.2.1⟩

theorem SobolevFermion.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) :
    ∀ᵐ y, SobolevFermion (coreSlice ψ t y) := by
  have hv (s : Spins N) : ∀ᵐ y, MemLp ((coreSlice ψ t y).value s) 2 := by
    have hh := (hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hg (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, MemLp ((coreSlice ψ t y).gradient s i a) 2 := by
    have hh := (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
      (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hw (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, IsWeakDerivative (direction i a) ((coreSlice ψ t y).value s)
        ((coreSlice ψ t y).gradient s i a) := by
    have hh := (hψ.2.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).pullback
      (configurationJoin N M) (configurationJoin_preserving N M) (configurationJoin_direction i a)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using hh.slice_left
      ((hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M))
      ((hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
        (configurationJoin_preserving N M))
  have ha (π : Equiv.Perm (Fin N)) (s : Spins N) : ∀ᵐ y, ∀ᵐ x,
      (coreSlice ψ t y).value (s ∘ π) (x ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t y).value s x) := by
    have hh := (configurationJoin_preserving N M).quasiMeasurePreserving.ae
      (hψ.2.2.2 (corePerm M π) (joinLists s t))
    have hh' : ∀ᵐ z : Configuration N × Configuration M,
        (coreSlice ψ t z.2).value (s ∘ π) (z.1 ∘ π) =
          (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t z.2).value s z.1) := by
      filter_upwards [hh] with z hz
      rcases z with ⟨x,y⟩
      simpa only [configurationJoin_apply, joinLists_corePerm, corePerm_sign, coreSlice] using hz
    rw [Measure.volume_eq_prod] at hh'
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh')

  filter_upwards [ae_all_iff.mpr hv, ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hg s i))), ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hw s i))), ae_all_iff.mpr (fun π => ae_all_iff.mpr (ha π))]
    with y hyv hyg hyw hya
  exact ⟨hyv,hyg,hyw,hya⟩

def formMass {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2

lemma formMass_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formMass ψ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

def scaleForm {N : ℕ} (c : ℝ) (ψ : FormVector N) : FormVector N where
  value s x := (c : ℂ) * ψ.value s x
  gradient s i a x := (c : ℂ) * ψ.gradient s i a x

lemma SobolevFermion.scale {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (c : ℝ) : SobolevFermion (scaleForm c ψ) := by
  refine ⟨fun s => (hψ.1 s).const_mul _, fun s i a => (hψ.2.1 s i a).const_mul _, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    change (∫ x, ((c : ℂ) * ψ.value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
      -(∫ x, ((c : ℂ) * ψ.gradient s i a x) * (φ x : ℂ))
    simp only [mul_assoc, integral_const_mul, hψ.2.2.1 s i a φ hφ hcφ, mul_neg]
  · intro π s
    filter_upwards [hψ.2.2.2 π s] with x hx
    change (c : ℂ) * ψ.value (s ∘ π) (x ∘ π) = _
    rw [hx]
    change _ = (((Equiv.Perm.sign π : ℤ) : ℂ) * ((c : ℂ) * ψ.value s x))
    ring

lemma scaled_norm_sq (c : ℝ) (z : ℂ) : ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma formMass_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) :
    formMass (scaleForm c ψ) = c ^ 2 * formMass ψ := by
  simp only [formMass, scaleForm, scaled_norm_sq, integral_const_mul, Finset.mul_sum]

lemma formEnergy_scale {N : ℕ} (Z c : ℝ) (ψ : FormVector N) :
    formEnergy Z (scaleForm c ψ) = c ^ 2 * formEnergy Z ψ := by
  simp only [formEnergy, scaleForm, scaled_norm_sq, mul_div_assoc, integral_const_mul]
  have hi (s : Spins N) (i j : Fin N) :
      (if i < j then c ^ 2 * ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
        c ^ 2 * (if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) := by
    split_ifs <;> simp
  simp_rw [hi, ← Finset.mul_sum]
  ring

lemma SobolevFermion.admissible {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hn : formMass ψ = 1) : FormAdmissible ψ := by
  refine ⟨hψ.1,hψ.2.1,hψ.2.2.1,hψ.2.2.2,hn,?_,?_⟩
  · intro s i
    exact nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
  · intro s i j hij
    exact pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)

theorem SobolevFermion.normalize {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : 0 < formMass ψ) :
    FormAdmissible (scaleForm (Real.sqrt (formMass ψ))⁻¹ ψ) := by
  apply (hψ.scale _).admissible
  rw [formMass_scale, inv_pow, Real.sq_sqrt (le_of_lt hm), inv_mul_cancel₀ (ne_of_gt hm)]

lemma energy_le_form {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    {ψ : FormVector N} (hψ : FormAdmissible ψ) : energy Z N ≤ formEnergy Z ψ := by
  by_cases hN : N = 0
  · subst N
    simp [energy, formEnergy]
  · rw [energy, ite_eq_right hN]
    exact csInf_le ⟨-(N : ℝ) * Z ^ 2 / 2, by
      rintro e ⟨φ,hφ,rfl⟩
      exact formEnergy_lower_bound hZ hφ⟩ ⟨ψ,hψ,rfl⟩

lemma SobolevFermion.mass_zero_nuclear {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 0) (s : Spins N) (i : Fin N) :
    (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) = 0 := by
  have hs : (∫ x, ‖ψ.value s x‖ ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
      (Finset.mem_univ _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (hψ.1 s).norm.integrable_sq).mp hs
  calc
    _ = ∫ _x : Configuration N, (0 : ℝ) := integral_congr_ae (hae.mono fun x hx => by simp [hx])
    _ = 0 := integral_zero _ _

theorem SobolevFermion.energy_mul_mass_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z : ℝ} (hZ : 0 ≤ Z) :
    energy Z N * formMass ψ ≤ formEnergy Z ψ := by
  rcases (formMass_nonneg ψ).eq_or_lt with hm | hm
  · rw [← hm, mul_zero]
    have hn := hψ.mass_zero_nuclear hm.symm
    simp only [formEnergy, hn, Finset.sum_const_zero, mul_zero, sub_zero]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
    · apply Finset.sum_nonneg; intro s _
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      split_ifs
      · exact integral_nonneg fun _ => div_nonneg (sq_nonneg _) (norm_nonneg _)
      · rfl
  · have hh := energy_le_form hZ (hψ.normalize hm)
    rw [formEnergy_scale, inv_pow, Real.sq_sqrt (le_of_lt hm)] at hh
    have hs := mul_le_mul_of_nonneg_right hh (le_of_lt hm)
    have he : (formMass ψ)⁻¹ * formEnergy Z ψ * formMass ψ = formEnergy Z ψ := by
      field_simp
    rwa [he] at hs

theorem conditional_core_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) {Z : ℝ} (hZ : 0 ≤ Z) :
    ∀ᵐ y, energy Z N * formMass (coreSlice ψ t y) ≤ formEnergy Z (coreSlice ψ t y) :=
  (hψ.ae_coreSlice t).mono fun _ hy => hy.energy_mul_mass_le hZ


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
