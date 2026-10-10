import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FermionicCoefficients

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

theorem measurePreserving_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Type*} [MeasurableSpace A] (μ : ι → κ → Measure A)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm
      (Measure.pi fun i => Measure.pi (μ i))
      (Measure.pi fun ij : ι × κ => μ ij.1 ij.2) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product Finset.univ Finset.univ (fun ij : ι × κ => μ ij.1 ij.2 (s ij))).symm

noncomputable def configurationMeasurableEquiv (n : ℕ) :
    Configuration n ≃ᵐ (Fin n → Space) :=
  ((MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)).symm.trans
    (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ)).trans
    (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem configurationMeasurableEquiv_apply (n : ℕ) (x : Configuration n) (i : Fin n) :
    configurationMeasurableEquiv n x i = position x i := rfl

theorem configurationMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (configurationMeasurableEquiv n) volume volume := by
  apply MeasurePreserving.trans
    (MeasurePreserving.trans (PiLp.volume_preserving_ofLp (Fin n × Fin 3))
      (measurePreserving_uncurry (fun (_ : Fin n) (_ : Fin 3) =>
         (volume : Measure ℝ))).symm)
  exact volume_preserving_pi (fun _ => PiLp.volume_preserving_toLp (Fin 3))

theorem tensorOrbital_memLp {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) (s : Spins n) :
    MemLp (tensorOrbital v b s) 2 volume := by
  have hm : AEStronglyMeasurable (fun x : Fin n → Space => ∏ i, v (b i) (x i) (s i))
      volume := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hv (b i) (s i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Space)) i)
  have hi : Integrable (fun x : Fin n → Space => ∏ i, ‖v (b i) (x i) (s i)‖ ^ 2) volume :=
    Integrable.fintype_prod (fun i => (hv (b i) (s i)).norm.integrable_sq)
  have hl : MemLp (fun x : Fin n → Space => ∏ i, v (b i) (x i) (s i)) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_prod, ← Finset.prod_pow] using hi
  exact hl.comp_measurePreserving (configurationMeasurableEquiv_measurePreserving n)

theorem tensorOrbital_inner_integral {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b c : Fin n → α) :
    (∑ s : Spins n, ∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  classical
  have hi : ∀ s : Spins n,
      (∫ x, star (tensorOrbital v b s x) * tensorOrbital v c s x) =
      ∏ i, ∫ y, star (v (b i) y (s i)) * v (c i) y (s i) := by
    intro s
    calc
      _ = ∫ x : Fin n → Space, ∏ i, star (v (b i) (x i) (s i)) * v (c i) (x i) (s i) := by
        rw [← (configurationMeasurableEquiv_measurePreserving n).integral_comp']
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [tensorOrbital, star_prod, Finset.prod_mul_distrib,
            configurationMeasurableEquiv_apply]
      _ = _ := integral_fintype_prod_volume_eq_prod
        (fun i (y : Space) => star (v (b i) y (s i)) * v (c i) y (s i))
  simp_rw [hi]
  exact (Fintype.prod_sum fun i (t : Fin 2) => ∫ y, star (v (b i) y t) * v (c i) y t).symm

abbrev StateHilbert (n : ℕ) := PiLp 2 (fun _ : Spins n => Lp ℂ 2 (volume : Measure (Configuration n)))

noncomputable def H1Vector.toHilbert {n : ℕ} (ψ : H1Vector n) : StateHilbert n :=
  WithLp.toLp 2 (fun s => (ψ.value_L2 s).toLp (ψ.value s))

noncomputable def tensorHilbert {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) : StateHilbert n :=
  WithLp.toLp 2 (fun s => (tensorOrbital_memLp v hv b s).toLp (tensorOrbital v b s))

lemma inner_toLp_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, star (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma norm_toLp_sq_complex {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (↑(‖hf.toLp f‖ ^ 2) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∫ x, star (f x) * f x ∂μ := inner_toLp_complex hf hf
    _ = ∫ x, (↑(‖f x‖ ^ 2) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [mul_comm, Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f x)

lemma H1Vector.toHilbert_norm_sq {n : ℕ} (ψ : H1Vector n) :
    ‖ψ.toHilbert‖ ^ 2 = mass ψ := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun s _ => norm_toLp_sq_complex (ψ.value_L2 s)

lemma tensorHilbert_inner {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b c : Fin n → α) :
    inner ℂ (tensorHilbert v hv b) (tensorHilbert v hv c) =
      ∏ i, ∑ t : Fin 2, ∫ y, star (v (b i) y t) * v (c i) y t := by
  rw [PiLp.inner_apply]
  simp only [tensorHilbert, WithLp.ofLp_toLp, inner_toLp_complex]
  exact tensorOrbital_inner_integral v b c

lemma tensorHilbert_orthonormal {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t) * v c y t) =
      if a = c then (1 : ℂ) else 0) :
    Orthonormal ℂ (tensorHilbert (n := n) v hv) := by
  classical
  rw [orthonormal_iff_ite]
  intro b c
  rw [tensorHilbert_inner]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    have hi : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hi]

lemma orbitalCoefficient_eq_inner {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (b : Fin n → α) :
    orbitalCoefficient ψ v b = inner ℂ (tensorHilbert v hv b) ψ.toHilbert := by
  rw [PiLp.inner_apply]
  simp only [tensorHilbert, H1Vector.toHilbert, WithLp.ofLp_toLp, inner_toLp_complex,
    orbitalCoefficient]

theorem orbitalCoefficient_summable_and_bound {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t) * v c y t) =
      if a = c then (1 : ℂ) else 0) :
    Summable (fun b : Fin n → α => ‖orbitalCoefficient ψ v b‖ ^ 2) ∧
      (∑' b : Fin n → α, ‖orbitalCoefficient ψ v b‖ ^ 2) ≤ mass ψ := by
  have ht := tensorHilbert_orthonormal (n := n) v hv ho
  simp_rw [orbitalCoefficient_eq_inner ψ v hv]
  exact ⟨ht.inner_products_summable ψ.toHilbert,
    (ht.tsum_inner_products_le ψ.toHilbert).trans_eq ψ.toHilbert_norm_sq⟩

theorem orbitalCoefficient_pauli {n : ℕ} {α : Type*} (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, MemLp (fun x => v a x s) 2 volume)
    (ho : ∀ a c, (∑ t : Fin 2, ∫ y, star (v a y t) * v c y t) =
      if a = c then (1 : ℂ) else 0) (a : α) (i : Fin n) :
    (n : ℝ) * (∑' b : Fin n → α,
      if b i = a then ‖orbitalCoefficient ψ v b‖ ^ 2 else (0 : ℝ)) ≤ mass ψ := by
  have hf : FermionicCoefficients (orbitalCoefficient ψ v) :=
    fun p b => orbitalCoefficient_antisymmetric hψ v p b
  obtain ⟨hs, hb⟩ := orbitalCoefficient_summable_and_bound ψ v hv ho
  simpa using (hf.pauli_bound hs a i).trans hb

section FiberContraction
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma memLp_fiber_ae {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    ∀ᵐ b ∂ν, MemLp (fun a => f (b, a)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.norm.integrable_sq.prod_right_ae]
    with b hb hbi
  exact (memLp_two_iff_integrable_sq_norm hb).2 hbi

omit [SigmaFinite μ] in
lemma integralInner_sq_le {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ a, star (f a) * g a ∂μ‖ ^ 2 ≤
      (∫ a, ‖f a‖ ^ 2 ∂μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) := by
  rw [← inner_toLp_complex hf hg, ← norm_toLp_sq_complex hf, ← norm_toLp_sq_complex hg,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

noncomputable def fiberContract (v : A → ℂ) (f : B × A → ℂ) (b : B) : ℂ :=
  ∫ a, star (v a) * f (b, a) ∂μ

lemma fiberContract_memLp {v : A → ℂ} {f : B × A → ℂ}
    (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (fiberContract (μ := μ) v f) 2 ν := by
  have hm : AEStronglyMeasurable (fiberContract (μ := μ) v f) ν :=
    (hv.aestronglyMeasurable.star.comp_snd.mul hf.aestronglyMeasurable).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).2
  apply Integrable.mono' ((hf.norm.integrable_sq.integral_prod_left).const_mul
    (∫ a, ‖v a‖ ^ 2 ∂μ)) (hm.norm.pow 2)
  filter_upwards [memLp_fiber_ae hf] with b hb
  simpa only [fiberContract, Pi.pow_apply, Real.norm_eq_abs, abs_sq] using integralInner_sq_le hv hb

lemma fiberContract_norm_sq_le {v : A → ℂ} {f : B × A → ℂ}
    (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    (∫ b, ‖fiberContract (μ := μ) v f b‖ ^ 2 ∂ν) ≤
      (∫ a, ‖v a‖ ^ 2 ∂μ) * (∫ z, ‖f z‖ ^ 2 ∂(ν.prod μ)) := by
  rw [integral_prod _ hf.norm.integrable_sq, ← integral_const_mul]
  apply integral_mono_ae (fiberContract_memLp hv hf).norm.integrable_sq
    (hf.norm.integrable_sq.integral_prod_left.const_mul _)
  filter_upwards [memLp_fiber_ae hf] with b hb
  exact integralInner_sq_le hv hb

omit [SigmaFinite μ] [SigmaFinite ν] in

lemma tensorPair_memLp [SFinite μ] {w : B → ℂ} {v : A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) :
    MemLp (fun z : B × A => w z.1 * v z.2) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hw.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hw.norm.integrable_sq.mul_prod hv.norm.integrable_sq

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma integrable_star_mul {F : Type*} [MeasurableSpace F] {η : Measure F}
    {f g : F → ℂ} (hf : MemLp f 2 η) (hg : MemLp g 2 η) :
    Integrable (fun x => star (f x) * g x) η := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

lemma integral_tensorPair {w : B → ℂ} {v : A → ℂ} {f : B × A → ℂ}
    (hw : MemLp w 2 ν) (hv : MemLp v 2 μ) (hf : MemLp f 2 (ν.prod μ)) :
    (∫ z, star (w z.1 * v z.2) * f z ∂(ν.prod μ)) =
      ∫ b, star (w b) * fiberContract (μ := μ) v f b ∂ν := by
  rw [integral_prod _ (integrable_star_mul (tensorPair_memLp hw hv) hf)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    dsimp only [fiberContract]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      simp only [star_mul]
      ring

end FiberContraction

def CompleteOrbitals {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) : Prop :=
  ∀ f : A → ℂ, MemLp f 2 μ → (∀ i, (∫ a, star (v i a) * f a ∂μ) = 0) → f =ᵐ[μ] 0

section CompleteProducts
variable {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    [Countable ι]

theorem completeOrbitals_tensorPair {v : ι → A → ℂ} {w : κ → B → ℂ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hw : ∀ j, MemLp (w j) 2 ν)
    (hc : CompleteOrbitals μ v) (hd : CompleteOrbitals ν w) :
    CompleteOrbitals (ν.prod μ) (fun ij : κ × ι => fun z => w ij.1 z.1 * v ij.2 z.2) := by
  intro f hf hz
  have hzero : ∀ i, fiberContract (μ := μ) (v i) f =ᵐ[ν] 0 := by
    intro i
    apply hd _ (fiberContract_memLp (hv i) hf)
    intro j
    rw [← integral_tensorPair (hw j) (hv i) hf]
    exact hz (j, i)
  have hslice : ∀ᵐ b ∂ν, (fun a => f (b, a)) =ᵐ[μ] 0 := by
    filter_upwards [memLp_fiber_ae hf, ae_all_iff.mpr hzero] with b hb hbi
    apply hc _ hb
    exact hbi
  have hi : (∫ z, ‖f z‖ ^ 2 ∂(ν.prod μ)) = 0 := by
    rw [integral_prod _ hf.norm.integrable_sq]
    apply integral_eq_zero_of_ae
    filter_upwards [hslice] with b hb
    apply integral_eq_zero_of_ae
    filter_upwards [hb] with a ha
    simp [ha]
  have hz' := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖)
    hf.norm.integrable_sq).1 hi
  filter_upwards [hz'] with z h
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using h

end CompleteProducts

theorem HilbertBasis_completeOrbitals {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} (v : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    CompleteOrbitals μ (fun i => v i) := by
  intro f hf hz
  have he : v.repr (hf.toLp f) = 0 := by
    apply lp.ext
    funext i
    rw [v.repr_apply_apply]
    change inner ℂ (v i) (hf.toLp f) = 0
    have hi := inner_toLp_complex (Lp.memLp (v i)) hf
    simp only [Lp.toLp_coeFn] at hi
    rw [hi, hz i]
  have hf0 : hf.toLp f = 0 := v.repr.injective (by simpa using he)
  exact hf.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).1 hf0)

theorem CompleteOrbitals.comp {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {v : ι → A → ℂ}
    (hc : CompleteOrbitals μ v) (e : B ≃ᵐ A) (he : MeasurePreserving e ν μ) :
    CompleteOrbitals ν (fun i b => v i (e b)) := by
  intro f hf hz
  have hs := hc (f ∘ e.symm) (hf.comp_measurePreserving (he.symm e)) (by
    intro i
    dsimp only [Function.comp_apply]
    rw [← he.integral_comp' (fun a => star (v i a) * f (e.symm a))]
    simpa using hz i)
  filter_upwards [he.quasiMeasurePreserving.ae hs] with b hb
  simpa using hb

lemma scalarTensor_memLp {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (b : Fin n → ι) :
    MemLp (fun x : Fin n → A => ∏ i, v (b i) (x i)) 2 (Measure.pi fun _ => μ) := by
  have hm : AEStronglyMeasurable (fun x : Fin n → A => ∏ i, v (b i) (x i))
      (Measure.pi fun _ => μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hv (b i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i => (hv (b i)).norm.integrable_sq)

theorem completeOrbitals_finPi {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] [Countable ι] (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hc : CompleteOrbitals μ v) (n : ℕ) :
    CompleteOrbitals (Measure.pi fun _ : Fin n => μ)
      (fun b : Fin n → ι => fun x => ∏ i, v (b i) (x i)) := by
  induction n with
  | zero =>
    intro f hf hz
    have h := hz (fun i => Fin.elim0 i)
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    have hcp : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) =
        f (fun i => Fin.elim0 i) := by
      rw [he]
      simp [Measure.real, Measure.pi_empty_univ]
    have hh : (∫ x, f x ∂(Measure.pi fun _ : Fin 0 => μ)) = 0 := by
      simpa only [Fin.prod_univ_zero, star_one, one_mul] using h
    rw [hcp] at hh
    filter_upwards with x
    have hx : x = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [hx, Pi.zero_apply] using hh
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0
    have hp : MeasurePreserving e (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have ht := (completeOrbitals_tensorPair
      (fun (b : Fin n → ι) => scalarTensor_memLp v hv b) hv ih hc).comp e hp
    intro f hf hz
    apply ht f hf
    intro ib
    have hz' := hz (Fin.insertNth 0 ib.1 ib.2)
    convert hz' using 1
    congr 1
    funext x
    dsimp only
    congr 1
    rw [Fin.prod_univ_succAbove _ 0]
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.tail]

theorem orthonormal_subtype_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [SecondCountableTopology E] {s : Set E}
    (hs : Orthonormal ℂ (Subtype.val : s → E)) : Countable s := by
  have : DiscreteTopology s := DiscreteTopology.of_forall_le_dist (r := 1) (by norm_num) (by
    intro x y hxy
    have he : ‖(x : E) - y‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hs.1 x, hs.1 y, hs.inner_eq_zero hxy]
      norm_num
    change 1 ≤ dist (x : E) (y : E)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((x : E) - y)])
  exact countable_of_Lindelof_of_discrete

end Coulomb
end
end

end OAI
