import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.ConfigurationMeasurableEquiv

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

theorem exists_countable_spatial_basis :
    ∃ (s : Set (Lp ℂ 2 (volume : Measure Space))) (b : HilbertBasis s ℂ (Lp ℂ 2 volume)),
      Countable s ∧ ⇑b = Subtype.val := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure Space))
  refine ⟨s, b, ?_, hb⟩
  apply orthonormal_subtype_countable
  simpa only [hb] using b.orthonormal

theorem hilbertBasis_parseval {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : HilbertBasis ι ℂ E) (f : E) :
    (∑' i, ‖inner ℂ (b i) f‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (b.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h.symm

noncomputable def orbitalHilbertBasis {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) : HilbertBasis ι ℂ (Lp ℂ 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i => (hv i).toLp (v i))
    (by rw [orthonormal_iff_ite]; intro i j; rw [inner_toLp_complex]; exact ho i j)
    (by
      apply (Submodule.eq_bot_iff _).mpr
      intro f hf
      apply Lp.eq_zero_iff_ae_eq_zero.mpr
      apply hc f (Lp.memLp f)
      intro i
      have he := (Submodule.mem_orthogonal _ _).1 hf ((hv i).toLp (v i))
        (Submodule.subset_span (Set.mem_range_self i))
      have hi := inner_toLp_complex (hv i) (Lp.memLp f)
      simp only [Lp.toLp_coeFn] at hi
      rwa [hi] at he)

lemma orbitalHilbertBasis_apply {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (i : ι) :
    orbitalHilbertBasis v hv ho hc i = (hv i).toLp (v i) := by
  simp only [orbitalHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem completeOrbitals_parseval {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (f : A → ℂ) (hf : MemLp f 2 μ) :
    (∑' i, ‖∫ a, star (v i a) * f a ∂μ‖ ^ 2) = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have h := hilbertBasis_parseval (orbitalHilbertBasis v hv ho hc) (hf.toLp f)
  simpa only [orbitalHilbertBasis_apply, inner_toLp_complex, norm_toLp_sq_complex] using h

noncomputable def spinOrbital {ι : Type*} (v : ι → Space → ℂ)
    (is : ι × Fin 2) (x : Space) (s : Fin 2) : ℂ := if s = is.2 then v is.1 x else 0

lemma spinOrbital_memLp {ι : Type*} (v : ι → Space → ℂ)
    (hv : ∀ i, MemLp (v i) 2 volume) (is : ι × Fin 2) (s : Fin 2) :
    MemLp (fun x => spinOrbital v is x s) 2 volume := by
  by_cases h : s = is.2
  · simpa only [spinOrbital, ite_eq_left h] using hv is.1
  · simpa only [spinOrbital, ite_eq_right h] using (MemLp.zero' (μ := (volume : Measure Space)) (p := 2) (ε := ℂ))

lemma tensorSpinOrbital_apply {ι : Type*} {n : ℕ} (v : ι → Space → ℂ)
    (b : Fin n → ι) (s t : Spins n) (x : Configuration n) :
    tensorOrbital (spinOrbital v) (fun i => (b i, s i)) t x =
      if t = s then (∏ i, v (b i) (position x i)) else 0 := by
  by_cases h : t = s
  · subst t
    simp only [tensorOrbital, spinOrbital, ite_eq_left]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ s i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma spinOrbital_orthonormal {ι : Type*} (v : ι → Space → ℂ)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x) = if i = j then (1 : ℂ) else 0) :
    ∀ i j : ι × Fin 2, (∑ s, ∫ x, star (spinOrbital v i x s) * spinOrbital v j x s) =
      if i = j then (1 : ℂ) else 0 := by
  intro i j
  by_cases ht : i.2 = j.2
  · have hm : ∀ s x, star (spinOrbital v i x s) * spinOrbital v j x s =
        if s = i.2 then star (v i.1 x) * v j.1 x else 0 := by
      intro s x
      by_cases hs : s = i.2 <;> simp [spinOrbital, ← ht, hs]
    simp_rw [hm]
    have hi : ∀ s : Fin 2, (∫ x, if s = i.2 then star (v i.1 x) * v j.1 x else 0) =
        if s = i.2 then (∫ x, star (v i.1 x) * v j.1 x) else 0 := by
      intro s
      split_ifs <;> simp
    simp_rw [hi]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ho]
    congr 1
    exact propext ⟨fun h => Prod.ext h ht, fun h => congrArg Prod.fst h⟩
  · have he : i ≠ j := fun h => ht (congrArg Prod.snd h)
    rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hi : s = i.2
    · have hj : s ≠ j.2 := by rwa [hi]
      simp only [spinOrbital, ite_eq_left hi, ite_eq_right hj, mul_zero, integral_zero]
    · simp only [spinOrbital, ite_eq_right hi, star_zero, zero_mul, integral_zero]

lemma tensorSpinHilbert_inner {ι : Type*} {n : ℕ} (v : ι → Space → ℂ)
    (hv : ∀ i, MemLp (v i) 2 volume) (b : Fin n → ι) (s : Spins n)
    (f : StateHilbert n) :
    inner ℂ (tensorHilbert (spinOrbital v) (spinOrbital_memLp v hv)
      (fun i => (b i, s i))) f =
      ∫ x, star (∏ i, v (b i) (position x i)) * (f s : Configuration n → ℂ) x := by
  rw [PiLp.inner_apply]
  have hi : ∀ t : Spins n,
      inner ℂ ((tensorHilbert (spinOrbital v) (spinOrbital_memLp v hv)
        (fun i => (b i, s i))) t) (f t) =
      if t = s then (∫ x, star (∏ i, v (b i) (position x i)) *
        (f s : Configuration n → ℂ) x) else 0 := by
    intro t
    have he := inner_toLp_complex
      (tensorOrbital_memLp (spinOrbital v) (spinOrbital_memLp v hv)
        (fun i => (b i, s i)) t) (Lp.memLp (f t))
    simp only [Lp.toLp_coeFn] at he
    simp only [tensorHilbert, WithLp.ofLp_toLp]
    rw [he]
    simp_rw [tensorSpinOrbital_apply]
    split_ifs with ht
    · subst t; rfl
    · simp
  simp_rw [hi]
  simp

theorem tensorSpinHilbert_orthogonal_eq_bot {ι : Type*} [Countable ι] {n : ℕ}
    (v : ι → Space → ℂ) (hv : ∀ i, MemLp (v i) 2 volume)
    (hc : CompleteOrbitals volume v) :
    (Submodule.span ℂ (Set.range
      (tensorHilbert (n := n) (spinOrbital v) (spinOrbital_memLp v hv))))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hcc := (completeOrbitals_finPi v hv hc n).comp
    (configurationMeasurableEquiv n) (configurationMeasurableEquiv_measurePreserving n)
  apply PiLp.ext
  intro s
  change f s = (0 : Lp ℂ 2 (volume : Measure (Configuration n)))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply hcc (f s) (Lp.memLp (f s))
  intro b
  have he := (Submodule.mem_orthogonal _ _).1 hf
    (tensorHilbert (spinOrbital v) (spinOrbital_memLp v hv) (fun i => (b i, s i)))
    (Submodule.subset_span (Set.mem_range_self _))
  rw [tensorSpinHilbert_inner v hv] at he
  exact he

noncomputable def tensorSpinHilbertBasis {ι : Type*} [Countable ι] {n : ℕ}
    (v : ι → Space → ℂ) (hv : ∀ i, MemLp (v i) 2 volume)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals volume v) : HilbertBasis (Fin n → ι × Fin 2) ℂ (StateHilbert n) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (tensorHilbert_orthonormal _ _ (by
      intro i j
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using spinOrbital_orthonormal v ho i j
      · simpa only [ite_eq_right hij] using spinOrbital_orthonormal v ho i j))
    (tensorSpinHilbert_orthogonal_eq_bot v hv hc)

lemma tensorSpinHilbertBasis_apply {ι : Type*} [Countable ι] {n : ℕ}
    (v : ι → Space → ℂ) (hv : ∀ i, MemLp (v i) 2 volume)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals volume v) (b : Fin n → ι × Fin 2) :
    tensorSpinHilbertBasis v hv ho hc b =
      tensorHilbert (spinOrbital v) (spinOrbital_memLp v hv) b := by
  simp only [tensorSpinHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem orbitalCoefficient_spin_parseval {ι : Type*} [Countable ι] {n : ℕ}
    (ψ : H1Vector n) (v : ι → Space → ℂ) (hv : ∀ i, MemLp (v i) 2 volume)
    (ho : ∀ i j, (∫ x, star (v i x) * v j x) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals volume v) :
    (∑' b : Fin n → ι × Fin 2, ‖orbitalCoefficient ψ (spinOrbital v) b‖ ^ 2) = mass ψ := by
  have h := hilbertBasis_parseval (tensorSpinHilbertBasis (n := n) v hv ho hc) ψ.toHilbert
  simpa only [tensorSpinHilbertBasis_apply, ← orbitalCoefficient_eq_inner,
    H1Vector.toHilbert_norm_sq] using h

lemma fin_strictMono_nat_le {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have h : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hi := ih hk'
      have hj := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k+1, hk⟩ from Nat.lt_succ_self k)
      omega
  exact h i.val i.isLt

theorem levels_sum_le {n : ℕ} (levels : ℕ → ℝ) (hlevels : Monotone levels)
    (b : Fin n → ℕ) (hb : Function.Injective b) :
    (∑ k ∈ Finset.range n, levels k) ≤ ∑ i, levels (b i) := by
  classical
  let s : Finset ℕ := Finset.univ.image b
  have hs : s.card = n := by simp only [s, Finset.card_image_of_injective _ hb, Finset.card_univ, Fintype.card_fin]
  let e := s.orderEmbOfFin hs
  have he : ∑ i, levels (e i) = ∑ a ∈ s, levels a := by
    calc
      _ = ∑ a ∈ Finset.univ.image e, levels a := (Finset.sum_image e.injective.injOn).symm
      _ = _ := by rw [Finset.image_orderEmbOfFin_univ]
  calc
    _ = ∑ i : Fin n, levels i.val := Finset.sum_range levels
    _ ≤ ∑ i : Fin n, levels (e i) := Finset.sum_le_sum fun i _ =>
      hlevels (fin_strictMono_nat_le e e.strictMono i)
    _ = ∑ a ∈ s, levels a := he
    _ = ∑ i, levels (b i) := Finset.sum_image hb.injOn

theorem FermionicCoefficients.levels_lower {n : ℕ} {f : (Fin n → ℕ) → ℂ}
    (hf : FermionicCoefficients f) (hs : Summable (fun b => ‖f b‖^2))
    (levels : ℕ → ℝ) (hlevels : Monotone levels)
    (he : Summable (fun b => (∑ i, levels (b i)) * ‖f b‖^2)) :
    (∑ k ∈ Finset.range n, levels k) * (∑' b, ‖f b‖^2) ≤
      ∑' b, (∑ i, levels (b i)) * ‖f b‖^2 := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hs.mul_left _) he
  intro b
  by_cases hz : f b = 0
  · simp [hz]
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    exact hz (hf.vanish_of_repeat hne hij)
  exact mul_le_mul_of_nonneg_right (levels_sum_le levels hlevels b hb) (sq_nonneg _)

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma measurePreserving_permutePi {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → A => x ∘ p)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  have he : (MeasurableEquiv.piCongrLeft (fun _ => A) p.symm :
      (Fin n → A) → (Fin n → A)) = fun x => x ∘ p := by
    funext x i
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => A) p.symm x (p i))
  simpa only [he] using measurePreserving_piCongrLeft (fun _ : Fin n => μ) p.symm

lemma scalarTensor_inner_integral {n : ℕ} (v : ι → A → ℂ) (b c : Fin n → ι) :
    (∫ x : Fin n → A, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = ∏ i, ∫ a, star (v (b i) a) * v (c i) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i a => star (v (b i) a) * v (c i) a)

lemma scalarTensor_orthonormal {n : ℕ} (v : ι → A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    ∀ b c : Fin n → ι, (∫ x, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = if b = c then (1 : ℂ) else 0 := by
  intro b c
  rw [scalarTensor_inner_integral]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

noncomputable def scalarCoefficient {n : ℕ} (f : (Fin n → A) → ℂ)
    (v : ι → A → ℂ) (b : Fin n → ι) : ℂ :=
  ∫ x, star (∏ i, v (b i) (x i)) * f x ∂(Measure.pi fun _ => μ)

def ProductAntisymmetric {n : ℕ} (f : (Fin n → A) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)), ∀ᵐ x ∂(Measure.pi fun _ => μ),
    f (x ∘ p) = ((p.sign : ℤ) : ℂ) * f x

lemma scalarCoefficient_antisymmetric {n : ℕ} {f : (Fin n → A) → ℂ}
    (hf : ProductAntisymmetric (μ := μ) f) (v : ι → A → ℂ) :
    FermionicCoefficients (scalarCoefficient (μ := μ) f v) := by
  intro p b
  unfold scalarCoefficient
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) p.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ => A) p.symm :
      (Fin n → A) → (Fin n → A)) = fun x => x ∘ p := by
    funext x i
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => A) p.symm x (p i))
  rw [← hp.integral_comp' (fun x => star (∏ i, v ((b ∘ p) i) (x i)) * f x), he,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hf p] with x hx
  simp only [Function.comp_apply, hx]
  rw [Equiv.prod_comp p (fun i => v (b i) (x i))]
  ring

theorem scalarCoefficient_parseval [Countable ι] {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) :
    (∑' b : Fin n → ι, ‖scalarCoefficient (μ := μ) f v b‖^2) =
      ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have ht := completeOrbitals_parseval (μ := Measure.pi fun _ : Fin n => μ)
    (fun (b : Fin n → ι) (x : Fin n → A) => ∏ i, v (b i) (x i))
    (scalarTensor_memLp v hv) (by
      intro b c
      have h := scalarTensor_orthonormal (μ := μ) v ho b c
      by_cases he : b = c <;> simpa only [he, ite_true, ite_false] using h)
    (completeOrbitals_finPi v hv hc n) f hf
  simpa only [scalarCoefficient] using ht

lemma scalarCoefficient_summable {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    Summable (fun b : Fin n → ι => ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  have ho' : Orthonormal ℂ (fun b : Fin n → ι =>
      (scalarTensor_memLp v hv b).toLp (fun x : Fin n → A => ∏ i, v (b i) (x i))) := by
    rw [orthonormal_iff_ite]
    intro b c
    rw [inner_toLp_complex]
    exact scalarTensor_orthonormal v ho b c
  have hs := ho'.inner_products_summable (hf.toLp f)
  simpa only [inner_toLp_complex, scalarCoefficient] using hs

theorem scalarCoefficient_levels_lower {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : ℕ → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (levels : ℕ → ℝ) (hl : Monotone levels)
    (he : Summable (fun b => (∑ i, levels (b i)) *
      ‖scalarCoefficient (μ := μ) f v b‖^2)) :
    (∑ k ∈ Finset.range n, levels k) * (∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ)) ≤
      ∑' b, (∑ i, levels (b i)) * ‖scalarCoefficient (μ := μ) f v b‖^2 := by
  have ho' : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) =
      if i = j then (1 : ℂ) else 0 := ho
  have hp := scalarCoefficient_parseval f hf v hv (by
    intro i j
    by_cases hij : i = j <;> simpa only [hij, ite_true, ite_false] using ho' i j) hc
  rw [← hp]
  exact (scalarCoefficient_antisymmetric ha v).levels_lower
    (scalarCoefficient_summable f hf v hv (by
    intro i j
    by_cases hij : i = j <;> simpa only [hij, ite_true, ite_false] using ho' i j)) levels hl he

end GeneralFermionSpace

noncomputable def cosineMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.cos ((n : ℝ) * Real.pi * x / b) : ℂ)

noncomputable def evenOnSegment (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Ioc 0 b).indicator f x + (Ioc 0 b).indicator f (-x)

lemma evenOnSegment_memLp {b : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) :
    MemLp (evenOnSegment b f) 2 volume := by
  have hg : MemLp ((Ioc 0 b).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc).2 hf
  exact hg.add (hg.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ)))

lemma evenOnSegment_pos {b x : ℝ} (f : ℝ → ℂ) (hx : x ∈ Ioc 0 b) :
    evenOnSegment b f x = f x := by
  have hn : -x ∉ Ioc 0 b := by rintro ⟨hh, _⟩; linarith [hx.1]
  simp only [evenOnSegment, indicator_of_mem hx, indicator_of_notMem hn, add_zero]

lemma evenOnSegment_eq_zero {b x : ℝ} (hb : 0 < b) (f : ℝ → ℂ)
    (hx : x ∉ Icc (-b) b) : evenOnSegment b f x = 0 := by
  have hp : x ∉ Ioc 0 b := by
    intro h
    exact hx ⟨by linarith [h.1], h.2⟩
  have hn : -x ∉ Ioc 0 b := by
    intro h
    exact hx ⟨by linarith [h.2], by linarith [h.1]⟩
  simp [evenOnSegment, hp, hn]

lemma evenOnSegment_neg (b : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    evenOnSegment b f (-x) = evenOnSegment b f x := by
  simp only [evenOnSegment, neg_neg, add_comm]

lemma fourierOn_ae_zero {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hz : ∀ n : ℤ, fourierCoeffOn hab f n = 0) :
    f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hp := tsum_sq_fourierCoeffOn hab hf
  simp only [hz, norm_zero, zero_pow (by omega : 2 ≠ 0), tsum_zero,
    smul_eq_mul, intervalIntegral.integral_of_le hab.le] at hp
  have hnorm : (∫ x in Ioc a b, ‖f x‖^2) = 0 := by
    exact (mul_eq_zero.mp hp.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr hab.ne'))
  have hz' := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖)
    hf.norm.integrable_sq).1 hnorm
  filter_upwards [hz'] with x hx
  simpa using hx

end Coulomb
end
end

end OAI
