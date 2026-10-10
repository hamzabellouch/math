import OAI.Geometry.LatticeCovering.Folded

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma law_real_of_subset {h : ℝ} (hh : 0 < h) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Icc (0 : ℝ) 1) :
    (law h).real s = (∫ t in s, density h t)/totalMass h := by
  calc
    _ = ∫ _ in s, (1 : ℝ) ∂law h := by simp
    _ = ∫ t in s, density h t/totalMass h ∂volume.restrict (Icc (0 : ℝ) 1) := by
      unfold law
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_weight h)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ => (1 : ℝ)) hs]
      simp only [ENNReal.toReal_ofReal (div_nonneg (density_pos hh _).le (totalMass_pos hh).le),
        smul_eq_mul, mul_one]
    _ = _ := by rw [Measure.restrict_restrict hs, inter_eq_left.mpr hsub, integral_div]


def centralInterval (h : ℝ) : Set ℝ := Icc (1/2-1/(2*h^2)) (1/2+1/(2*h^2))

lemma centralInterval_subset {h : ℝ} (hh : 1 ≤ h) : centralInterval h ⊆ Icc (0 : ℝ) 1 := by
  have hh2 : 1 ≤ h^2 := by nlinarith
  have hw : 1/(2*h^2) ≤ (1/2 : ℝ) := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)
  intro t ht
  rcases ht with ⟨hl,hu⟩
  constructor <;> linarith

lemma centralInterval_volume {h : ℝ} (hh : 0 < h) :
    volume.real (centralInterval h) = 1/h^2 := by
  unfold centralInterval
  rw [Real.volume_real_Icc]
  have hz : 0 ≤ (1/2+1/(2*h^2))-(1/2-1/(2*h^2)) := by
    have : 0 ≤ 1/(2*h^2) := by positivity
    linarith
  rw [max_eq_left hz]
  ring

lemma centralInterval_probability {h : ℝ} (hh : 1 ≤ h) :
    Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) ≤ (law h).real (centralInterval h) := by
  have hp : 0 < h := by linarith
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hmin : h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) * volume.real (centralInterval h) ≤
      ∫ t in centralInterval h, density h t := by
    calc
      _ = ∫ _ in centralInterval h, h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) := by simp [mul_comm]
      _ ≤ _ := by
        apply setIntegral_mono_on (integrableOn_const (s := centralInterval h) (hs := isCompact_Icc.measure_ne_top))
          (continuous_density h).integrableOn_Icc measurableSet_Icc
        intro t ht
        exact density_lower hp (centralInterval_subset hh ht)
  rw [centralInterval_volume hp] at hmin
  have he : h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8)*(1/h^2) =
      Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) := by field_simp
  rw [he] at hmin
  rw [law_real_of_subset (s := centralInterval h) hp measurableSet_Icc (centralInterval_subset hh)]
  exact hmin.trans ((le_div_iff₀ (totalMass_pos hp)).mpr
    (mul_le_of_le_one_right (le_trans (by positivity) hmin) (totalMass_le_one hp)))

variable {ι : Type*} [Fintype ι]

def cubeLaw (h : ℝ) : Measure (ι → ℝ) := Measure.pi (fun _ : ι => law h)

lemma log_folded {h : ℝ} (hh : 0 < h) (t : ι → ℝ) :
    Real.log (folded h t) = ∑ i, Real.log (density h (t i)) := by
  exact Real.log_prod (fun i _ => (density_pos hh (t i)).ne')

lemma folded_chebyshev {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | c ≤ |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h|} ≤
      (Fintype.card ι : ℝ)*((Real.log 2+h^2/8)/2)^2/c^2 := by
  let := law_isProbability hh
  have ht := Concentration.sum_chebyshev (ι := ι) (log_density_memLp hh)
    (log_density_variance hh) hc
  simp only [integral_log_density hh] at ht
  simpa only [cubeLaw, log_folded hh] using ht

lemma central_count_tail {h : ℝ} (hh : 1 ≤ h) (hi : 0 < Fintype.card ι)
    {r : ℝ} (hr : 2*r ≤ (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) :
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r} ≤
      4/((Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) := by
  have hp : 0 < h := by linarith
  let := law_isProbability hp
  have hl := mul_le_mul_of_nonneg_left (centralInterval_probability hh) (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  rw [←mul_div_assoc] at hl
  have hx : 0 < (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) := by positivity
  have ht := Concentration.count_lower_tail (ι := ι) (μ := law h) (s := centralInterval h) measurableSet_Icc (lt_of_lt_of_le hx hl)
  apply (measureReal_mono (show {t : ι → ℝ | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r} ⊆ _ from ?_)).trans
    (ht.trans (div_le_div_of_nonneg_left (by norm_num) hx hl))
  intro t ht
  dsimp at ht ⊢
  linarith




end SingleLatticeCovering.Folded
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace SingleLatticeCovering
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, SigmaFinite (μ i)]

lemma pi_withDensity_ofReal {f : ∀ i, Ω i → ℝ}
    (hf : ∀ i, Integrable (f i) (μ i)) (hpos : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [←ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i => (hf i).restrict))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hpos i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hpos i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (Filter.Eventually.of_forall (hpos i))


end SingleLatticeCovering

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real
variable {ι : Type*} [Fintype ι]

def cube : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

lemma continuous_folded (h : ℝ) : Continuous (folded h : (ι → ℝ) → ℝ) := by
  unfold folded
  exact continuous_finsetProd _ (fun i _ => (continuous_density h).comp (continuous_apply i))

lemma cubeLaw_density {h : ℝ} (hh : 0 < h) :
    (cubeLaw h : Measure (ι → ℝ)) =
      (volume.restrict cube).withDensity
        (fun t => ENNReal.ofReal (folded h t/(totalMass h)^Fintype.card ι)) := by
  have hf : Integrable (fun x => density h x/totalMass h) (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((continuous_density h).div_const _).integrableOn_Icc
  have ht := pi_withDensity_ofReal (μ := fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))
    (f := fun _ : ι => fun x => density h x/totalMass h) (fun _ => hf)
    (fun _ x => div_nonneg (density_pos hh x).le (totalMass_pos hh).le)
  simpa only [cubeLaw, law, ←Measure.restrict_pi_pi, volume_pi, cube,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, folded] using ht

lemma cube_integral {h : ℝ} (_ : 0 < h) :
    (∫ t in (cube : Set (ι → ℝ)), folded h t) = (totalMass h)^Fintype.card ι := by
  rw [cube, volume_pi, Measure.restrict_pi_pi]
  unfold folded
  rw [integral_fintype_prod_eq_pow, integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

lemma cubeLaw_real {h : ℝ} (hh : 0 < h) {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    (cubeLaw h).real s = (∫ t in s ∩ cube, folded h t)/(totalMass h)^Fintype.card ι := by
  calc
    _ = ∫ _ in s, (1 : ℝ) ∂cubeLaw h := by simp
    _ = ∫ t in s, folded h t/(totalMass h)^Fintype.card ι ∂volume.restrict cube := by
      rw [cubeLaw_density hh, setIntegral_withDensity_eq_setIntegral_toReal_smul
        (((continuous_folded h).div_const _).measurable.ennreal_ofReal)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ => (1 : ℝ)) hs]
      simp only [ENNReal.toReal_ofReal (div_nonneg (folded_pos hh _).le (pow_nonneg (totalMass_pos hh).le _)),
        smul_eq_mul, mul_one]
    _ = _ := by rw [Measure.restrict_restrict hs, integral_div]

lemma cubeLaw_isProbability {h : ℝ} (hh : 0 < h) : IsProbabilityMeasure (cubeLaw h : Measure (ι → ℝ)) := by
  let := law_isProbability hh
  change IsProbabilityMeasure (Measure.pi (fun _ : ι => law h))
  infer_instance


lemma continuous_good_mass {h c r : ℝ} (hh : 1 ≤ h) (hi : 0 < Fintype.card ι) (hc : 0 < c)
    (hr : 2*r ≤ (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) :
    1 - (Fintype.card ι : ℝ)*((Real.log 2+h^2/8)/2)^2/c^2 -
      4/((Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) ≤
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
        r ≤ ∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)} := by
  have hp : 0 < h := by linarith
  let := cubeLaw_isProbability (ι := ι) hp
  let A : Set (ι → ℝ) := {t | c ≤ |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h|}
  let B : Set (ι → ℝ) := {t | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r}
  have hA : MeasurableSet A := by
    apply measurableSet_le measurable_const
    exact (((continuous_folded h).log (fun t => (folded_pos hp t).ne')).sub continuous_const).abs.measurable
  have hB : MeasurableSet B := by
    apply measurableSet_lt _ measurable_const
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator (show MeasurableSet (centralInterval h) from measurableSet_Icc)).comp (measurable_pi_apply i))
  have he : {t : ι → ℝ | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
        r ≤ ∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)} = (A ∪ B)ᶜ := by
    ext t
    simp only [A, B, mem_ofPred_eq, mem_compl_iff, mem_union, not_or, not_le, not_lt]
  rw [he, measureReal_compl (hA.union hB)]
  have hu := measureReal_union_le (μ := cubeLaw h) A B
  have ha := folded_chebyshev (ι := ι) hp hc
  have hb := central_count_tail (ι := ι) hh hi hr
  change (cubeLaw h).real A ≤ _ at ha
  change (cubeLaw h).real B ≤ _ at hb
  have hu1 : (cubeLaw h : Measure (ι → ℝ)).real Set.univ = 1 := by simp
  rw [hu1]
  linarith



end SingleLatticeCovering.Folded



noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.ConstructionA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def generator (p : ℕ) (a : ι → ℤ) : ι → ℝ := fun j => (a j : ℝ) / p

def matrix (p : ℕ) (i : ι) (a : ι → ℤ) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ).updateRow i (generator p a)

lemma det_matrix (p : ℕ) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    (matrix p i a).det = (p : ℝ)⁻¹ := by
  have hs : (∑ j, (generator p a j) • (1 : Matrix ι ι ℝ) j) = generator p a := by
    ext k
    simp [Matrix.one_apply, Pi.smul_apply, smul_eq_mul]
  rw [matrix, ← hs, Matrix.det_updateRow_sum]
  simp [generator, ha]

lemma independent_matrix (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    LinearIndependent ℝ (matrix p i a) := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit (matrix p i a).det
  rw [det_matrix p i a ha]
  exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hp.ne'))

def basis (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    Basis ι ℝ (ι → ℝ) := by
  letI : Nonempty ι := ⟨i⟩
  exact Basis.mk (independent_matrix p hp i a ha)
    (by rw [(independent_matrix p hp i a ha).span_eq_top_of_card_eq_finrank
      (Module.finrank_pi ℝ).symm])

@[simp] lemma basis_apply (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (j : ι) : basis p hp i a ha j = matrix p i a j := by
  unfold basis
  exact Basis.mk_apply _ _ j

@[simp] lemma basis_pivot (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    basis p hp i a ha i = generator p a := by
  rw [basis_apply]
  exact Matrix.updateRow_self

lemma basis_other (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (j : ι) (hj : j ≠ i) : basis p hp i a ha j = (Pi.basisFun ℝ ι) j := by
  rw [basis_apply]
  change (1 : Matrix ι ι ℝ).updateRow i (generator p a) j = _
  rw [Matrix.updateRow_ne hj]
  ext k
  simp [Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

def lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    Submodule ℤ (ι → ℝ) := span ℤ (Set.range (basis p hp i a ha))

instance lattice_discrete (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    DiscreteTopology (lattice p hp i a ha) := inferInstanceAs
      (DiscreteTopology (span ℤ (Set.range (basis p hp i a ha))))

instance lattice_full (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    IsZLattice ℝ (lattice p hp i a ha) := inferInstanceAs
      (IsZLattice ℝ (span ℤ (Set.range (basis p hp i a ha))))

lemma covolume_lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    ZLattice.covolume (lattice p hp i a ha) = (p : ℝ)⁻¹ := by
  change ZLattice.covolume (span ℤ (Set.range (basis p hp i a ha))) = _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (basis p hp i a ha) volume),
    ZSpan.volume_real_fundamentalDomain]
  have he : Matrix.of (basis p hp i a ha) = matrix p i a := by ext; simp
  rw [he, det_matrix p i a ha, abs_of_pos (inv_pos.mpr (by exact_mod_cast hp))]

lemma generator_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    generator p a ∈ lattice p hp i a ha := by
  rw [← basis_pivot p hp i a ha]
  exact subset_span ⟨i, rfl⟩

lemma integer_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (z : ι → ℤ) : (fun j => (z j : ℝ)) ∈ lattice p hp i a ha := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => if j = i then (p : ℤ)*z i else z j-z i*a j, ?_⟩
  ext k
  rw [Finset.sum_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Pi.smul_apply, basis_pivot, generator, zsmul_eq_mul]
  have he : ∑ j ∈ Finset.univ.erase i,
      ((if j = i then (p : ℤ)*z i else z j-z i*a j) : ℤ) •
        basis p hp i a ha j k =
      if k = i then 0 else (z k : ℝ) - (z i : ℝ)*(a k : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i,
          ((z j : ℝ)-(z i : ℝ)*(a j : ℝ)) * (if j = k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        rw [ite_eq_right hji, basis_other p hp i a ha j hji]
        simp [Pi.basisFun_apply, Pi.single_apply, eq_comm, zsmul_eq_mul]
      _ = _ := by
        by_cases hki : k = i
        · subst k
          simp only [↓reduceIte]
          apply Finset.sum_eq_zero
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
        · simp [hki, Finset.mem_erase]
  simp only [zsmul_eq_mul] at he
  rw [he]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  by_cases hki : k = i
  · subst k; simp [ha]; field_simp
  · rw [ite_eq_right hki]
    push_cast
    field_simp
    ring

lemma mem_lattice_iff (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (x : ι → ℝ) : x ∈ lattice p hp i a ha ↔
      ∃ (z : ι → ℤ) (m : ℤ), x = (fun j => (z j : ℝ)) + m • generator p a := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine ⟨fun j => if j = i then 0 else c j, c i, ?_⟩
    rw [← hc]
    ext k
    rw [Finset.sum_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Pi.add_apply, Pi.smul_apply, basis_pivot]
    congr 1
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (c j : ℝ) * (if j = k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [basis_other p hp i a ha j (Finset.mem_erase.mp hj).1]
        simp [Pi.basisFun_apply, Pi.single_apply, eq_comm, zsmul_eq_mul]
      _ = _ := by
        by_cases hki : k = i
        · subst k
          simp only [↓reduceIte, Int.cast_zero]
          apply Finset.sum_eq_zero
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
        · simp [hki, Finset.mem_erase]
  · rintro ⟨z, m, rfl⟩
    exact (lattice p hp i a ha).add_mem (integer_mem p hp i a ha z)
      ((lattice p hp i a ha).smul_mem m (generator_mem p hp i a ha))



end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residue (p : ℕ) (k : ι → ℤ) : ι → ZMod p := fun j => (k j : ZMod p)



def codeLattice (p : ℕ) (C : Submodule (ZMod p) (ι → ZMod p)) :
    Submodule ℤ (ι → ℝ) where
  carrier := {x | ∃ k : ι → ℤ, residue p k ∈ C ∧ generator p k = x}
  zero_mem' := ⟨0, by convert C.zero_mem using 1 ; ext j ; simp [residue], by ext; simp [generator]⟩
  add_mem' := by
    rintro x y ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨k+l, ?_, ?_⟩
    · convert C.add_mem hk hl using 1 ; ext j ; simp [residue]
    · ext j; simp [generator, add_div]
  smul_mem' := by
    rintro m x ⟨k, hk, rfl⟩
    refine ⟨m • k, ?_, ?_⟩
    · convert C.smul_mem (m : ZMod p) hk using 1 ; ext j ; simp [residue]
    · ext j; simp [generator, zsmul_eq_mul, mul_div_assoc]

lemma lattice_eq_codeLattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    lattice p hp i a ha = codeLattice p (Submodule.span (ZMod p) {residue p a}) := by
  let : NeZero p := ⟨hp.ne'⟩
  ext x
  rw [mem_lattice_iff]
  constructor
  · rintro ⟨z, m, rfl⟩
    refine ⟨fun j => (p : ℤ)*z j+m*a j, ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨(m : ZMod p), ?_⟩
      ext j
      simp [residue]
    · ext j
      simp only [Pi.add_apply, zsmul_eq_mul, Pi.mul_apply]
      change ((p : ℤ)*z j+m*a j : ℤ) / (p : ℝ) = (z j : ℝ) + (m : ℝ)*((a j : ℝ)/p)
      push_cast
      field_simp

  · rintro ⟨k, hk, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hk
    let m : ℤ := r.val
    have hm : (m : ZMod p) = r := by simp [m]
    have hd (j : ι) : (p : ℤ) ∣ k j - m*a j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hj := congr_fun hr j
      simpa [residue, hm] using sub_eq_zero.mpr hj.symm
    choose z hz using hd
    refine ⟨z, m, ?_⟩
    ext j
    have hj : (k j : ℝ) - (m : ℝ)*(a j : ℝ) = (p : ℝ)*(z j : ℝ) := by
      exact_mod_cast hz j
    simp only [Pi.add_apply, zsmul_eq_mul, Pi.mul_apply]
    change (k j : ℝ)/(p : ℝ) = (z j : ℝ)+(m : ℝ)*((a j : ℝ)/p)
    apply (div_eq_iff (show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne')).mpr
    field_simp
    nlinarith

lemma normalized_lift {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [Fact p.Prime] (v : ι → ZMod p) (hv : v ≠ 0) :
    ∃ (i : ι) (a : ι → ℤ), a i = 1 ∧
      Submodule.span (ZMod p) {residue p a} = Submodule.span (ZMod p) {v} := by
  have hp : p.Prime := Fact.out
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let a : ι → ℤ := fun j => ((v i)⁻¹*v j).val
  have ha : a i = 1 := by simp only [a, inv_mul_cancel₀ hi, ZMod.val_one, Nat.cast_one]
  have hr : residue p a = (v i)⁻¹ • v := by
    ext j
    simp [residue, a]
  refine ⟨i, a, ha, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_span_singleton.mpr ⟨(v i)⁻¹, hr.symm⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v i, ?_⟩
    rw [hr, smul_smul, mul_inv_cancel₀ hi, one_smul]



theorem line_lattice (p : ℕ) [Fact p.Prime] (v : ι → ZMod p) (hv : v ≠ 0) :
    ∃ (_ : DiscreteTopology (codeLattice p (Submodule.span (ZMod p) {v}))),
      IsZLattice ℝ (codeLattice p (Submodule.span (ZMod p) {v})) ∧
      ZLattice.covolume (codeLattice p (Submodule.span (ZMod p) {v})) = (p : ℝ)⁻¹ := by
  obtain ⟨i, a, ha, hspan⟩ := normalized_lift p v hv
  have hp : 0 < p := (show p.Prime from Fact.out).pos
  have he : codeLattice p (Submodule.span (ZMod p) {v}) = lattice p hp i a ha := by
    rw [lattice_eq_codeLattice p hp i a ha, hspan]
  rw [he]
  exact ⟨inferInstance, inferInstance, covolume_lattice p hp i a ha⟩


end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def floorVector (p : ℕ) (t : ι → ℝ) : ι → ℤ := fun j => ⌊(p : ℝ)*t j⌋
def anchor (p : ℕ) (z : ι → ZMod p) : ι → ℝ := fun j => (z j).val / (p : ℝ)
def integerLift (p : ℕ) (z : ι → ZMod p) : ι → ℤ := fun j => (z j).val

def gridCell (p : ℕ) (z : ι → ZMod p) : Set (ι → ℝ) :=
  {t | ∀ j, t j - anchor p z j ∈ Set.Ico 0 (p : ℝ)⁻¹}

def cellPoint (p : ℕ) (t : ι → ℝ) (z : ι → ZMod p) : ι → ℝ :=
  generator p (floorVector p t - integerLift p z)

lemma residue_integerLift {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [NeZero p] (z : ι → ZMod p) :
    residue p (integerLift p z) = z := by
  ext j
  simp only [residue, integerLift, Int.cast_natCast, ZMod.natCast_zmod_val]

lemma cellPoint_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [NeZero p] (C : Submodule (ZMod p) (ι → ZMod p))
    (t : ι → ℝ) (z : ι → ZMod p)
    (hz : residue p (floorVector p t) - z ∈ C) : cellPoint p t z ∈ codeLattice p C := by
  refine ⟨floorVector p t - integerLift p z, ?_, rfl⟩
  convert hz using 1
  ext j
  simp [residue, integerLift]

lemma cell_residual {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (t : ι → ℝ) (z : ι → ZMod p) (j : ι) :
    (t-cellPoint p t z) j = ((z j).val + Int.fract ((p : ℝ)*t j))/(p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hf := Int.floor_add_fract ((p : ℝ)*t j)
  simp only [Pi.sub_apply, cellPoint, generator, floorVector, integerLift, Int.cast_sub,
    Int.cast_natCast]
  apply (eq_div_iff hp0).mpr
  field_simp
  nlinarith [Int.floor_add_fract (t j*(p : ℝ))]

lemma cell_residual_mem_grid (p : ℕ) (hp : 0 < p) (t : ι → ℝ) (z : ι → ZMod p) :
    t-cellPoint p t z ∈ gridCell p z := by
  intro j
  rw [cell_residual p hp t z j]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  change 0 ≤ ((z j).val+Int.fract ((p : ℝ)*t j))/(p : ℝ)-(z j).val/(p : ℝ) ∧
    ((z j).val+Int.fract ((p : ℝ)*t j))/(p : ℝ)-(z j).val/(p : ℝ) < (p : ℝ)⁻¹
  rw [add_div, add_sub_cancel_left]
  constructor
  · exact div_nonneg (Int.fract_nonneg _) hp0.le
  · simpa only [one_div] using (div_lt_div_of_pos_right (Int.fract_lt_one _) hp0)

lemma gridCell_subset_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (τ : ι → ℝ)
    (hτ : τ ∈ gridCell p z) (j : ι) : τ j ∈ Set.Ico 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hj := hτ j
  change 0 ≤ τ j - (z j).val/(p : ℝ) ∧ τ j - (z j).val/(p : ℝ) < (p : ℝ)⁻¹ at hj
  have hv : ((z j).val : ℝ)+1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (ZMod.val_lt _)
  have h0 : 0 ≤ ((z j).val : ℝ)/(p : ℝ) := div_nonneg (Nat.cast_nonneg _) hp0.le
  have hl : ((z j).val : ℝ)/(p : ℝ) + (p : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div, ← add_div, div_le_one hp0]
    exact hv
  exact ⟨by linarith, by linarith⟩

lemma integer_code_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (C : Submodule (ZMod p) (ι → ZMod p))
    (k : ι → ℤ) : (fun j => (k j : ℝ)) ∈ codeLattice p C := by
  refine ⟨fun j => (p : ℤ)*k j, ?_, ?_⟩
  · have he : residue p (fun j => (p : ℤ)*k j) = 0 := by ext; simp [residue]
    rw [he]; exact C.zero_mem
  · ext j
    simp [generator, show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne']

lemma cell_bits (p : ℕ) (hp : 0 < p) (C : Submodule (ZMod p) (ι → ZMod p))
    (t : ι → ℝ) (z : ι → ZMod p)
    (hz : residue p (floorVector p t) - z ∈ C) (e : ι → Bool) :
    cellPoint p t z + (fun j => if e j then (1 : ℝ) else 0) ∈ codeLattice p C ∧
      ∀ j, (t j - cellPoint p t z j - (if e j then (1 : ℝ) else 0)) ∈ Set.Icc (-1) 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  refine ⟨(codeLattice p C).add_mem (cellPoint_mem p C t z hz) ?_, ?_⟩
  · convert integer_code_mem p hp C (fun j => if e j then (1 : ℤ) else 0) using 1
    ext j
    cases e j <;> simp
  · intro j
    have hj := gridCell_subset_cube p hp z _ (cell_residual_mem_grid p hp t z) j
    simp only [Pi.sub_apply, Set.mem_Ico] at hj
    cases e j <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, Set.mem_Icc] <;>
      constructor <;> linarith


end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridCell_eq_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (z : ι → ZMod p) :
    gridCell p z = Set.univ.pi (fun j => Ico (anchor p z j) (anchor p z j+(p : ℝ)⁻¹)) := by
  ext t
  simp only [gridCell, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ico]
  constructor <;> intro ht j <;> have hj := ht j <;> constructor <;> linarith

lemma gridCell_measurable (p : ℕ) (z : ι → ZMod p) : MeasurableSet (gridCell p z) := by
  rw [gridCell_eq_pi]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

lemma floorVector_gridCell {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p) {z : ι → ZMod p} {t : ι → ℝ}
    (ht : t ∈ gridCell p z) : floorVector p t = integerLift p z := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  ext j
  apply Int.floor_eq_iff.mpr
  have hj := ht j
  change 0 ≤ t j-(z j).val/(p : ℝ) ∧ t j-(z j).val/(p : ℝ) < (p : ℝ)⁻¹ at hj
  have h1 := mul_le_mul_of_nonneg_left hj.1 hp0.le
  have h2 := mul_lt_mul_of_pos_left hj.2 hp0
  simp only [mul_sub, mul_div_cancel₀ _ hp0.ne', mul_inv_cancel₀ hp0.ne', mul_zero] at h1 h2
  change ((z j).val : ℝ) ≤ (p : ℝ)*t j ∧ (p : ℝ)*t j < (z j).val+1
  constructor <;> linarith

lemma gridCell_disjoint {p : ℕ} (hp : 0 < p) {z w : ι → ZMod p} (hzw : z ≠ w) :
    Disjoint (gridCell p z) (gridCell p w) := by
  let : NeZero p := ⟨hp.ne'⟩
  apply Set.disjoint_left.mpr
  intro t hz hw
  have he := (floorVector_gridCell hp hz).symm.trans (floorVector_gridCell hp hw)
  have he' := congr_arg (residue p) he
  simp only [residue_integerLift] at he'
  exact hzw he'

lemma anchor_floorVector {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p) {t : ι → ℝ}
    (ht : ∀ j, t j ∈ Ico 0 1) (j : ι) :
    anchor p (residue p (floorVector p t)) j = (⌊(p : ℝ)*t j⌋ : ℝ)/(p : ℝ) := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h0 : 0 ≤ ⌊(p : ℝ)*t j⌋ := Int.floor_nonneg.mpr (mul_nonneg hp0.le (ht j).1)
  have h1 : ⌊(p : ℝ)*t j⌋ < (p : ℤ) := Int.floor_lt.mpr (by simpa only [Int.cast_natCast, mul_one] using (mul_lt_mul_of_pos_left (ht j).2 hp0))
  have he := ZMod.val_intCast (n := p) (a := ⌊(p : ℝ)*t j⌋)
  rw [Int.emod_eq_of_lt h0 h1] at he
  unfold anchor residue floorVector
  congr 1
  exact_mod_cast he

lemma cube_mem_gridCell {p : ℕ} (hp : 0 < p) {t : ι → ℝ} (ht : ∀ j, t j ∈ Ico 0 1) :
    t ∈ gridCell p (residue p (floorVector p t)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  intro j
  rw [anchor_floorVector hp ht]
  have h0 := Int.floor_le ((p : ℝ)*t j)
  have h1 := Int.lt_floor_add_one ((p : ℝ)*t j)
  constructor
  · rw [sub_nonneg, div_le_iff₀ hp0]
    nlinarith
  · rw [sub_lt_iff_lt_add, ← one_div, ← add_div, lt_div_iff₀ hp0]
    nlinarith

lemma gridCell_iUnion {p : ℕ} (hp : 0 < p) :
    (⋃ z : ι → ZMod p, gridCell p z) = Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_univ_pi]
  constructor
  · rintro ⟨z, ht⟩ j
    exact gridCell_subset_cube p hp z t ht j
  · intro ht
    exact ⟨_, cube_mem_gridCell hp ht⟩

lemma gridCell_volume (p : ℕ) (z : ι → ZMod p) :
    volume (gridCell p z) = (ENNReal.ofReal ((p : ℝ)⁻¹))^Fintype.card ι := by
  rw [gridCell_eq_pi, volume_pi_pi]
  simp only [Real.volume_Ico, add_sub_cancel_left, Finset.prod_const, Finset.card_univ]

lemma gridCell_volume_real (p : ℕ) (z : ι → ZMod p) :
    volume.real (gridCell p z) = ((p : ℝ)⁻¹)^Fintype.card ι := by
  rw [Measure.real, gridCell_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal]
  positivity

lemma integral_gridCells {p : ℕ} [NeZero p] (hp : 0 < p) {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) :
    (∫ t in Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1), f t) =
      ∑ z : ι → ZMod p, ∫ t in gridCell p z, f t := by
  let : NeZero p := ⟨hp.ne'⟩
  have hi : IsCompact (Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hf' z : IntegrableOn f (gridCell p z) :=
    (hf.continuousOn.integrableOn_compact hi).mono_set (by
      intro t ht
      exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt))
  have he : Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) =ᵐ[volume]
      Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1) := by
    rw [volume_pi]
    exact Measure.pi_Ico_ae_eq_pi_Icc
  rw [←setIntegral_congr_set he, ←gridCell_iUnion hp]
  exact integral_iUnion_fintype (gridCell_measurable p)
    (fun _ _ hz => gridCell_disjoint hp hz) hf'


end SingleLatticeCovering.ConstructionA


end
end
end
end
end
end

end OAI
