import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinMode

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma spinCubeMode_inner {b : ℝ} (hb : 0 < b) (a c : SpinMode) :
    (∫ x, star (spinCubeMode b a x) * spinCubeMode b c x ∂(spinCubeMeasure b)) =
      if a = c then (1 : ℂ) else 0 := by
  classical
  rw [show (fun x => star (spinCubeMode b a x) * spinCubeMode b c x) =
    fun x => (star (spinDelta a.1 x.1) * spinDelta c.1 x.1) *
      (star (cubeMode b a.2 x.2) * cubeMode b c.2 x.2) by
    funext x; simp only [spinCubeMode, star_mul]; ring]
  rw [spinCubeMeasure, integral_prod_mul
    (fun q => star (spinDelta a.1 q) * spinDelta c.1 q)
    (fun x => star (cubeMode b a.2 x) * cubeMode b c.2 x), spinDelta_inner,
    show (∫ x, star (cubeMode b a.2 x) * cubeMode b c.2 x ∂(cubeMeasure b 3)) =
      if a.2 = c.2 then (1 : ℂ) else 0 from
      by
        have H := scalarTensor_orthonormal (μ := volume.restrict (Ioc 0 b))
          (neumannMode b) (fun i j => by
            by_cases hij : i = j
            · simpa only [ite_eq_left hij] using neumannMode_orthonormal hb i j
            · simpa only [ite_eq_right hij] using neumannMode_orthonormal hb i j) a.2 c.2
        by_cases h : a.2 = c.2
        · simpa only [cubeMode, cubeMeasure, ite_eq_left h] using H
        · simpa only [cubeMode, cubeMeasure, ite_eq_right h] using H]
  by_cases h1 : a.1 = c.1 <;> by_cases h2 : a.2 = c.2 <;>
    simp [h1, h2, Prod.ext_iff]

section FiniteCubeBasis
variable {I : Type*} [Fintype I]

lemma finiteCubeMeasure_le_volume (b : ℝ) :
    finiteCubeMeasure b I ≤ (volume : Measure (I → ℝ)) := by
  unfold finiteCubeMeasure
  rw [← Measure.restrict_pi_pi]
  exact Measure.restrict_le_self

lemma finiteCubeMode_memLp (b : ℝ) (q : I → ℕ) :
    MemLp (finiteCubeMode b q) 2 (finiteCubeMeasure b I) := by
  have hm : AEStronglyMeasurable (finiteCubeMode b q) (finiteCubeMeasure b I) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (neumannMode_memLp b (q i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : I => volume.restrict (Ioc 0 b)) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [finiteCubeMode, finiteCubeMeasure, norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i => (neumannMode_memLp b (q i)).norm.integrable_sq)

lemma finiteCubeMode_inner {b : ℝ} (hb : 0 < b) (q r : I → ℕ) :
    (∫ x, star (finiteCubeMode b q x) * finiteCubeMode b r x ∂(finiteCubeMeasure b I)) =
      if q = r then (1 : ℂ) else 0 := by
  classical
  simp only [finiteCubeMode, finiteCubeMeasure, star_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : I => volume.restrict (Ioc 0 b))
    (fun i x => star (neumannMode b (q i) x) * neumannMode b (r i) x)]
  simp_rw [neumannMode_orthonormal hb]
  by_cases h : q = r
  · subst r; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma finiteCubeMode_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (finiteCubeMeasure b I) (finiteCubeMode b) := by
  classical
  let e := Fintype.equivFin I
  have H := (cubeMode_complete hb (Fintype.card I)).comp (reindexCube e)
    (reindexCube_measurePreserving b e)
  intro f hf hz
  apply H f hf
  intro q
  have he (x : I → ℝ) : cubeMode b q (reindexCube e x) = finiteCubeMode b (q ∘ e) x := by
    have hh := finiteCubeMode_reindex b e (q ∘ e) x
    simpa only [Function.comp_def, e.apply_symm_apply, finiteCubeMode, cubeMode] using hh
  simp_rw [he]
  exact hz (q ∘ e)

end FiniteCubeBasis

noncomputable def cubeLabelEquiv (n : ℕ) :
    (Fin n → SpinMode) ≃ (Spins n × ((Fin n × Fin 3) → ℕ)) where
  toFun a := (fun i => (a i).1, fun ij => (a ij.1).2 ij.2)
  invFun sq := fun i => (sq.1 i, fun j => sq.2 (i,j))
  left_inv a := by rfl
  right_inv sq := by rfl

noncomputable def cubeFermionCoefficient {n : ℕ} (ψ : H1Vector n) (b : ℝ)
    (a : Fin n → SpinMode) : ℂ :=
  ∫ x, star (finiteCubeMode b (cubeLabelEquiv n a).2 x) *
    ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 x)
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

noncomputable def cubeMass {n : ℕ} (ψ : H1Vector n) (b : ℝ) : ℝ :=
  ∑ s, ∫ x, ‖ψ.value s (WithLp.toLp 2 x)‖^2
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

lemma H1Vector.cube_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) (s : Spins n) :
    MemLp (fun x => ψ.value s (WithLp.toLp 2 x)) 2
      (finiteCubeMeasure b (Fin n × Fin 3)) :=
  ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)).mono_measure
    (finiteCubeMeasure_le_volume b)

lemma finiteCubeCoefficient_summable {I : Type*} [Fintype I] {b : ℝ} (hb : 0 < b)
    (f : (I → ℝ) → ℂ) (hf : MemLp f 2 (finiteCubeMeasure b I)) :
    Summable (fun q => ‖∫ x, star (finiteCubeMode b q x) * f x
      ∂(finiteCubeMeasure b I)‖^2) := by
  have ho : Orthonormal ℂ (fun q : I → ℕ => (finiteCubeMode_memLp b q).toLp (finiteCubeMode b q)) := by
    rw [orthonormal_iff_ite]
    intro q r
    rw [inner_toLp_complex]
    exact finiteCubeMode_inner hb q r
  simpa only [inner_toLp_complex] using ho.inner_products_summable (hf.toLp f)

lemma cubeFermionCoefficient_summable {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    Summable (fun a => ‖cubeFermionCoefficient ψ b a‖^2) := by
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
      ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have hs (s : Spins n) : Summable (fun q : (Fin n × Fin 3) → ℕ => F (s,q)) :=
    (by
      dsimp only [F]
      exact finiteCubeCoefficient_summable (I := Fin n × Fin 3) hb
        (fun x => ψ.value s (WithLp.toLp 2 x)) (ψ.cube_memLp b s))
  have hF : Summable F := (summable_prod_of_nonneg (f := F) (fun _ => sq_nonneg _)).2
    ⟨hs, (hasSum_fintype _).summable⟩
  exact (Equiv.summable_iff (cubeLabelEquiv n)).2 hF

lemma cubeFermionCoefficient_parseval {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    (∑' a, ‖cubeFermionCoefficient ψ b a‖^2) = cubeMass ψ b := by
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
      ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have hF : Summable F := (Equiv.summable_iff (cubeLabelEquiv n)).1
    (cubeFermionCoefficient_summable ψ hb)
  change (∑' a, F (cubeLabelEquiv n a)) = _
  rw [(cubeLabelEquiv n).tsum_eq, hF.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  exact completeOrbitals_parseval (finiteCubeMode b) (finiteCubeMode_memLp b)
    (fun q r => by
      by_cases hqr : q = r
      · simpa only [ite_eq_left hqr] using finiteCubeMode_inner hb q r
      · simpa only [ite_eq_right hqr] using finiteCubeMode_inner hb q r)
    (finiteCubeMode_complete hb) _ (ψ.cube_memLp b s)

lemma cubeFermionCoefficient_antisymmetric {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (b : ℝ) :
    FermionicCoefficients (cubeFermionCoefficient ψ b) := by
  intro p a
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
    (hψ p (cubeLabelEquiv n a).1)
  filter_upwards [ha.filter_mono (ae_mono (finiteCubeMeasure_le_volume b))] with x hx
  rw [hx]
  ring

noncomputable def cubeKinetic {n : ℕ} (ψ : H1Vector n) (b : ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ s, ∑ i, ∫ x, ‖ψ.gradient s i (WithLp.toLp 2 x)‖^2
    ∂(finiteCubeMeasure b (Fin n × Fin 3))

noncomputable def cubeSpectralWeight {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin n × Fin 3, (((cubeLabelEquiv n a).2 i : ℝ) * Real.pi / b)^2

lemma cubeSpectralWeight_nonneg {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) :
    0 ≤ cubeSpectralWeight b a := by
  unfold cubeSpectralWeight
  positivity

lemma configuration_nonempty_equiv {n : ℕ} (hn : 0 < n) :
    Nonempty ((Fin n × Fin 3) ≃ Fin ((3*n-1)+1)) := by
  have hc : Fintype.card (Fin n × Fin 3) = (3*n-1)+1 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  exact ⟨(Fintype.equivFin _).trans (finCongr hc)⟩

lemma cubeFermionCoefficient_finite_energy {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) (s : Finset (Fin n → SpinMode)) :
    ∑ a ∈ s, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2 ≤
      cubeKinetic ψ b := by
  classical
  let e := cubeLabelEquiv n
  let Q := s.image (fun a => (e a).2)
  let F : Spins n × ((Fin n × Fin 3) → ℕ) → ℝ := fun sq =>
    ((1/2 : ℝ) * ∑ i, ((sq.2 i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (finiteCubeMode b sq.2 x) * ψ.value sq.1 (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b (Fin n × Fin 3))‖^2
  have he : ∑ a ∈ s, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2 =
      ∑ sq ∈ s.image e, F sq := by
    rw [Finset.sum_image e.injective.injOn]
    rfl
  have hsub : s.image e ⊆ Finset.univ.product Q := by
    intro sq hsq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsq
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
  have hF (sq) : 0 ≤ F sq := by dsimp only [F]; positivity
  obtain ⟨E⟩ := configuration_nonempty_equiv hn
  calc
    _ = ∑ sq ∈ s.image e, F sq := he
    _ ≤ ∑ sq ∈ Finset.univ.product Q, F sq :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun sq _ _ => hF sq)
    _ = ∑ t : Spins n, ∑ q ∈ Q, F (t,q) := Finset.sum_product _ _ _
    _ ≤ ∑ t : Spins n, (1/2 : ℝ) * ∑ i, ∫ x,
        ‖ψ.gradient t i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b (Fin n × Fin 3)) := by
      apply Finset.sum_le_sum
      intro t _
      have H := finiteCube_weak_spectral_lower E hb (ψ.value_L2 t) (ψ.partial_L2 t)
        (ψ.weak_partial t) Q
      have hh := mul_le_mul_of_nonneg_left H (show (0:ℝ) ≤ 1/2 by norm_num)
      simpa only [F, mul_assoc, ← Finset.mul_sum] using hh
    _ = cubeKinetic ψ b := by simp only [cubeKinetic, Finset.mul_sum]

lemma cubeFermionCoefficient_energy_summable {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    Summable (fun a => cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2) := by
  exact summable_of_sum_le (fun a => mul_nonneg (cubeSpectralWeight_nonneg b a) (sq_nonneg _))
    (fun s => cubeFermionCoefficient_finite_energy hn ψ hb s)

lemma cubeFermionCoefficient_energy_le {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    (∑' a, cubeSpectralWeight b a * ‖cubeFermionCoefficient ψ b a‖^2) ≤
      cubeKinetic ψ b := by
  exact Real.tsum_le_of_sum_le (fun a => mul_nonneg (cubeSpectralWeight_nonneg b a) (sq_nonneg _))
    (fun s => cubeFermionCoefficient_finite_energy hn ψ hb s)

lemma cubeSpectralWeight_eq_neumann {n : ℕ} (b : ℝ) (a : Fin n → SpinMode) :
    cubeSpectralWeight b a =
      ∑ i, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
  classical
  unfold cubeSpectralWeight
  simp only [Fintype.sum_prod_type, cubeLabelEquiv, Equiv.coe_fn_mk,
    latticeRadius, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fermionic_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    ((b⁻¹)^2 * (thomasFermiCoefficient * (n : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) * (n : ℝ) ^ (4/3 : ℝ))) * cubeMass ψ b ≤
        cubeKinetic ψ b := by
  have hs := cubeFermionCoefficient_summable ψ hb
  have hf := cubeFermionCoefficient_antisymmetric hψ b
  have he := cubeFermionCoefficient_energy_summable hn ψ hb
  rw [← cubeFermionCoefficient_parseval ψ hb, ← tsum_mul_left]
  apply le_trans (Summable.tsum_le_tsum ?_ (hs.mul_left _) he)
    (cubeFermionCoefficient_energy_le hn ψ hb)
  intro a
  by_cases hz : cubeFermionCoefficient ψ b a = 0
  · simp [hz]
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact hz (hf.vanish_of_repeat hne hij)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [cubeSpectralWeight_eq_neumann]
  exact neumann_kinetic_sum_lower a ha hb
end Coulomb

end
end

end OAI
