import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.FullCarrier

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma linear_pi_expansion (L : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  have he : v = ∑ i, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

lemma ae_fderivWithin_scalar_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (fun x => φ (fun i => π i x))) C.domain z =
        (dφ (fun i => C.scalar (π i) z)).comp
          (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)) := by
  have hall : ∀ᵐ z ∂volume.restrict C.domain,
      ∀ i, DifferentiableWithinAt ℝ (C.scalar (π i)) C.domain z :=
    ae_all_iff.mpr fun i => C.ae_differentiableWithinAt_scalar (hπ i).choose_spec
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,hall] with z hz hzs hD
  have hPi := hasFDerivWithinAt_pi.mpr (fun i => (hD i).hasFDerivWithinAt)
  have hcomp := (hφ (fun i => C.scalar (π i) z)).comp_hasFDerivWithinAt z hPi
  have he : EqOn (C.scalar (fun x => φ (fun i => π i x)))
      (fun z => φ (fun i => C.scalar (π i) z)) C.domain := by
    intro y hy
    simp only [C.scalar_eq hy]
  exact (hcomp.congr he (he hzs)).fderivWithin hz

lemma ae_jacobian_update_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => φ (fun j => π j x))) z =
        dφ (fun j => C.scalar (π j) z) (Pi.single i 1) * C.jacobian π z := by
  filter_upwards [C.ae_fderivWithin_scalar_multi π hπ hφ] with z hz
  rw [C.jacobian_update,hz]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a j =>
    fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)
  let a : Fin k → ℝ := fun j => dφ (fun l => C.scalar (π l) z) (Pi.single j 1)
  have he : (fun j => ((dφ (fun i => C.scalar (π i) z)).comp
      (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)))
        (EuclideanSpace.single j 1)) = ∑ l, a l • M l := by
    ext j
    rw [ContinuousLinearMap.comp_apply,linear_pi_expansion]
    simp only [ContinuousLinearMap.pi_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,a,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact Matrix.det_updateRow_sum M i a

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_multi [BorelSpace X] [CompactSpace X]
    {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  classical
  obtain ⟨C,_,_,_,hrep⟩ := hT
  rw [hrep,hrep]
  apply tsum_congr
  intro q
  have had : Admissible b (Function.update π i (fun x => φ (fun j => π j x))) := by
    refine ⟨hb,?_⟩
    intro j
    by_cases he : j = i
    · simpa [he] using hφπ.1
    · simpa only [Function.update_of_ne he] using hπ j
  rw [IntegerChart.action,ite_eq_left had,IntegerChart.action,ite_eq_left ⟨hb.mul hdπ,hπ⟩]
  apply integral_congr_ae
  filter_upwards [(C q).ae_jacobian_update_multi π hπ hφ i,ae_restrict_mem (C q).borel] with z hz hzs
  rw [hz]
  simp only [(C q).scalar_eq hzs]
  ring

end CAT0Fillings.Foundations

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [Nonempty X] in
lemma NormalApprox.product_rule [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) + T f (Matrix.vecCons b π) =
      boundarySucc T (fun x => b x * f x) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := (hlim b (Matrix.vecCons f π)).add (hlim f (Matrix.vecCons b π))
  have hright := boundarySucc_weak_limit hlim (fun x => b x * f x) π
  have he j := IntegerRectifiable.product_rule (hTs j).2.1 hb hf π hπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

omit [Nonempty X] in
lemma NormalApprox.apply_update_multi [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := hlim b (Function.update π i (fun x => φ (fun j => π j x)))
  have hright := hlim (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_update_multi (hrect j) hb π hπ hφ i hφπ hdπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.apply_permute [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    T b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ)*T b π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hl := hlim b (π ∘ σ)
  have hr := (hlim b π).const_mul ((Equiv.Perm.sign σ : ℤ):ℝ)
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_permute (hrect j) hab σ
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma NormalApprox.abs_apply_permute {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    |T b (π ∘ σ)| = |T b π| := by
  rw [hT.apply_permute hab σ,abs_mul,abs_unit_intCast,one_mul]

lemma NormalApprox.head_measure_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ}
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (hf : BoundedLip f)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    |T b (Matrix.vecCons f π)| ≤ (K:ℝ)^k *
      ((∫ x, |f x| ∂currentMassMeasure hT.normal.1) +
       (∫ x, |f x| ∂currentMassMeasure hT.normal.2)) := by
  have hbl : BoundedLip b := ⟨⟨1,hb⟩,1,hb1⟩
  have hp := hT.product_rule hbl hf π (fun i => ⟨K,hπ i⟩)
  have he : T b (Matrix.vecCons f π) =
      boundarySucc T (fun x => b x*f x) π - T f (Matrix.vecCons b π) := by linarith
  have hbd := hT.normal.2.mass_bound (currentMassMeasure_controls hT.normal.2)
    (hbl.mul hf) (fun _ => K) hπ
  have hcur := hT.normal.1.mass_bound (currentMassMeasure_controls hT.normal.1)
    (π := Matrix.vecCons b π) hf (Matrix.vecCons 1 (fun _ => K)) (by intro i;exact Fin.cases hb (fun j => hπ j) i)
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,NNReal.coe_one,one_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hbd hcur
  have hbi : (∫ x, |b x*f x| ∂currentMassMeasure hT.normal.2) ≤
      ∫ x, |f x| ∂currentMassMeasure hT.normal.2 := by
    apply integral_mono (integrable_boundedLip _ (hbl.mul hf)).abs (integrable_boundedLip _ hf).abs
    intro x
    change |b x*f x| ≤ |f x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hb1 x) (abs_nonneg _)).trans_eq (one_mul _)
  rw [he]
  calc _ ≤ |boundarySucc T (fun x => b x*f x) π| + |T f (Matrix.vecCons b π)| := abs_sub _ _
    _ ≤ (K:ℝ)^k * (∫ x, |f x| ∂currentMassMeasure hT.normal.2) +
        (K:ℝ)^k * (∫ x, |f x| ∂currentMassMeasure hT.normal.1) :=
      add_le_add (hbd.trans (mul_le_mul_of_nonneg_left hbi (pow_nonneg K.coe_nonneg _))) hcur
    _ = _ := by ring

lemma NormalApprox.coordinate_measure_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ}
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (hf : BoundedLip f)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) (i : Fin (k+1)) :
    |T b (Function.update π i f)| ≤ (K:ℝ)^k *
      ((∫ x, |f x| ∂currentMassMeasure hT.normal.1) +
       (∫ x, |f x| ∂currentMassMeasure hT.normal.2)) := by
  classical
  let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hne (j : Fin k) : σ j.succ ≠ i := by
    intro he
    have hh := congrArg σ he
    simp [σ] at hh
  have he : (Function.update π i f) ∘ σ = Matrix.vecCons f ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · simp only [Function.comp_apply,Function.update_of_ne (hne j),Matrix.cons_val_succ,ρ]
  have ha : Admissible b (Function.update π i f) := by
    refine ⟨⟨⟨1,hb⟩,1,hb1⟩,?_⟩
    intro j
    by_cases hj : j = i
    · simpa [hj] using hf.1
    · simpa only [Function.update_of_ne hj] using (show ∃ L, LipschitzWith L (π j) from ⟨K,hπ j⟩)
  rw [←hT.abs_apply_permute ha σ,he]
  exact hT.head_measure_bound hb hb1 hf ρ (fun j => hπ (σ j.succ))

theorem fullSlice_distributional_bound {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    {φ : (Fin (k+1) → ℝ) → ℝ}
    {dφ : (Fin (k+1) → ℝ) → (Fin (k+1) → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin (k+1))
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    |∫ z : Euc (k+1), dφ (WithLp.ofLp z) (Pi.single i 1)*
        fullSlice h π z b (fun j => Fin.elim0 j)| ≤
      (K:ℝ)^k * ((∫ x, |φ (fun j => π j x)| ∂currentMassMeasure h.normal.1) +
       (∫ x, |φ (fun j => π j x)| ∂currentMassMeasure h.normal.2)) := by
  have hbl : BoundedLip b := ⟨⟨1,hb⟩,1,hb1⟩
  have he := (fullSlice_weighted_integral h hX π (fun j => boundedLip_of_lipschitz (hπ j))
    (φ := fun z => dφ (WithLp.ofLp z) (Pi.single i 1)) hdπ hbl).2
  rw [←he]
  have hc := h.apply_update_multi hbl π (fun j => ⟨K,hπ j⟩) hφ i hφπ hdπ
  have hw : (fun x => dφ (fun j => π j x) (Pi.single i 1)*b x) =
      (fun x => b x*dφ (fun j => π j x) (Pi.single i 1)) := by funext x;ring
  change |T (fun x => dφ (fun j => π j x) (Pi.single i 1)*b x) π| ≤ _
  rw [hw,←hc]
  exact h.coordinate_measure_bound hb hb1 hφπ π hπ i

end CAT0Fillings.Slicing
end

end OAI
