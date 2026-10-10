import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def compatible (n : ℕ) : Submodule ℝ
    (C₀(Coord n, ℝ) × Lp ℝ 1 (volume : Measure (Coord n))) where
  carrier := {v | (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X)}
  zero_mem' := by exact Lp.coeFn_zero ..
  add_mem' := by
    intro v w hv hw
    change (fun X => (v.2 + w.2) X) =ᵐ[volume] (fun X => v.1 X + w.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    change (fun X => w.2 X) =ᵐ[volume] (fun X => w.1 X) at hw
    filter_upwards [Lp.coeFn_add v.2 w.2, hv, hw] with X hadd hvx hwx
    simpa [hvx, hwx] using hadd
  smul_mem' := by
    intro c v hv
    change (fun X => (c • v.2) X) =ᵐ[volume] (fun X => c * v.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    filter_upwards [Lp.coeFn_smul c v.2, hv] with X hsmul hvx
    simpa [hvx] using hsmul

theorem memLp_two {n : ℕ} (f : C₀(Coord n, ℝ)) (hfi : Integrable (fun X => f X)) :
    MemLp (fun X => f X) 2 volume := by
  apply (memLp_two_iff_integrable_sq hfi.aestronglyMeasurable).mpr
  apply (hfi.norm.const_mul ‖f‖).mono' ?_ ?_
  · exact hfi.aestronglyMeasurable.pow 2
  · filter_upwards [] with X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hbound : ‖f X‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f.toBCF X
    calc
      (f X) ^ 2 = ‖f X‖ * ‖f X‖ := by simp [Real.norm_eq_abs, ← sq, sq_abs]
      _ ≤ ‖f‖ * ‖f X‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

theorem integral_sq_le {n : ℕ} (f : C₀(Coord n, ℝ))
    (hfi : Integrable (fun X => f X)) :
    (∫ X, (f X) ^ 2) ≤ ‖f‖ * (∫ X, ‖f X‖) := by
  rw [← integral_const_mul]
  apply integral_mono
    ((memLp_two_iff_integrable_sq hfi.aestronglyMeasurable).mp (memLp_two f hfi))
    (hfi.norm.const_mul _) (fun X => ?_)
  have hbound : ‖f X‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_coe_le_norm f.toBCF X
  calc
    (f X) ^ 2 = ‖f X‖ * ‖f X‖ := by simp [Real.norm_eq_abs, ← sq, sq_abs]
    _ ≤ ‖f‖ * ‖f X‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

theorem L2_norm_sq {n : ℕ} {f : Coord n → ℝ}
    (hf : MemLp f 2 volume) : ‖hf.toLp f‖ ^ 2 = ∫ X, (f X) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with X hX
  simp [hX, Real.norm_eq_abs, sq_abs]

theorem member_memLp {n : ℕ} (v : compatible n) :
    MemLp (fun X => v.val.1 X) 2 volume :=
  memLp_two v.val.1 ((L1.integrable_coeFn v.val.2).congr v.property)

def toL2Linear (n : ℕ) : compatible n →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Coord n)) where
  toFun v := (member_memLp v).toLp (fun X => v.val.1 X)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(member_memLp (v + w)).coeFn_toLp,
      Lp.coeFn_add ((member_memLp v).toLp _) ((member_memLp w).toLp _),
      (member_memLp v).coeFn_toLp, (member_memLp w).coeFn_toLp] with X hvw ha hv hw
    rw [hvw, ha]
    simp only [Pi.add_apply, hv, hw]
    rfl
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(member_memLp (c • v)).coeFn_toLp,
      Lp.coeFn_smul c ((member_memLp v).toLp _),
      (member_memLp v).coeFn_toLp] with X hcv hs hv
    change _ = (c • (member_memLp v).toLp _) X
    rw [hcv, hs]
    simp only [Pi.smul_apply, hv]
    rfl

theorem norm_toL2Linear_sq_le {n : ℕ} (v : compatible n) :
    ‖toL2Linear n v‖ ^ 2 ≤ ‖v.val.1‖ * ‖v.val.2‖ := by
  change ‖(member_memLp v).toLp (fun X => v.val.1 X)‖ ^ 2 ≤ _
  rw [L2_norm_sq, L1.norm_eq_integral_norm]
  have hv : (fun X => v.val.2 X) =ᵐ[volume] (fun X => v.val.1 X) := v.property
  have heq : (∫ X, ‖v.val.2 X‖) = ∫ X, ‖v.val.1 X‖ := integral_congr_ae (hv.fun_comp norm)
  rw [heq]
  exact integral_sq_le v.val.1 ((L1.integrable_coeFn v.val.2).congr v.property)

theorem norm_toL2Linear_le {n : ℕ} (v : compatible n) :
    ‖toL2Linear n v‖ ≤ ‖v‖ := by
  have h := norm_toL2Linear_sq_le v
  have h1 : ‖v.val.1‖ ≤ ‖v‖ := norm_fst_le v.val
  have h2 : ‖v.val.2‖ ≤ ‖v‖ := norm_snd_le v.val
  have hh := mul_le_mul h1 h2 (norm_nonneg v.val.2) (norm_nonneg v)
  nlinarith [norm_nonneg v, norm_nonneg (toL2Linear n v)]

def toL2 (n : ℕ) : compatible n →L[ℝ] Lp ℝ 2 (volume : Measure (Coord n)) where
  toLinearMap := toL2Linear n
  cont := AddMonoidHomClass.continuous_of_bound (toL2Linear n) 1 (fun v => by
    simpa only [one_mul] using norm_toL2Linear_le (n := n) v)

theorem coeFn_toL2 {n : ℕ} (v : compatible n) :
    (fun X => toL2 n v X) =ᵐ[volume] (fun X => v.val.1 X) := by
  exact (member_memLp v).coeFn_toLp

theorem continuousOn_L2 {n : ℕ} {s : Set ℝ}
    (f : ℝ → C₀(Coord n, ℝ)) (r : ℝ → Lp ℝ 1 (volume : Measure (Coord n)))
    (hrep : ∀ t, (fun X => r t X) =ᵐ[volume] (fun X => f t X))
    (hf : ContinuousOn f s) (hr : ContinuousOn r s) :
    ContinuousOn (fun t => toL2 n ⟨(f t, r t), hrep t⟩) s := by
  apply (toL2 n).continuous.comp_continuousOn
  intro t ht
  exact tendsto_subtype_rng.mpr (hf.prodMk hr t ht)

theorem hasDerivWithinAt_compatible {n : ℕ} {s : Set ℝ} {t : ℝ}
    (f : ℝ → C₀(Coord n, ℝ)) (r : ℝ → Lp ℝ 1 (volume : Measure (Coord n)))
    (hrep : ∀ u, (fun X => r u X) =ᵐ[volume] (fun X => f u X))
    {df : C₀(Coord n, ℝ)} {dr : Lp ℝ 1 (volume : Measure (Coord n))}
    (hdrep : (fun X => dr X) =ᵐ[volume] (fun X => df X))
    (hf : HasDerivWithinAt f df s t) (hr : HasDerivWithinAt r dr s t) :
    HasDerivWithinAt (fun u => (⟨(f u, r u), hrep u⟩ : compatible n))
      ⟨(df, dr), hdrep⟩ s t := by
  apply (hasDerivWithinAt_iff_isLittleO (𝕜 := ℝ) (F := compatible n)).mpr
  apply Asymptotics.IsLittleO.of_norm_left
  exact (hf.prodMk hr).isLittleO.norm_left

theorem hasDerivWithinAt_L2 {n : ℕ} {s : Set ℝ} {t : ℝ}
    (f : ℝ → C₀(Coord n, ℝ)) (r : ℝ → Lp ℝ 1 (volume : Measure (Coord n)))
    (hrep : ∀ u, (fun X => r u X) =ᵐ[volume] (fun X => f u X))
    {df : C₀(Coord n, ℝ)} {dr : Lp ℝ 1 (volume : Measure (Coord n))}
    (hdrep : (fun X => dr X) =ᵐ[volume] (fun X => df X))
    (hf : HasDerivWithinAt f df s t) (hr : HasDerivWithinAt r dr s t) :
    HasDerivWithinAt (fun u => toL2 n ⟨(f u, r u), hrep u⟩)
      (toL2 n ⟨(df, dr), hdrep⟩) s t := by
  let v : ℝ → compatible n := fun u => ⟨(f u, r u), hrep u⟩
  let dv : compatible n := ⟨(df, dr), hdrep⟩
  have hh : HasDerivWithinAt v dv s t :=
    hasDerivWithinAt_compatible f r hrep hdrep hf hr
  have hL : HasFDerivAt (toL2 n) (toL2 n) (v t) :=
    (toL2 n).hasFDerivAt (x := v t)
  exact HasFDerivAt.comp_hasDerivWithinAt (F := compatible n)
    (E := Lp ℝ 2 (volume : Measure (Coord n))) t hL hh

theorem C1_L2 {n : ℕ} {s : Set ℝ}
    (f df : ℝ → C₀(Coord n, ℝ)) (r dr : ℝ → Lp ℝ 1 (volume : Measure (Coord n)))
    (hrep : ∀ u, (fun X => r u X) =ᵐ[volume] (fun X => f u X))
    (hdrep : ∀ u, (fun X => dr u X) =ᵐ[volume] (fun X => df u X))
    (hf : ContinuousOn f s) (hr : ContinuousOn r s)
    (hdf : ContinuousOn df s) (hdr : ContinuousOn dr s)
    (hfder : ∀ t ∈ s, HasDerivWithinAt f (df t) s t)
    (hrder : ∀ t ∈ s, HasDerivWithinAt r (dr t) s t) :
    ContinuousOn (fun u => toL2 n ⟨(f u, r u), hrep u⟩) s ∧
    ContinuousOn (fun u => toL2 n ⟨(df u, dr u), hdrep u⟩) s ∧
    ∀ t ∈ s, HasDerivWithinAt (fun u => toL2 n ⟨(f u, r u), hrep u⟩)
      (toL2 n ⟨(df t, dr t), hdrep t⟩) s t :=
  ⟨continuousOn_L2 f r hrep hf hr, continuousOn_L2 df dr hdrep hdf hdr,
    fun t ht => hasDerivWithinAt_L2 f r hrep (hdrep t) (hfder t ht) (hrder t ht)⟩

end VelocityDetection.TailSpace
end

end OAI
