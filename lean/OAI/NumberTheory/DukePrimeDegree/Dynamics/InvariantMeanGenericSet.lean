import OAI.NumberTheory.DukePrimeDegree.Dynamics.BoundedGenericSet

namespace OAI

/-!
# Uniform generic sets with a nonconstant invariant mean

The ambient measure need not be ergodic for the chosen root flow.
The uniform average is therefore compared with its actual invariant
mean q(x).  This keeps ambient stabilizer invariance available for the
fiber-correction argument, without replacing q by the global integral.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def constantMeanOrbitSet (T : Y → Y) (q : Y → ℝ) : Set Y :=
  ⋂ N : ℕ, {x | q (T^[N] x) = q x}

lemma measurableSet_constantMeanOrbitSet (T : Y → Y) (hT : Measurable T)
    (q : Y → ℝ) (hq : Measurable q) :
    MeasurableSet (constantMeanOrbitSet T q) :=
  MeasurableSet.iInter (fun N => measurableSet_eq_fun (hq.comp (hT.iterate N)) hq)

lemma ae_mem_constantMeanOrbitSet (μ : Measure Y)
    (T : Y → Y) (hT : MeasurePreserving T μ μ) (q : Y → ℝ)
    (hqinvariant : (fun x => q (T x)) =ᵐ[μ] q) :
    ∀ᵐ x ∂μ, x ∈ constantMeanOrbitSet T q := by
  have hi (N : ℕ) : (fun x => q (T^[N] x)) =ᵐ[μ] q := by
    induction N with
    | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
    | succ N ih =>
      have hshift := (hT.iterate N).quasiMeasurePreserving.ae_eq_comp hqinvariant
      simpa only [Function.iterate_succ_apply', Function.comp_def] using hshift.trans ih
  simpa only [constantMeanOrbitSet, mem_iInter, mem_ofPred_eq] using ae_all_iff.mpr hi

omit [MeasurableSpace Y] in
lemma birkhoffAverage_eq_mean_on_orbitSet
    (T : Y → Y) (q : Y → ℝ) (x : Y) (hx : x ∈ constantMeanOrbitSet T q)
    (N : ℕ) (hN : N ≠ 0) :
    birkhoffAverage ℝ T q N x = q x := by
  have hsum : (∑ k ∈ Finset.range N, q (T^[k] x)) = (N : ℝ) * q x := by
    calc
      _ = ∑ _k ∈ Finset.range N, q x :=
        Finset.sum_congr rfl (fun k _ => mem_iInter.mp hx k)
      _ = _ := by simp
  rw [birkhoffAverage, smul_eq_mul, birkhoffSum, hsum,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]

/-- One bounded coboundary plus the maximal inequality controls the
nonconstant invariant mean on a full-measure orbit set. -/
theorem exists_uniform_invariant_mean_set_from_residual
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (q : Y → ℝ) (hqm : Measurable q) (hqi : Integrable q μ)
    (hqinvariant : (fun x => q (T x)) =ᵐ[μ] q)
    (η : ℝ) (hη : 0 < η) (M : ℕ) (hM : M ≠ 0) :
    ∃ G : Set Y, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal
        ((∫ x, |birkhoffAverage ℝ T f M x - q x| ∂μ) / η) ∧
      ∀ x ∈ G, ∀ N : ℕ, N ≠ 0 →
        |birkhoffAverage ℝ T f N x - q x| ≤
          (N : ℝ)⁻¹ * (2 * (M * C)) + η := by
  let r : Y → ℝ := fun x => birkhoffAverage ℝ T f M x - q x
  have hrm : Measurable r := (measurable_orbit_average T hT.measurable f hfm M).sub hqm
  have hri : Integrable r μ := (integrable_orbit_average μ T hT f hfi M).sub hqi
  obtain ⟨G, hG, hGμ, hGsum⟩ := exists_discrete_average_good_set μ hT hri.norm
    (by simpa only [Real.norm_eq_abs] using hrm.norm)
    (fun x => abs_nonneg (r x)) η hη
  let I := constantMeanOrbitSet T q
  have hI : MeasurableSet I := measurableSet_constantMeanOrbitSet T hT.measurable q hqm
  have hIzero : μ Iᶜ = 0 := ae_iff.mp (ae_mem_constantMeanOrbitSet μ T hT q hqinvariant)
  refine ⟨G ∩ I, hG.inter hI, ?_, ?_⟩
  · rw [compl_inter]
    exact (measure_union_le _ _).trans (by
      simpa only [hIzero, add_zero, r, Real.norm_eq_abs] using hGμ)
  · rintro x ⟨hxG, hxI⟩ N hN
    have hrbound : |birkhoffAverage ℝ T r N x| ≤ η :=
      abs_orbit_average_le_of_abs_sum_le T r η N hN x (hGsum x hxG N)
    have hcob := orbit_average_coboundary_bound T (orbitAveragePotential T f M)
      (M * C) (orbitAveragePotential_abs_le T f C hC0 hC M) N x
    have hfun : (fun y => orbitAveragePotential T f M y -
        orbitAveragePotential T f M (T y)) = fun y => f y - birkhoffAverage ℝ T f M y := by
      funext y
      exact (sub_orbit_average_eq_coboundary T f M hM y).symm
    rw [hfun] at hcob
    have hqaverage := birkhoffAverage_eq_mean_on_orbitSet T q x hxI N hN
    have hdecomp : birkhoffAverage ℝ T f N x - q x =
        birkhoffAverage ℝ T (fun y => f y - birkhoffAverage ℝ T f M y) N x +
          birkhoffAverage ℝ T r N x := by
      change _ = birkhoffAverage ℝ T (f - birkhoffAverage ℝ T f M) N x +
        birkhoffAverage ℝ T (birkhoffAverage ℝ T f M - q) N x
      rw [birkhoffAverage_sub_apply, birkhoffAverage_sub_apply, hqaverage]
      ring
    rw [hdecomp]
    exact (abs_add_le _ _).trans (add_le_add hcob hrbound)

/-- Fixed good sets for a nonergodic transformation. Their limiting
observable is the invariant mean supplied by the mean-ergodic theorem. -/
theorem exists_uniform_invariant_mean_set
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (q : Y → ℝ) (hqm : Measurable q) (hqi : Integrable q μ)
    (hqinvariant : (fun x => q (T x)) =ᵐ[μ] q)
    (hmean : Tendsto (fun M => ∫ x, |birkhoffAverage ℝ T f M x - q x| ∂μ)
      atTop (𝓝 0))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀,
        |birkhoffAverage ℝ T f N x - q x| ≤ ε := by
  have hsmall := hmean.eventually
    (gt_mem_nhds (show (0 : ℝ) < δ * (ε / 2) by positivity))
  obtain ⟨M, hM, hres⟩ := (eventually_gt_atTop (0 : ℕ)).and hsmall |>.exists
  obtain ⟨G, hG, hGμ, hGbound⟩ := exists_uniform_invariant_mean_set_from_residual μ T hT
    f hfm hfi C hC0 hC q hqm hqi hqinvariant (ε / 2) (by positivity) M (Nat.ne_of_gt hM)
  refine ⟨G, hG, hGμ.trans ?_, ?_⟩
  · exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by positivity : 0 < ε / 2)).mpr hres.le)
  · have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * (M * C))) atTop (𝓝 0) := by
      simpa only [div_eq_inv_mul] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (2 * (M * C)) / (N : ℝ)) atTop (𝓝 0))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_gt_atTop (0 : ℕ)).and
      (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))))
    refine ⟨N₀, ?_⟩
    intro x hx N hN
    have hs := hGbound x hx N (Nat.ne_of_gt (hN₀ N hN).1)
    linarith [(hN₀ N hN).2]

end DukePrimeDegree

end

end OAI
