import OAI.MathematicalPhysics.RapidForcing.StepSchwartz

namespace OAI


open scoped BigOperators ENNReal Topology SchwartzMap
open Set MeasureTheory

namespace RapidForcing

def HasSchwartzExtension {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Field E) : Prop :=
  ∃ g : 𝓢(ℝ × Space, E), ∀ t, 0 ≤ t → ∀ x, v t x = g (t, x)

namespace HasSchwartzExtension
section General
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v w : Field E}

lemma zero : HasSchwartzExtension (fun _ _ => (0 : E)) := ⟨0, by simp⟩

lemma add (hv : HasSchwartzExtension v) (hw : HasSchwartzExtension w) :
    HasSchwartzExtension (fun t x => v t x + w t x) := by
  obtain ⟨g, hg⟩ := hv
  obtain ⟨h, hh⟩ := hw
  exact ⟨g + h, fun t ht x => by simp [hg t ht x, hh t ht x]⟩

lemma sub (hv : HasSchwartzExtension v) (hw : HasSchwartzExtension w) :
    HasSchwartzExtension (fun t x => v t x - w t x) := by
  obtain ⟨g, hg⟩ := hv
  obtain ⟨h, hh⟩ := hw
  exact ⟨g - h, fun t ht x => by simp [hg t ht x, hh t ht x]⟩

lemma sum {ι : Type} (s : Finset ι) {f : ι → Field E}
    (hf : ∀ i ∈ s, HasSchwartzExtension (f i)) :
    HasSchwartzExtension (fun t x => ∑ i ∈ s, f i t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (E := E))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma const_smul (hv : HasSchwartzExtension v) (a : ℝ) :
    HasSchwartzExtension (fun t x => a • v t x) := by
  obtain ⟨g, hg⟩ := hv
  exact ⟨a • g, fun t ht x => by simp [hg t ht x]⟩

lemma postcomp (hv : HasSchwartzExtension v) (L : E →L[ℝ] F) :
    HasSchwartzExtension (fun t x => L (v t x)) := by
  obtain ⟨g, hg⟩ := hv
  exact ⟨SchwartzMap.postcompCLM L g, fun t ht x => by simp [hg t ht x]⟩

lemma spatialD (hv : HasSchwartzExtension v) (i : Fin 3) :
    HasSchwartzExtension (RapidForcing.spatialD i v) := by
  obtain ⟨g, hg⟩ := hv
  refine ⟨LineDeriv.lineDerivOp ((0 : ℝ), basis i) g, ?_⟩
  intro t ht x
  have he : v t = fun y => g (t, y) := funext (hg t ht)
  have hD : HasFDerivAt (fun y : Space => g (t, y))
      ((fderiv ℝ g (t, x)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) x :=
    g.differentiableAt.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change fderiv ℝ (v t) x (basis i) = _
  rw [he, hD.fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

lemma timeD (hv : HasSchwartzExtension v) :
    HasSchwartzExtension (RapidForcing.timeD v) := by
  obtain ⟨g, hg⟩ := hv
  refine ⟨LineDeriv.lineDerivOp ((1 : ℝ), (0 : Space)) g, ?_⟩
  intro t ht x
  have hD : HasDerivAt (fun s : ℝ => g (s, x)) (fderiv ℝ g (t, x) (1, 0)) t :=
    g.differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  change derivWithin (fun s => v s x) (Ici 0) t = _
  rw [derivWithin_congr (s := Ici (0 : ℝ)) (fun s hs => hg s hs x) (hg t ht x),
    hD.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht),
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

lemma spatialD_iterate (hv : HasSchwartzExtension v) (i : Fin 3) (n : ℕ) :
    HasSchwartzExtension ((RapidForcing.spatialD i)^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.spatialD i

lemma timeD_iterate (hv : HasSchwartzExtension v) (n : ℕ) :
    HasSchwartzExtension (RapidForcing.timeD^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.timeD

lemma mixedD (hv : HasSchwartzExtension v) (l : ℕ) (α : MultiIndex) :
    HasSchwartzExtension (RapidForcing.mixedD l α v) :=
  (((hv.spatialD_iterate 2 (α 2)).spatialD_iterate 1 (α 1)).spatialD_iterate 0 (α 0)).timeD_iterate l

lemma rapid (hv : HasSchwartzExtension v) : Rapid v := by
  intro J l α
  obtain ⟨g, hg⟩ := hv.mixedD l α
  let C := 2 ^ J * (Finset.Iic (J, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t ht x
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (J, 0)) (k := J) (n := 0) le_rfl le_rfl g (t, x)
  simp only [norm_iteratedFDeriv_zero] at hb
  rw [hg t ht x]
  calc
    (1 + t) ^ J * ‖g (t, x)‖ ≤ (1 + ‖(t, x)‖) ^ J * ‖g (t, x)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply pow_le_pow_left₀ (by linarith) _
      have hn : t ≤ ‖(t, x)‖ := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using norm_fst_le (t, x)
      linarith
    _ ≤ C := hb
    _ ≤ max 0 C := le_max_right _ _
end General

lemma smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Field ℝ} {w : Field E} (hv : HasSchwartzExtension v) (hw : HasSchwartzExtension w) :
    HasSchwartzExtension (fun t x => v t x • w t x) := by
  obtain ⟨g, hg⟩ := hv
  obtain ⟨h, hh⟩ := hw
  refine ⟨SchwartzMap.pairing (ContinuousLinearMap.lsmul ℝ ℝ) g h, ?_⟩
  intro t ht x
  simp [hg t ht x, hh t ht x]

lemma advection {u : Field Space} (hu : HasSchwartzExtension u) :
    HasSchwartzExtension (RapidForcing.advection u) := by
  apply sum
  intro i _
  exact (hu.postcomp (EuclideanSpace.proj i)).smul (hu.spatialD i)

lemma laplace {u : Field Space} (hu : HasSchwartzExtension u) :
    HasSchwartzExtension (RapidForcing.laplace u) := by
  apply sum
  intro i _
  exact (hu.spatialD i).spatialD i

lemma residual {u : Field Space} (hu : HasSchwartzExtension u) (ν : ℝ) :
    HasSchwartzExtension (RapidForcing.residual ν u) :=
  (hu.timeD.add hu.advection).sub (hu.laplace.const_smul ν)

end HasSchwartzExtension

theorem addressed_fields_rapid (ν : ℝ) (M : Machine) (w : M.Input) :
    Rapid (addressedVelocity M w) ∧ RapidSpaceTime (addressedVelocity M w) ∧
    Rapid (addressedForce ν M w) ∧ RapidSpaceTime (addressedForce ν M w) := by
  have hu : HasSchwartzExtension (addressedVelocity M w) :=
    ⟨addressedSchwartz M w, fun _ _ _ => rfl⟩
  have huR := hu.rapid
  have hfR := (hu.residual ν).rapid
  exact ⟨huR, rapidSpaceTime_of_supported_rapid (addressedVelocity_supported M w) huR,
    hfR, rapidSpaceTime_of_supported_rapid (addressedForce_supported ν M w) hfR⟩

end RapidForcing

end OAI
