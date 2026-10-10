import OAI.MathematicalPhysics.RapidForcing.FieldExpressions

namespace OAI


open scoped BigOperators Topology
open Set Filter
namespace RapidForcing

def EqBefore {E : Type} (R : ℝ) (v w : Field E) : Prop :=
  ∀ t, 0 ≤ t → t < R → ∀ x, v t x = w t x

namespace EqBefore
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {v w : Field E}
lemma spatial (h : EqBefore R v w) (i : Fin 3) : EqBefore R (spatialD i v) (spatialD i w) := by
  intro t ht hR x
  have he : v t = w t := funext (h t ht hR)
  simp only [spatialD, he]
lemma time (h : EqBefore R v w) : EqBefore R (timeD v) (timeD w) := by
  intro t ht hR x
  apply Filter.EventuallyEq.derivWithin_eq_of_mem _ ht
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR)] with s hs hsR
  exact h s hs hsR x
lemma mixed (h : EqBefore R v w) (l : ℕ) (α : MultiIndex) :
    EqBefore R (mixedD l α v) (mixedD l α w) := by
  have hsp (i : Fin 3) (n : ℕ) {a b : Field E} (hab : EqBefore R a b) :
      EqBefore R ((spatialD i)^[n] a) ((spatialD i)^[n] b) := by
    induction n with
    | zero => exact hab
    | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.spatial i
  unfold mixedD spatialMulti
  induction l with
  | zero => exact hsp 0 _ (hsp 1 _ (hsp 2 _ h))
  | succ l ih => simpa only [Function.iterate_succ_apply'] using ih.time
end EqBefore

namespace EffectiveProfile
namespace Formula

noncomputable def pack (ν t : ℝ) (x : Space) : Fin 5 → ℝ := ![t, x 0, x 1, x 2, ν]
def spaceIndex (i : Fin 3) : Fin 5 := ⟨i.val + 1, by omega⟩

noncomputable def scalarField (a : Formula 5) (ν : ℝ) : Field ℝ :=
  fun t x => a.value (pack ν t x)
noncomputable def vectorField (a : Fin 3 → Formula 5) (ν : ℝ) : Field Space :=
  fun t x => WithLp.toLp 2 (fun i => (a i).scalarField ν t x)

lemma pack_smooth (ν : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => pack ν p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pack] <;> fun_prop
lemma scalarField_smooth (a : Formula 5) (ν : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (a.scalarField ν)) :=
  a.contDiff.comp (pack_smooth ν)
lemma vectorField_smooth (a : Fin 3 → Formula 5) (ν : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (vectorField a ν)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact (a i).scalarField_smooth ν

lemma pack_space_line (ν t : ℝ) (x : Space) (i : Fin 3) (s : ℝ) :
    pack ν t (x + s • basis i) = pack ν t x + s • Pi.single (spaceIndex i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [pack, basis, spaceIndex]
lemma pack_time_line (ν t : ℝ) (x : Space) (s : ℝ) :
    pack ν (t + s) x = pack ν t x + s • Pi.single (0 : Fin 5) 1 := by
  ext j
  fin_cases j <;> simp [pack]

lemma spatial_scalarField (a : Formula 5) (ν : ℝ) (i : Fin 3) :
    spatialD i (a.scalarField ν) = (a.diff (spaceIndex i)).scalarField ν := by
  funext t x
  have hline : HasDerivAt (fun s : ℝ => x + s • basis i) (basis i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basis i)).const_add x
  have hd : DifferentiableAt ℝ (a.scalarField ν t) x :=
    ((a.scalarField_smooth ν).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
  have hp := a.hasDerivAt_line (spaceIndex i) (pack ν t x) 0
  have he : (fun s : ℝ => a.value (pack ν t x + s • Pi.single (spaceIndex i) (1 : ℝ))) =
      fun s => a.scalarField ν t (x + s • basis i) := by
    funext s
    rw [← pack_space_line]
    rfl
  rw [he] at hp
  have hd' : HasFDerivAt (a.scalarField ν t) (fderiv ℝ (a.scalarField ν t) x)
      (x + (0 : ℝ) • basis i) := by simpa using hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero, spatialD, scalarField] using hc.unique hp

lemma time_scalarField (a : Formula 5) (ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeD (a.scalarField ν) t x = (a.diff 0).scalarField ν t x := by
  have h := a.hasDerivAt_line 0 (pack ν 0 x) t
  have he : (fun s => a.value (pack ν 0 x + s • Pi.single 0 1)) =
      fun s => a.scalarField ν s x := by
    funext s
    rw [← pack_time_line, zero_add]
    rfl
  rw [he, ← pack_time_line, zero_add] at h
  exact h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)

lemma spatial_vectorField (a : Fin 3 → Formula 5) (ν : ℝ) (i : Fin 3) :
    spatialD i (vectorField a ν) = vectorField (fun j => (a j).diff (spaceIndex i)) ν := by
  funext t x
  ext j
  have hd : DifferentiableAt ℝ (vectorField a ν t) x :=
    ((vectorField_smooth a ν).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
  change (fderiv ℝ (vectorField a ν t) x (basis i)) j = _
  rw [← fderiv_coordinate hd]
  exact congrFun (congrFun (spatial_scalarField (a j) ν i) t) x

lemma time_vectorField (a : Fin 3 → Formula 5) (ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    timeD (vectorField a ν) t x = vectorField (fun j => (a j).diff 0) ν t x := by
  have hd : HasDerivAt (fun s => vectorField a ν s x)
      (vectorField (fun j => (a j).diff 0) ν t x) t := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    apply hasDerivAt_pi.mpr
    intro j
    have h := (a j).hasDerivAt_line 0 (pack ν 0 x) t
    have he : (fun s => (a j).value (pack ν 0 x + s • Pi.single 0 1)) =
        fun s => (a j).scalarField ν s x := by
      funext s
      rw [← pack_time_line, zero_add]
      rfl
    rw [he, ← pack_time_line, zero_add] at h
    exact h
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)

def mixed (l : ℕ) (α : MultiIndex) (a : Formula 5) : Formula 5 :=
  (diff 0)^[l] ((diff (spaceIndex 0))^[α 0]
    ((diff (spaceIndex 1))^[α 1] ((diff (spaceIndex 2))^[α 2] a)))

lemma mixed_vectorField (a : Fin 3 → Formula 5) (ν : ℝ) (l : ℕ) (α : MultiIndex)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixedD l α (vectorField a ν) t x = vectorField (fun j => (a j).mixed l α) ν t x := by
  have hsp (i : Fin 3) (n : ℕ) (a : Fin 3 → Formula 5) :
      (spatialD i)^[n] (vectorField a ν) = vectorField (fun j => (diff (spaceIndex i))^[n] (a j)) ν := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, spatial_vectorField]
  have htime (n : ℕ) (a : Fin 3 → Formula 5) :
      ∀ s, 0 ≤ s → ∀ y, (timeD)^[n] (vectorField a ν) s y =
        vectorField (fun j => (diff 0)^[n] (a j)) ν s y := by
    induction n with
    | zero => intro s _ y; rfl
    | succ n ih =>
      intro s hs y
      rw [Function.iterate_succ_apply']
      have he : (fun r => (timeD)^[n] (vectorField a ν) r y) =ᶠ[𝓝[Ici 0] s]
          fun r => vectorField (fun j => (diff 0)^[n] (a j)) ν r y := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact ih r hr y
      rw [timeD, he.derivWithin_eq_of_mem hs, ← timeD,
        time_vectorField _ _ _ hs]
      simp only [Function.iterate_succ_apply']
  unfold mixedD spatialMulti mixed
  rw [hsp, hsp, hsp]
  exact htime l _ t ht x

end Formula
end EffectiveProfile
end RapidForcing

end OAI
