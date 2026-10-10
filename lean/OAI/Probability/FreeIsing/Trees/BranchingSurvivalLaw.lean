import OAI.Probability.FreeIsing.Estimates.LabelDecomposition

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.BranchingSurvival

abbrev Labels (b : ℕ) := List (Fin b) → ℝ

def wordMeasure (b : ℕ) : Measure (Labels b) :=
  Measure.infinitePi (fun _ => uniform01)

instance wordMeasure_probability (b : ℕ) : IsProbabilityMeasure (wordMeasure b) := by
  unfold wordMeasure
  infer_instance

def branches {b : ℕ} (U : Labels b) (i : Fin b) : Labels b := fun w => U (i :: w)

lemma measurable_branches (b : ℕ) : Measurable (@branches b) := by
  unfold branches
  fun_prop

lemma map_branches (b : ℕ) :
    (wordMeasure b).map branches =
      Measure.infinitePi (fun _ : Fin b => wordMeasure b) := by
  have hinj : Function.Injective (fun p : Fin b × List (Fin b) => p.1 :: p.2) := by
    rintro ⟨i, w⟩ ⟨j, z⟩ h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  calc
    _ = ((wordMeasure b).map
        (fun U (p : Fin b × List (Fin b)) => U (p.1 :: p.2))).map
          (MeasurableEquiv.curry (Fin b) (List (Fin b)) ℝ) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      unfold wordMeasure
      rw [Measure.map_infinitePi_infinitePi_of_inj hinj]
      exact Measure.infinitePi_map_curry (fun (_ : Fin b) (_ : List (Fin b)) => uniform01)

lemma indepFun_root_branches (b : ℕ) :
    IndepFun (fun U : Labels b => U []) branches (wordMeasure b) := by
  have h := LabelDecomposition.indepFun_coordinate_rest
    (fun _ : List (Fin b) => uniform01) []
  let F : ({w : List (Fin b) // w ≠ []} → ℝ) → (Fin b → Labels b) :=
    fun Y i w => Y ⟨i :: w, List.cons_ne_nil _ _⟩
  have hF : Measurable F := by fun_prop
  exact h.comp measurable_id hF

lemma map_root_branches (b : ℕ) :
    (wordMeasure b).map (fun U => (U [], branches U)) =
      uniform01.prod (Measure.infinitePi (fun _ : Fin b => wordMeasure b)) := by
  rw [(indepFun_root_branches b).map_prod_eq_prod_map_map
    (measurable_pi_apply []).aemeasurable (measurable_branches b).aemeasurable,
    map_branches]
  congr 1
  exact Measure.infinitePi_map_eval (fun _ : List (Fin b) => uniform01) []

def survives {b : ℕ} (p : ℝ) : ℕ → Set (Labels b)
  | 0 => Set.univ
  | n + 1 => {U | ∃ i : Fin b, U [i] ≤ p ∧ branches U i ∈ survives p n}

def live {b : ℕ} (p : ℝ) (n : ℕ) : Set (Labels b) :=
  {U | U [] ≤ p} ∩ survives p n

lemma measurableSet_survives (b : ℕ) (p : ℝ) (n : ℕ) :
    MeasurableSet (@survives b p n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
      change MeasurableSet {U : Labels b | ∃ i : Fin b,
        U [i] ≤ p ∧ branches U i ∈ survives p n}
      simp only [Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro i
      exact (measurableSet_le (measurable_pi_apply [i]) measurable_const).inter
        (ih.preimage (by unfold branches; fun_prop))

lemma measurableSet_live (b : ℕ) (p : ℝ) (n : ℕ) :
    MeasurableSet (@live b p n) :=
  (measurableSet_le (measurable_pi_apply []) measurable_const).inter
    (measurableSet_survives b p n)

def anyLive {b : ℕ} (p : ℝ) (n : ℕ) : Set (Fin b → Labels b) :=
  {Y | ∃ i, Y i ∈ live p n}

lemma measurableSet_anyLive (b : ℕ) (p : ℝ) (n : ℕ) :
    MeasurableSet (@anyLive b p n) := by
  unfold anyLive
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun i =>
    (measurableSet_live b p n).preimage (measurable_pi_apply i))

lemma survives_succ_eq_preimage {b : ℕ} (p : ℝ) (n : ℕ) :
    survives (b := b) p (n + 1) = branches ⁻¹' anyLive p n := by
  ext U
  simp [survives, anyLive, live, branches]

lemma uniform01_Iic {p : ℝ} (hp : p ≤ 1) : uniform01 (Set.Iic p) = ENNReal.ofReal p := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iic]
  have heq : Set.Iic p ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hup, hu0, _⟩ => ⟨hu0, hup⟩,
      fun ⟨hu0, hup⟩ => ⟨hup, hu0, hup.trans hp⟩⟩
  rw [heq, Real.volume_Icc, sub_zero]

lemma root_open_mass (b : ℕ) {p : ℝ} (hp : p ≤ 1) :
    wordMeasure b {U | U [] ≤ p} = ENNReal.ofReal p := by
  have hmap := Measure.infinitePi_map_eval (fun _ : List (Fin b) => uniform01) []
  have h := congrArg (fun μ : Measure ℝ => μ (Set.Iic p)) hmap
  rw [Measure.map_apply (measurable_pi_apply []) measurableSet_Iic] at h
  exact h.trans (uniform01_Iic hp)

theorem live_mass (b : ℕ) {p : ℝ} (hp : p ≤ 1) (n : ℕ) :
    wordMeasure b (live p n) =
      ENNReal.ofReal p * wordMeasure b (survives p n) := by
  cases n with
  | zero => simpa [live, survives] using root_open_mass b hp
  | succ n =>
      change wordMeasure b ((fun U : Labels b => U []) ⁻¹' Set.Iic p ∩
        survives p (n + 1)) = _
      rw [survives_succ_eq_preimage,
        (indepFun_root_branches b).measure_inter_preimage_eq_mul
          (Set.Iic p) (anyLive p n) measurableSet_Iic (measurableSet_anyLive b p n)]
      congr 1
      exact root_open_mass b hp

theorem survives_succ_compl_mass (b : ℕ) (p : ℝ) (n : ℕ) :
    wordMeasure b (survives p (n + 1))ᶜ =
      (wordMeasure b (live p n)ᶜ) ^ b := by
  have hpre : (survives (b := b) p (n + 1))ᶜ =
      branches ⁻¹' (Set.univ.pi (fun _ : Fin b => (live p n)ᶜ)) := by
    ext U
    simp [survives, live, branches, Set.mem_pi]
  rw [hpre, ← Measure.map_apply (measurable_branches b)
    (MeasurableSet.univ_pi (fun _ => (measurableSet_live b p n).compl)),
    map_branches, Measure.infinitePi_eq_pi, Measure.pi_pi]
  simp

def probability (b : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (wordMeasure b).real (survives p n)

@[simp] theorem probability_zero (b : ℕ) (p : ℝ) : probability b p 0 = 1 := by
  simp [probability, survives]

lemma probability_nonneg (b : ℕ) (p : ℝ) (n : ℕ) : 0 ≤ probability b p n :=
  measureReal_nonneg

lemma probability_le_one (b : ℕ) (p : ℝ) (n : ℕ) : probability b p n ≤ 1 :=
  measureReal_le_one

theorem probability_succ (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    probability b p (n + 1) = 1 - (1 - p * probability b p n) ^ b := by
  have hlive : (wordMeasure b).real (live p n) = p * probability b p n := by
    unfold Measure.real probability
    rw [live_mass b hp1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0]
    rfl
  have h := congrArg ENNReal.toReal (survives_succ_compl_mass b p n)
  rw [ENNReal.toReal_pow] at h
  change (wordMeasure b).real (survives p (n + 1))ᶜ =
    ((wordMeasure b).real (live p n)ᶜ) ^ b at h
  rw [probReal_compl_eq_one_sub (measurableSet_survives b p (n + 1)),
    probReal_compl_eq_one_sub (measurableSet_live b p n), hlive] at h
  change 1 - probability b p (n + 1) = _ at h
  linarith

end Problem367.BranchingSurvival

end

end OAI
