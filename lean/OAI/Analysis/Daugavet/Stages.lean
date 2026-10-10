import OAI.Analysis.Daugavet.MeasureDistance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

/-- One finite-coordinate stage of the construction. -/
structure ConstructionStage where
  space : Submodule ℝ KWL1
  finiteDimensional : FiniteDimensional ℝ space
  finiteCoordinates : FiniteCoordinates space
  nonzero : space ≠ ⊥

/-- All estimates propagated from one stage to the next. -/
structure StepEstimates (G H : Submodule ℝ KWL1) (h : ℝ) : Prop where
  proper : G < H
  wholeBall : ∀ g ∈ H, ‖g‖ ≤ 1 →
    ∃ ψ ∈ G, ‖ψ‖ ≤ 1 ∧ measureDistance kwMeasure g ψ ≤ h
  averages : ∀ u ∈ G, ‖u‖ = 1 → ∃ n : ℕ, 0 < n ∧ ∃ v : Fin n → KWL1,
    (∀ j, v j ∈ H ∧ ‖v j‖ = 1) ∧
    ‖u - (n : ℝ)⁻¹ • ∑ j, v j‖ ≤ 2 * h ∧
    ∀ w ∈ G, ‖w‖ = 1 → ∀ j, 2 - h ≤ ‖w + v j‖

lemma stage_enlargement (G : ConstructionStage) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    ∃ H : ConstructionStage, StepEstimates G.space H.space h := by
  classical
  let : FiniteDimensional ℝ G.space := G.finiteDimensional
  let : Nontrivial G.space := Submodule.nontrivial_iff_ne_bot.mpr G.nonzero
  obtain ⟨t, hts, htfin, hcover⟩ := (isCompact_sphere (0 : G.space) 1).finite_cover_balls hh
  have hex : ∃ z : G.space, ‖z‖ = 1 := exists_norm_eq G.space (by norm_num : (0:ℝ) ≤ 1)
  have htne : t.Nonempty := by
    obtain ⟨z,hz⟩ := hex
    have hzcover := hcover (show z ∈ Metric.sphere (0:G.space) 1 by simpa using hz)
    simp only [Set.mem_iUnion] at hzcover
    obtain ⟨b,hb,_⟩ := hzcover
    exact ⟨b,hb⟩
  let : Fintype t := htfin.fintype
  let : Nonempty t := htne.to_subtype
  let u : t → G.space := fun z => z.val
  have hu (z : t) : ‖u z‖ = 1 := by simpa [u] using hts z.property
  obtain ⟨A⟩ := finite_dimensional_enlargement G.space G.nonzero G.finiteCoordinates u hu hh hh1
  have hproper : G.space < A.space := by
    apply lt_of_le_of_ne A.contains
    intro heq
    let k : t := Classical.choice inferInstance
    let j : Fin A.copies := ⟨0,A.copies_pos⟩
    have hv : A.vectors k j ∈ G.space := by simpa only [heq] using A.vectors_mem k j
    have hhfar := A.additive (-A.vectors k j) (G.space.neg_mem hv)
      (by simpa using A.vectors_unit k j) k j
    simp only [neg_add_cancel, norm_zero] at hhfar
    linarith
  let H : ConstructionStage := ⟨A.space, A.finiteDimensional, A.finiteCoordinates,
    ne_bot_of_gt hproper⟩
  refine ⟨H, ⟨hproper, A.wholeBall, ?_⟩⟩
  intro x hx hxu
  have hxcover := hcover (show (⟨x,hx⟩ : G.space) ∈ Metric.sphere 0 1 by simpa using hxu)
  simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hxcover
  obtain ⟨b,hb,hxb⟩ := hxcover
  let k : t := ⟨b,hb⟩
  refine ⟨A.copies, A.copies_pos, A.vectors k, fun j => ⟨A.vectors_mem k j, A.vectors_unit k j⟩, ?_, ?_⟩
  · have ha := A.averages k
    have hxb' : ‖x - (u k : KWL1)‖ < h := hxb
    calc
      _ ≤ ‖x - (u k : KWL1)‖ + ‖(u k : KWL1) - (A.copies : ℝ)⁻¹ • ∑ j, A.vectors k j‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * h := by linarith
  · exact fun w hw hw1 j => A.additive w hw hw1 k j

/-- The constant-one vector, so the initial stage is literally span{1}. -/
def oneVector : KWL1 := Lp.const 1 kwMeasure (1:ℝ)

lemma oneVector_norm : ‖oneVector‖ = 1 := by
  simp [oneVector, Lp.norm_const]

lemma oneVector_finiteCoordinates : FiniteCoordinates (Submodule.span ℝ {oneVector}) := by
  let c : Fin 0 → ℕ := Fin.elim0
  have hc : Function.Injective c := fun i => Fin.elim0 i
  refine ⟨Fin 0, inferInstance, c, hc, Submodule.span_le.mpr ?_⟩
  intro x hx
  have hx' : x = oneVector := Set.mem_singleton_iff.mp hx
  subst x
  refine ⟨Lp.const 1 (cubeMeasure (Fin 0)) (1:ℝ), ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.const 1 (cubeMeasure (Fin 0)) (1:ℝ))
      (finite_coordinates_mp c hc),
    (finite_coordinates_mp c hc).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_const 1 (cubeMeasure (Fin 0)) (1:ℝ)),
    Lp.coeFn_const 1 kwMeasure (1:ℝ)] with ω hω hω' hω''
  exact hω.trans (hω'.trans hω''.symm)

def initialStage : ConstructionStage where
  space := Submodule.span ℝ {oneVector}
  finiteDimensional := inferInstance
  finiteCoordinates := oneVector_finiteCoordinates
  nonzero := by
    intro heq
    have hmem : oneVector ∈ (⊥ : Submodule ℝ KWL1) := heq ▸ Submodule.subset_span (Set.mem_singleton oneVector)
    have hz : oneVector = 0 := hmem
    have hn := oneVector_norm
    rw [hz, norm_zero] at hn
    norm_num at hn

def stageError (n : ℕ) : ℝ := (1/2)^(n+1)

lemma stageError_pos (n : ℕ) : 0 < stageError n := by unfold stageError; positivity

lemma stageError_lt_one (n : ℕ) : stageError n < 1 := by
  unfold stageError
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

lemma stageError_succ (n : ℕ) : 2 * stageError (n+1) = stageError n := by
  simp only [stageError, pow_succ]
  ring

def nextStage (n : ℕ) (G : ConstructionStage) : ConstructionStage :=
  Classical.choose (stage_enlargement G (stageError_pos n) (stageError_lt_one n))

lemma nextStage_estimates (n : ℕ) (G : ConstructionStage) :
    StepEstimates G.space (nextStage n G).space (stageError n) :=
  Classical.choose_spec (stage_enlargement G (stageError_pos n) (stageError_lt_one n))

def stages : ℕ → ConstructionStage
  | 0 => initialStage
  | n+1 => nextStage n (stages n)

def stageSpace (n : ℕ) : Submodule ℝ KWL1 := (stages n).space

instance stageSpace_finite (n : ℕ) : FiniteDimensional ℝ (stageSpace n) :=
  (stages n).finiteDimensional

lemma stageSpace_nonzero (n : ℕ) : stageSpace n ≠ ⊥ := (stages n).nonzero

lemma step_estimates (n : ℕ) : StepEstimates (stageSpace n) (stageSpace (n+1)) (stageError n) :=
  nextStage_estimates n (stages n)

lemma stageSpace_strictMono : StrictMono stageSpace :=
  strictMono_nat_of_lt_succ (fun n => (step_estimates n).proper)

lemma stageSpace_mono : Monotone stageSpace := stageSpace_strictMono.monotone

def unionSpace : Submodule ℝ KWL1 := ⨆ n, stageSpace n

def constructedSpace : Submodule ℝ KWL1 := unionSpace.topologicalClosure

lemma stageSpace_le_constructed (n : ℕ) : stageSpace n ≤ constructedSpace :=
  (le_iSup stageSpace n).trans unionSpace.le_topologicalClosure

lemma constructedSpace_closed : IsClosed (constructedSpace : Set KWL1) :=
  unionSpace.isClosed_topologicalClosure

lemma constructedSpace_nonzero : constructedSpace ≠ ⊥ :=
  ne_bot_of_le_ne_bot (stageSpace_nonzero 0) (stageSpace_le_constructed 0)

end ExactModuli.KW

end

end OAI
