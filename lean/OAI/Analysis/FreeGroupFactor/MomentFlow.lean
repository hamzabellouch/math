import OAI.Analysis.FreeGroupFactor.Operators

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

instance groupVN_normedSpaceReal (G : Type uG) [Group G] :
    NormedSpace ℝ (groupVonNeumann G) :=
  NormedSpace.restrictScalars ℝ ℂ (groupVonNeumann G)

 instance groupHilbert_nontrivial (G : Type uG) [Group G] : Nontrivial (GroupHilbert G) := by
  classical
  apply nontrivial_of_ne (lp.single 2 (1 : G) (1 : ℂ)) 0
  intro he
  have hh := congrArg (fun x : GroupHilbert G => x 1) he
  simp at hh

 instance groupVN_normOneClass (G : Type uG) [Group G] : NormOneClass (groupVonNeumann G) where
  norm_one := by
    change ‖(1 : GroupOperator G)‖ = 1
    exact norm_one

 def groupUnitaryHom (G : Type uG) [Group G] : G →* groupVonNeumann G where
  toFun := groupUnitary
  map_one' := Subtype.ext (leftRegular_one)
  map_mul' g b := Subtype.ext (leftRegular_mul g b)

 def groupAlgebraEvaluation (G : Type uG) [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] groupVonNeumann G :=
  MonoidAlgebra.lift ℂ (groupVonNeumann G) G (groupUnitaryHom G)

 @[simp] theorem groupAlgebraEvaluation_of {G : Type uG} [Group G] (g : G) :
    groupAlgebraEvaluation G (MonoidAlgebra.of ℂ G g) = groupUnitary g := by
  simp [groupAlgebraEvaluation, groupUnitaryHom]

 theorem canonicalTrace_groupAlgebraEvaluation {G : Type uG} [Group G] [DecidableEq G]
    (p : MonoidAlgebra ℂ G) : canonicalTrace (groupAlgebraEvaluation G p) = p.coeff 1 := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    rw [groupAlgebraEvaluation_of, canonicalTrace_groupUnitary]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  | add p q hp hq =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (p + q)) = _
    simp only [map_add, canonicalTraceCLM_apply, hp, hq, MonoidAlgebra.coeff_add,
      Finsupp.add_apply]
  | smul c p hp =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (c • p)) = _
    simp only [map_smul, canonicalTraceCLM_apply, hp, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply]

 theorem canonicalTrace_eval {ι : Type uι} [DecidableEq ι]
    (p : NCPolynomial.Expr (ι × Bool)) :
    canonicalTrace (NCPolynomial.eval (fun ib => groupUnitary (AlgebraPolynomial.signed ib)) p) =
      (NCPolynomial.eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι)
        (AlgebraPolynomial.signed ib)) p).coeff 1 := by
  rw [← canonicalTrace_groupAlgebraEvaluation]
  congr 1
  rw [AlgebraPolynomial.map_eval]
  congr 1
  funext ib
  exact (groupAlgebraEvaluation_of _).symm

theorem source_laurent_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  let J := Finset.univ.sup (fun ib => NCPolynomial.degree (V ib))
  let B := ∑ ib, NCPolynomial.mass (V ib)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => NCPolynomial.mass_nonneg _
  have hdeg (ib) : NCPolynomial.degree (V ib) ≤ J + 1 := by
    exact (Finset.le_sup (f := fun ib => NCPolynomial.degree (V ib))
      (Finset.mem_univ ib)).trans (Nat.le_succ _)
  have hmass (ib) : NCPolynomial.mass (V ib) ≤ B :=
    Finset.single_le_sum (fun i _ => NCPolynomial.mass_nonneg (V i)) (Finset.mem_univ ib)
  have hinitial (q) : canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q)) = 0 := by
    have hinit : Y 0 = fun ib => groupUnitary (AlgebraPolynomial.signed ib) := funext hY₀
    rw [hinit, canonicalTrace_eval]
    exact AlgebraPolynomial.encoded_initial_trace h l q
  have hreal (L : ℂ →L[ℝ] ℝ) :
      L (canonicalTrace (NCPolynomial.eval (Y t) p)) =
      L (canonicalTrace (NCPolynomial.eval (Y 0) p)) := by
    let Lt := L.comp ((canonicalTraceCLM (G := FreeGroup (Option ι))).restrictScalars ℝ)
    apply NCPolynomial.polynomial_moments Y V Lt hsmooth hODE 1 le_rfl hbounded
      J B hB hdeg hmass
    intro q
    change L (canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q))) = 0
    rw [hinitial, map_zero]
  exact Complex.ext (hreal Complex.reCLM) (hreal Complex.imCLM)

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem norm_signedTrajectory_le_one [Nontrivial A]
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) :
    ‖signedTrajectory X hU C t ib‖ ≤ 1 := by
  change ‖((FreeGroup.lift (extendUnitary (fun j => ⟨X t j, hU t j⟩) C)
    (AlgebraPolynomial.signed ib) : unitary A) : A)‖ ≤ 1
  exact (CStarRing.norm_of_mem_unitary (Subtype.property _)).le

 theorem smooth_signedTrajectory [Fintype ι]
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (hs : ContDiff ℝ ∞ X) (ib : Option ι × Bool) :
    ContDiff ℝ ∞ (fun t => signedTrajectory X hU C t ib) := by
  rcases ib with ⟨i,b⟩
  cases i with
  | none => cases b <;>
      simp only [signedTrajectory_none_pos, signedTrajectory_none_neg] <;> exact contDiff_const
  | some j => cases b
              · simp only [signedTrajectory_some_neg]
                exact (starL ℝ (A := A)).contDiff.comp ((contDiff_apply ℝ A j).comp hs)
              · simp only [signedTrajectory_some_pos]
                exact (contDiff_apply ℝ A j).comp hs
end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem groupUnitary_mem_unitary {G : Type uG} [Group G] (g : G) :
    groupUnitary g ∈ unitary (groupVonNeumann G) := by
  rw [Unitary.mem_iff]
  constructor <;> apply Subtype.ext
  · exact (Unitary.mem_iff.mp (leftRegular_unitary g)).1
  · exact (Unitary.mem_iff.mp (leftRegular_unitary g)).2

 def generatorUnitary {ι : Type uι} (i : ι) : unitary (groupVonNeumann (FreeGroup ι)) :=
  ⟨groupUnitary (FreeGroup.of i), groupUnitary_mem_unitary _⟩

 theorem wordHom_generatorUnitary {ι : Type uι} (g : FreeGroup ι) :
    UnitaryEvaluation.wordHom generatorUnitary g = groupUnitary g := by
  have he : UnitaryEvaluation.wordHom (generatorUnitary (ι := ι)) =
      groupUnitaryHom (FreeGroup ι) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  exact DFunLike.congr_fun he g

 theorem laurent_flow_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) :
    ∀ t (g : FreeGroup (Option ι)),
      canonicalTrace (UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
          (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let C : unitary (groupVonNeumann (FreeGroup (Option ι))) := generatorUnitary none
  let S := UnitaryEvaluation.laurentValue C l
  let Y := UnitaryEvaluation.signedTrajectory X hU C
  have hu0 : UnitaryEvaluation.extendUnitary (fun j => ⟨X 0 j, hU 0 j⟩) C =
      generatorUnitary := by
    funext i
    cases i with
    | none => rfl
    | some j => apply Subtype.ext; exact congrFun hX₀ j
  have hY₀ (ib) : Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib) := by
    dsimp [Y, UnitaryEvaluation.signedTrajectory]
    rw [hu0, wordHom_generatorUnitary]
  have hsmooth (ib) : ContDiff ℝ ∞ (fun t => Y t ib) :=
    UnitaryEvaluation.smooth_signedTrajectory X hU C
      (PolynomialFlow.smooth_solution S h X hX) ib
  have hbounded (t ib) : ‖Y t ib‖ ≤ 1 :=
    UnitaryEvaluation.norm_signedTrajectory_le_one X hU C t ib
  intro t g
  let p := AlgebraPolynomial.encode (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)
  have hmoment := source_laurent_moments h l Y hY₀ hsmooth hbounded
    (UnitaryEvaluation.signedTrajectory_ode C h l hS X hU hX) p t
  have he (s) : NCPolynomial.eval (Y s) p =
      UnitaryEvaluation.wordHom
        (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C) g := by
    change NCPolynomial.eval (fun ib => UnitaryEvaluation.wordHom
      (UnitaryEvaluation.extendUnitary (fun j => ⟨X s j, hU s j⟩) C)
        (AlgebraPolynomial.signed ib)) (AlgebraPolynomial.encode
          (MonoidAlgebra.of ℂ (FreeGroup (Option ι)) g)) = _
    rw [UnitaryEvaluation.eval_encode, UnitaryEvaluation.algebraHom_of]
  rw [he, he, hu0, wordHom_generatorUnitary, canonicalTrace_groupUnitary] at hmoment
  exact hmoment

 theorem actual_laurent_flow_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l)) :
    ∃ (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
      (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι)))),
      X 0 = (fun j => groupUnitary (FreeGroup.of (some j))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) ∧
      ∀ t (g : FreeGroup (Option ι)),
        canonicalTrace (UnitaryEvaluation.wordHom
          (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
            (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  classical
  let C : unitary (groupVonNeumann (FreeGroup (Option ι))) := generatorUnitary none
  let S := UnitaryEvaluation.laurentValue C l
  obtain ⟨X, hX₀, hX, hU⟩ := PolynomialFlow.global_unitary_solution S hS h
    (fun j => groupUnitary (FreeGroup.of (some j))) (fun j => groupUnitary_mem_unitary _)
  refine ⟨X,hU,hX₀,hX,?_⟩
  exact laurent_flow_moments h l hS X hU hX₀ hX

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Nontrivial A] [Fintype ι] [DecidableEq ι] in
theorem coe_wordList (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (w : List (ι × Bool)) (X : ι → E) :
    ((wordList w X : E) : A) = wordList w (fun i => (X i : A)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b <;> simpa [wordList] using
      congrArg (fun z : A => _ * z) ih

omit [Nontrivial A] [Fintype ι] in
theorem coe_field (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (S : E)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → E) (j : ι) :
    ((field S h X j : E) : A) = field (S : A) h (fun i => (X i : A)) j := by
  classical
  simp [field, hamiltonian, Finsupp.sum, word, coe_wordList]

theorem solution_mem_subalgebra (E : StarSubalgebra ℂ A) (hE : IsClosed (E : Set A))
    (S : A) (hS : IsSelfAdjoint S) (hSE : S ∈ E) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hU : ∀ t j, X t j ∈ unitary A) (t₀ : ℝ) (h₀ : ∀ j, X t₀ j ∈ E) :
    ∀ t j, X t j ∈ E := by
  let : IsClosed (E : Set A) := hE
  let S' : E := ⟨S, hSE⟩
  let V : ι → E := fun j => ⟨X t₀ j, h₀ j⟩
  have hS' : IsSelfAdjoint S' := Subtype.ext hS
  have hV : ∀ j, V j ∈ unitary E := by
    intro j
    rw [Unitary.mem_iff]
    exact ⟨Subtype.ext (hU t₀ j).1, Subtype.ext (hU t₀ j).2⟩
  obtain ⟨Y, hY₀, hY, hUY⟩ := global_unitary_solution S' hS' h V hV
  let L : (ι → E) →L[ℝ] (ι → A) :=
    ContinuousLinearMap.pi fun j =>
      (E.toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ).comp
        (ContinuousLinearMap.proj j)
  let Z : ℝ → ι → A := fun t => L (Y (t - t₀))
  have hZ : ∀ t, HasDerivAt Z (field S h (Z t)) t := by
    intro t
    have hd := (hY (t - t₀)).scomp t ((hasDerivAt_id t).sub_const t₀)
    have hm := L.hasFDerivAt.comp_hasDerivAt t hd
    have hm' : HasDerivAt Z (L (field S' h (Y (t - t₀)))) t := by
      simpa only [Function.comp_def, id_eq, one_smul, Z] using hm
    have hf : L (field S' h (Y (t - t₀))) = field S h (Z t) := by
      ext j
      exact coe_field E S' h (Y (t - t₀)) j
    rw [hf] at hm'
    exact hm'
  have hUZ : ∀ t j, Z t j ∈ unitary A := by
    intro t j
    exact ⟨congrArg Subtype.val (hUY (t - t₀) j).1,
      congrArg Subtype.val (hUY (t - t₀) j).2⟩
  have heq : X = Z := unitary_solutions_unique S h X Z hX hZ hU hUZ t₀ (by
    ext j
    change X t₀ j = ((Y (t₀ - t₀) j : E) : A)
    rw [sub_self, hY₀])
  intro t j
  rw [heq]
  exact (Y (t - t₀) j).property

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
