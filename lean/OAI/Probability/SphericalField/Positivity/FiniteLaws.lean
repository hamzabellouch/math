import Mathlib
import OAI.Probability.SphericalField.Control.FiniteValue

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma finiteFiberRow_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c})
    (n : ℕ) (hn : 1 ≤ n)
    (hblock : μ.map (finiteBlock n) = ν.map (finiteBlock n))
    (A : FiniteBlock L n) : finiteFiberRow μ n A = finiteFiberRow ν n A := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he : MeasurableSet {R : FiniteOverlap L | finiteBlock n R = A} :=
    (finiteBlock_measurable n) (measurableSet_singleton A)
  have hbase : μ.real {R | finiteBlock n R = A} = ν.real {R | finiteBlock n R = A} := by
    have hh := congrArg (fun ρ : Measure (FiniteBlock L n) => ρ.real {A}) hblock
    simpa only [measureReal_def,Measure.map_apply (finiteBlock_measurable n)
      (measurableSet_singleton A),Set.preimage,Set.mem_singleton_iff] using hh
  have hprev (i j : Fin n) (c : L) :
      μ.real {R | finiteBlock n R = A ∧ R i j = c} =
      ν.real {R | finiteBlock n R = A ∧ R i j = c} := by
    have hset : {R : FiniteOverlap L | finiteBlock n R = A ∧ R i j = c} =
        if A i j = c then {R | finiteBlock n R = A} else ∅ := by
      ext R
      by_cases hA : A i j = c
      · simp only [hA,ite_true,mem_ofPred_eq,and_iff_left_iff_imp]
        intro hR
        exact (congrFun (congrFun hR i) j).trans hA
      · simp only [hA,ite_false,mem_empty_iff_false,mem_ofPred_eq,iff_false,not_and]
        intro hR hh
        exact hA ((congrFun (congrFun hR i) j).symm.trans hh)
    rw [hset]
    split_ifs
    · exact hbase
    · simp
  have hrow (ρ : Measure (FiniteOverlap L))
      (hρ : ∀ᵐ R ∂ρ, (∀ i j, R i j = R j i) ∧
        ∀ i j k, min (R i j) (R i k) ≤ R j k) :
      ∀ᵐ v ∂finiteFiberRow ρ n A, ∀ i j,
        min (v i) (A i j) ≤ v j ∧ min (v i) (v j) ≤ A i j := by
    rw [finiteFiberRow,ae_map_iff (finiteRow_measurable n).aemeasurable (Set.to_countable _).measurableSet]
    apply (ae_restrict_iff' he).mpr
    filter_upwards [hρ] with R hR hRA
    intro i j
    have hij : R i j = A i j := congrFun (congrFun hRA i) j
    dsimp [finiteRow]
    constructor
    · simpa only [← hij,hR.1 n (j : ℕ)] using hR.2 (i : ℕ) n (j : ℕ)
    · simpa only [hR.1 n (i : ℕ),hR.1 n (j : ℕ),hij] using hR.2 n (i : ℕ) (j : ℕ)
  let : IsFiniteMeasure (μ.restrict {R | finiteBlock n R = A}) := inferInstance
  let : IsFiniteMeasure (ν.restrict {R | finiteBlock n R = A}) := inferInstance
  have : IsFiniteMeasure (finiteFiberRow μ n A) := by unfold finiteFiberRow; infer_instance
  have : IsFiniteMeasure (finiteFiberRow ν n A) := by unfold finiteFiberRow; infer_instance
  apply finite_ultrametric_row_law_unique A _ _ (hrow μ hμ) (hrow ν hν)
  intro i c
  rw [finiteFiberRow_real,finiteFiberRow_real,hGGμ n hn i A c,hGGν n hn i A c,hbase,hpair]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hprev i j c

lemma map_pair_eq_of_fiber_map_eq
    {Ω X Y : Type*} [MeasurableSpace Ω] [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ ν : Measure Ω) (a : Ω → X) (v : Ω → Y)
    (ha : Measurable a) (hv : Measurable v)
    (h : ∀ x, (μ.restrict {ω | a ω = x}).map v =
      (ν.restrict {ω | a ω = x}).map v) :
    μ.map (fun ω => (a ω,v ω)) = ν.map (fun ω => (a ω,v ω)) := by
  apply Measure.ext_of_singleton
  intro p
  have hh := congrArg (fun ρ : Measure Y => ρ {p.2}) (h p.1)
  rw [Measure.map_apply hv (measurableSet_singleton _),
    Measure.map_apply hv (measurableSet_singleton _),
    Measure.restrict_apply (hv (measurableSet_singleton _)),
    Measure.restrict_apply (hv (measurableSet_singleton _))] at hh
  rw [Measure.map_apply (ha.prodMk hv) (measurableSet_singleton _),
    Measure.map_apply (ha.prodMk hv) (measurableSet_singleton _)]
  convert hh using 1 <;> congr 1 <;> ext ω <;> simp [and_comm,Prod.ext_iff]

def finiteExtension {L : Type*} (d : L) {n : ℕ}
    (p : FiniteBlock L n × (Fin n → L)) : FiniteBlock L (n+1) :=
  fun i j => Fin.lastCases (Fin.lastCases d p.2 j)
    (fun ii => Fin.lastCases (p.2 ii) (p.1 ii) j) i

lemma finiteBlock_eq_extension {L : Type*} (d : L) (R : FiniteOverlap L)
    (hsym : ∀ i j, R i j = R j i) (hdiag : ∀ i, R i i = d) (n : ℕ) :
    finiteBlock (n+1) R = finiteExtension d (finiteBlock n R,finiteRow n R) := by
  funext i j
  refine Fin.lastCases ?_ (fun ii => ?_) i
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · simpa [finiteBlock,finiteExtension] using hdiag n
    · simpa [finiteBlock,finiteRow,finiteExtension] using hsym n jj
  · refine Fin.lastCases ?_ (fun jj => ?_) j
    · simp [finiteBlock,finiteRow,finiteExtension]
    · simp [finiteBlock,finiteExtension]

lemma finiteBlock_succ_law_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (d : L)
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c})
    (n : ℕ) (hn : 1 ≤ n)
    (hblock : μ.map (finiteBlock n) = ν.map (finiteBlock n)) :
    μ.map (finiteBlock (n+1)) = ν.map (finiteBlock (n+1)) := by
  have hjoint : μ.map (fun R => (finiteBlock n R,finiteRow n R)) =
      ν.map (fun R => (finiteBlock n R,finiteRow n R)) :=
    map_pair_eq_of_fiber_map_eq μ ν _ _ (finiteBlock_measurable n) (finiteRow_measurable n)
      fun A => finiteFiberRow_unique μ ν
        (hμ.mono fun _ h => ⟨h.1,h.2.2⟩) (hν.mono fun _ h => ⟨h.1,h.2.2⟩)
        hGGμ hGGν hpair n hn hblock A
  have hext (ρ : Measure (FiniteOverlap L))
      (hρ : ∀ᵐ R ∂ρ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
        ∀ i j k, min (R i j) (R i k) ≤ R j k) :
      ρ.map (finiteBlock (n+1)) =
        (ρ.map (fun R => (finiteBlock n R,finiteRow n R))).map (finiteExtension d) := by
    rw [Measure.map_map (measurable_of_countable _)
      ((finiteBlock_measurable n).prodMk (finiteRow_measurable n))]
    apply Measure.map_congr
    exact hρ.mono fun R hR => finiteBlock_eq_extension d R hR.1 hR.2.1 n
  rw [hext μ hμ,hext ν hν,hjoint]

theorem finiteGG_block_law_unique {L : Type*} [Fintype L] [LinearOrder L]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ ν : Measure (FiniteOverlap L)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : L)
    (hμ : ∀ᵐ R ∂μ, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = d) ∧
      ∀ i j k, min (R i j) (R i k) ≤ R j k)
    (hGGμ : FiniteGG μ) (hGGν : FiniteGG ν)
    (hpair : ∀ c, μ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c}) :
    ∀ n, μ.map (finiteBlock (n+1)) = ν.map (finiteBlock (n+1)) := by
  have hbase (ρ : Measure (FiniteOverlap L)) [IsProbabilityMeasure ρ]
      (hρ : ∀ᵐ R ∂ρ, ∀ i, R i i = d) :
      ρ.map (finiteBlock 1) = Measure.dirac (fun (_ _ : Fin 1) => d) := by
    have he : finiteBlock 1 =ᵐ[ρ] (fun _ => fun (_ _ : Fin 1) => d) := by
      filter_upwards [hρ] with R hR
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hi,hj,finiteBlock] using hR 0
    rw [Measure.map_congr he]
    simp
  intro n
  induction n with
  | zero =>
      exact (hbase μ (hμ.mono fun _ h => h.2.1)).trans
        (hbase ν (hν.mono fun _ h => h.2.1)).symm
  | succ n ih =>
      exact finiteBlock_succ_law_unique μ ν d hμ hν hGGμ hGGν hpair
        (n+1) (by omega) ih

lemma measureReal_atom_inter_of_ae_const {Ω X Y : Type*} [MeasurableSpace Ω] [DecidableEq X]
    (μ : Measure Ω) (a : Ω → X) (v : Ω → Y) (x₀ x : X) (y : Y)
    (ha : a =ᵐ[μ] fun _ => x₀) :
    μ.real {ω | a ω = x ∧ v ω = y} = if x₀ = x then μ.real {ω | v ω = y} else 0 := by
  classical
  by_cases hx : x₀ = x
  · rw [ite_eq_left hx]
    apply measureReal_congr
    filter_upwards [ha] with ω hω
    simp [hω, hx]
  · rw [ite_eq_right hx]
    convert (show μ.real ∅ = 0 from measureReal_empty) using 1
    apply measureReal_congr
    filter_upwards [ha] with ω hω
    change (a ω = x ∧ v ω = y) = False
    simp [hω, hx]

lemma finiteGG_of_ge_two {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] (μ : Measure (FiniteOverlap L)) [IsProbabilityMeasure μ]
    (d : L) (hdiag : ∀ᵐ R ∂μ, ∀ i, R i i = d)
    (hGG : ∀ n, 2 ≤ n → ∀ (i : Fin n) (A : FiniteBlock L n) (c : L),
      μ.real {R | finiteBlock n R = A ∧ R i n = c} =
        μ.real {R | finiteBlock n R = A} * μ.real {R | R 0 1 = c} / n +
        (∑ j ∈ Finset.univ.erase i, μ.real {R | finiteBlock n R = A ∧ R i j = c}) / n) :
    FiniteGG μ := by
  classical
  intro n hn i A c
  by_cases hn2 : 2 ≤ n
  · exact hGG n hn2 i A c
  have hn1 : n = 1 := by omega
  subst n
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hblock : finiteBlock (L := L) 1 =ᵐ[μ] fun _ => fun (_ _ : Fin 1) => d := by
    filter_upwards [hdiag] with R hR
    funext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    simpa [ha,hb,finiteBlock] using hR 0
  have hbase : μ.real {R | finiteBlock 1 R = A} =
      if (fun (_ _ : Fin 1) => d) = A then 1 else 0 := by
    have hh := measureReal_atom_inter_of_ae_const μ (finiteBlock 1) (fun _ => ())
      (fun (_ _ : Fin 1) => d) A () hblock
    simpa using hh
  have hnew := measureReal_atom_inter_of_ae_const μ (finiteBlock 1)
    (fun R => R 0 1) (fun (_ _ : Fin 1) => d) A c hblock
  simp only [Fin.val_zero,Nat.cast_one,div_one]
  rw [hnew,hbase]
  have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  rw [herase,Finset.sum_empty,add_zero]
  split_ifs <;> simp

end SphericalPerceptron
end
end

end OAI
