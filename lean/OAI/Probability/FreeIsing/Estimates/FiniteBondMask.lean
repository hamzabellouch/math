import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ClusterAssembly

def openMask {Ω E : Type*} (edges : Finset E) (X : E → Ω → Bool)
    (ω : Ω) : edges.powerset := by
  classical
  exact ⟨edges.filter (fun e => X e ω = true),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

theorem measurable_openMask {Ω E : Type*} [MeasurableSpace Ω]
    (edges : Finset E) (X : E → Ω → Bool)
    (hX : ∀ e ∈ edges, Measurable (X e)) : Measurable (openMask edges X) := by
  classical
  apply Measurable.subtype_mk
  apply measurable_finset_iff.mpr
  intro e
  by_cases he : e ∈ edges
  · have h : Measurable (fun ω => X e ω = true) := (hX e he).eq measurable_const
    simpa only [Finset.mem_filter, he, true_and] using h
  · simp only [Finset.mem_filter, he, false_and]
    exact measurable_const

theorem openMask_fiber {Ω E : Type*} [DecidableEq E]
    (edges : Finset E) (X : E → Ω → Bool)
    (A : edges.powerset) :
    {ω | openMask edges X ω = A} =
      ⋂ e ∈ edges, X e ⁻¹' {if e ∈ A.val then true else false} := by
  classical
  have hsub : A.val ⊆ edges := Finset.mem_powerset.mp A.property
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h e he
    have hm := congrArg (fun B : edges.powerset => e ∈ B.val) h
    change (e ∈ edges.filter (fun f => X f ω = true)) = (e ∈ A.val) at hm
    by_cases ha : e ∈ A.val
    · simpa [Finset.mem_filter, he, ha] using hm
    · have hn : X e ω ≠ true := by simpa [Finset.mem_filter, he, ha] using hm
      cases hx : X e ω <;> simp_all
  · intro h
    apply Subtype.ext
    apply Finset.ext
    intro e
    change (e ∈ edges.filter (fun f => X f ω = true)) ↔ e ∈ A.val
    by_cases he : e ∈ edges
    · have hx := h e he
      by_cases ha : e ∈ A.val <;> simp_all
    · have ha : e ∉ A.val := fun h => he (hsub h)
      simp [he, ha]

theorem openMask_atom_measure {Ω E : Type*} [MeasurableSpace Ω] [DecidableEq E]
    (μ : Measure Ω) (edges : Finset E) (X : E → Ω → Bool)
    (hindep : iIndepFun X μ) (p q : ENNReal)
    (htrue : ∀ e ∈ edges, μ {ω | X e ω = true} = p)
    (hfalse : ∀ e ∈ edges, μ {ω | X e ω = false} = q)
    (A : edges.powerset) :
    μ {ω | openMask edges X ω = A} = p ^ A.val.card * q ^ (edges \ A.val).card := by
  classical
  rw [openMask_fiber]
  rw [hindep.measure_inter_preimage_eq_mul edges (fun e _ => measurableSet_singleton _)]
  have hprod : (∏ e ∈ edges, μ (X e ⁻¹' {if e ∈ A.val then true else false})) =
      ∏ e ∈ edges, if e ∈ A.val then p else q := by
    apply Finset.prod_congr rfl
    intro e he
    have hset (b : Bool) : X e ⁻¹' {b} = {ω | X e ω = b} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    by_cases ha : e ∈ A.val
    · rw [ite_eq_left ha, ite_eq_left ha, hset]
      exact htrue e he
    · rw [ite_eq_right ha, ite_eq_right ha, hset]
      exact hfalse e he
  rw [hprod, Finset.prod_ite]
  have hsub : A.val ⊆ edges := Finset.mem_powerset.mp A.property
  have hfilter : edges.filter (fun e => e ∈ A.val) = A.val := by
    ext e
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hsub h)
  rw [hfilter, ← Finset.sdiff_eq_filter]
  simp only [Finset.prod_const]

theorem openMask_atom_measure_ofReal {Ω E : Type*} [MeasurableSpace Ω]
    [DecidableEq E] (μ : Measure Ω) (edges : Finset E) (X : E → Ω → Bool)
    (hindep : iIndepFun X μ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (htrue : ∀ e ∈ edges, μ {ω | X e ω = true} = ENNReal.ofReal theta)
    (hfalse : ∀ e ∈ edges, μ {ω | X e ω = false} = ENNReal.ofReal (1 - theta))
    (A : edges.powerset) :
    μ {ω | openMask edges X ω = A} =
      ENNReal.ofReal (theta ^ A.val.card * (1 - theta) ^ (edges \ A.val).card) := by
  rw [openMask_atom_measure μ edges X hindep _ _ htrue hfalse A]
  rw [ENNReal.ofReal_mul (pow_nonneg h0 _), ENNReal.ofReal_pow h0,
    ENNReal.ofReal_pow (sub_nonneg.mpr h1)]

theorem openMask_atom_measure_of_restricted_indep
    {Ω E : Type*} [MeasurableSpace Ω] [DecidableEq E]
    (μ : Measure Ω) (edges : Finset E) (X : E → Ω → Bool)
    (hindep : iIndepFun (fun e : edges => X e.val) μ) (p q : ENNReal)
    (htrue : ∀ e ∈ edges, μ {ω | X e ω = true} = p)
    (hfalse : ∀ e ∈ edges, μ {ω | X e ω = false} = q)
    (A : edges.powerset) :
    μ {ω | openMask edges X ω = A} = p ^ A.val.card * q ^ (edges \ A.val).card := by
  classical
  let sets : E → Set Bool := fun e => {if e ∈ A.val then true else false}
  have hi := hindep.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun e : edges => sets e.val) (fun _ _ => measurableSet_singleton _)
  have hset : (⋂ e : edges, X e.val ⁻¹' sets e.val) =
      ⋂ e ∈ edges, X e ⁻¹' sets e := by
    ext ω
    simp
  simp only [Finset.mem_univ, Set.iInter_true] at hi
  rw [hset, Finset.prod_coe_sort edges (fun e => μ (X e ⁻¹' sets e))] at hi
  rw [openMask_fiber]
  change μ (⋂ e ∈ edges, X e ⁻¹' sets e) = _
  rw [hi]
  have hprod : (∏ e ∈ edges, μ (X e ⁻¹' sets e)) =
      ∏ e ∈ edges, if e ∈ A.val then p else q := by
    apply Finset.prod_congr rfl
    intro e he
    have hset' (b : Bool) : X e ⁻¹' {b} = {ω | X e ω = b} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    dsimp only [sets]
    by_cases ha : e ∈ A.val
    · rw [ite_eq_left ha, ite_eq_left ha, hset']
      exact htrue e he
    · rw [ite_eq_right ha, ite_eq_right ha, hset']
      exact hfalse e he
  rw [hprod, Finset.prod_ite]
  have hsub : A.val ⊆ edges := Finset.mem_powerset.mp A.property
  have hfilter : edges.filter (fun e => e ∈ A.val) = A.val := by
    ext e
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => hsub h)
  rw [hfilter, ← Finset.sdiff_eq_filter]
  simp only [Finset.prod_const]

theorem openMask_atom_measure_ofReal_restricted
    {Ω E : Type*} [MeasurableSpace Ω] [DecidableEq E]
    (μ : Measure Ω) (edges : Finset E) (X : E → Ω → Bool)
    (hindep : iIndepFun (fun e : edges => X e.val) μ)
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (htrue : ∀ e ∈ edges, μ {ω | X e ω = true} = ENNReal.ofReal theta)
    (hfalse : ∀ e ∈ edges, μ {ω | X e ω = false} = ENNReal.ofReal (1 - theta))
    (A : edges.powerset) :
    μ {ω | openMask edges X ω = A} =
      ENNReal.ofReal (theta ^ A.val.card * (1 - theta) ^ (edges \ A.val).card) := by
  rw [openMask_atom_measure_of_restricted_indep μ edges X hindep _ _ htrue hfalse A]
  rw [ENNReal.ofReal_mul (pow_nonneg h0 _), ENNReal.ofReal_pow h0,
    ENNReal.ofReal_pow (sub_nonneg.mpr h1)]

end Problem367.ClusterAssembly

end

end OAI
