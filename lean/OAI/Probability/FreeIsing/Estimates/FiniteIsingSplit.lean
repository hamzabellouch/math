import OAI.Probability.FreeIsing.Cavity.ArtanhFusion
import OAI.Probability.FreeIsing.Cavity.Homeomorph
import OAI.Probability.FreeIsing.Estimates.FiniteSpinCoupling
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Ising.GaussianPosterior

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteIsingSplit

variable {V : Type*} [DecidableEq V]

def splitEquiv (A B : Finset V) (hAB : Disjoint A B) :
    (↥(A ∪ B) → IsingSpin) ≃ (A → IsingSpin) × (B → IsingSpin) where
  toFun eta := (fun v => eta ⟨v, Finset.mem_union_left B v.property⟩,
    fun v => eta ⟨v, Finset.mem_union_right A v.property⟩)
  invFun eta v := if h : v.1 ∈ A then eta.1 ⟨v.1, h⟩ else
    eta.2 ⟨v.1, (Finset.mem_union.mp v.property).resolve_left h⟩
  left_inv eta := by
    funext v
    dsimp only
    split_ifs <;> rfl
  right_inv eta := by
    apply Prod.ext
    · funext v
      simp only [dite_eq_left v.property]
    · funext v
      have hv : v.1 ∉ A := fun h => Finset.disjoint_left.mp hAB h v.property
      simp only [dite_eq_right hv]

@[simp] lemma splitEquiv_fst (A B : Finset V) (hAB : Disjoint A B)
    (eta : ↥(A ∪ B) → IsingSpin) (v : A) :
    (splitEquiv A B hAB eta).1 v =
      eta ⟨v, Finset.mem_union_left B v.property⟩ := rfl

@[simp] lemma splitEquiv_snd (A B : Finset V) (hAB : Disjoint A B)
    (eta : ↥(A ∪ B) → IsingSpin) (v : B) :
    (splitEquiv A B hAB eta).2 v =
      eta ⟨v, Finset.mem_union_right A v.property⟩ := rfl

variable {d : ℕ}

def observedEnergy (beta : ℝ) (D : Finset (TreeVertex d))
    (y : TreeVertex d → ℝ) : (D → IsingSpin) → ℝ :=
  FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
    (fun eta v => spinSign (eta v)) (D.restrict y)

lemma inducedEdges_endpoints {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    e.1 ∈ D ∧ e.2 ∈ D := by
  classical
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1

lemma observedEnergy_restrict (beta : ℝ) (D : Finset (TreeVertex d))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta D y (D.restrict eta) =
      beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2) +
        ∑ v ∈ D, y v * spinSign (eta v) := by
  classical
  unfold observedEnergy FinitePosterior.fieldEnergy finiteIsingEnergy
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have he' := inducedEdges_endpoints he
    simp [extendFiniteSpin, he'.1, he'.2]
  · exact Finset.sum_coe_sort D (fun v => y v * spinSign (eta v))

theorem observedEnergy_split_restrict (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta (A ∪ B) y ((A ∪ B).restrict eta) =
      observedEnergy beta A y (A.restrict eta) +
      observedEnergy beta B y (B.restrict eta) +
        beta * spinSign (eta u) * spinSign (eta v) := by
  classical
  have hdis : Disjoint (inducedEdges A) (inducedEdges B) := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact Finset.disjoint_left.mp hAB
      (inducedEdges_endpoints heA).1 (inducedEdges_endpoints heB).1
  have hnot : (u.1, v.1) ∉ inducedEdges A ∪ inducedEdges B := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.disjoint_left.mp hAB (inducedEdges_endpoints he).2 v.property
    · exact Finset.disjoint_left.mp hAB u.property (inducedEdges_endpoints he).1
  rw [observedEnergy_restrict, observedEnergy_restrict, observedEnergy_restrict,
    hEdges, Finset.sum_insert hnot, Finset.sum_union hdis, Finset.sum_union hAB]
  ring

theorem observedEnergy_split (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : ↥(A ∪ B) → IsingSpin) :
    observedEnergy beta (A ∪ B) y eta =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) (splitEquiv A B hAB eta) := by
  classical
  let sigma := extendFiniteSpin (A ∪ B) eta
  have hU : (A ∪ B).restrict sigma = eta := restrict_extendFiniteSpin _ _
  have hA : A.restrict sigma = (splitEquiv A B hAB eta).1 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_left B w.property⟩
  have hB : B.restrict sigma = (splitEquiv A B hAB eta).2 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_right A w.property⟩
  have hu : sigma u = (splitEquiv A B hAB eta).1 u := congrFun hA u
  have hv : sigma v = (splitEquiv A B hAB eta).2 v := congrFun hB v
  have h := observedEnergy_split_restrict beta A B hAB u v hEdges y sigma
  simpa only [hU, hA, hB, hu, hv, FiniteSpinCoupling.energy] using h

def mean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : ℝ :=
  FiniteSpinCoupling.mean (observedEnergy beta D y) (fun eta => eta v)

lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) :
    mean beta D v y = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) (D.restrict y) := by
  simp only [mean, FiniteSpinCoupling.mean_eq, FiniteSpinCoupling.numerator,
    FiniteSpinCoupling.partition, observedEnergy, FinitePosterior.fieldMean]

theorem mean_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      (mean beta A u y + Real.tanh beta * mean beta B v y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  exact FiniteSpinCoupling.mean_of_energy_split (splitEquiv A B hAB)
    (observedEnergy beta (A ∪ B) y) beta (observedEnergy beta A y)
    (observedEnergy beta B y) (fun s => s u) (fun s => s v)
    (observedEnergy_split beta A B hAB u v hEdges y)

theorem mean_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      (mean beta B v y + Real.tanh beta * mean beta A u y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  have hE : observedEnergy beta (A ∪ B) y =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) ∘ splitEquiv A B hAB :=
    funext (observedEnergy_split beta A B hAB u v hEdges y)
  unfold mean
  rw [hE]
  change FiniteSpinCoupling.mean (_ ∘ splitEquiv A B hAB)
    ((fun s : (A → IsingSpin) × (B → IsingSpin) => s.2 v) ∘ splitEquiv A B hAB) = _
  rw [FiniteSpinCoupling.mean_equiv, FiniteSpinCoupling.mean_energy_snd]

lemma mean_mem_Ioo (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : mean beta D v y ∈ Set.Ioo (-1 : ℝ) 1 := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    change spinSign (eta v) = -1 ∨ spinSign (eta v) = 1
    cases eta v <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

def field (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : ℝ := Real.artanh (mean beta D v y)

theorem field_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      field beta A u y + cavityMessage (Real.tanh beta) (field beta B v y) := by
  unfold field
  rw [mean_union_fst beta A B hAB u v hEdges y]
  exact artanh_binaryFusion_scaled_of_mem ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta A u y) (mean_mem_Ioo beta B v y)

theorem field_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      field beta B v y + cavityMessage (Real.tanh beta) (field beta A u y) := by
  unfold field
  rw [mean_union_snd beta A B hAB u v hEdges y]
  rw [show 1 + Real.tanh beta * mean beta A u y * mean beta B v y =
      1 + Real.tanh beta * mean beta B v y * mean beta A u y by ring]
  exact artanh_binaryFusion_scaled_of_mem
    ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta B v y) (mean_mem_Ioo beta A u y)

theorem cavityFromSites_eq_component_fields {beta : ℝ} (hbeta : 0 ≤ beta)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y,
        field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y) =
      (field beta A u y, field beta B v y) := by
  apply cavityFromSites_eq
  exact ⟨(field_union_fst beta A B hAB u v hEdges y).symm,
    (field_union_snd beta A B hAB u v hEdges y).symm⟩

end Problem367.FiniteIsingSplit

end

end OAI
