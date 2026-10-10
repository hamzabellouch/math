import OAI.Probability.SLE.Multipoint.MultipointCappedKernel

namespace OAI

/-! Each term of the nearest-neighbor cap expansion is a loop-free graph
with at most one outgoing edge at every vertex. Integrating a vertex of
incidence at most two proves the fixed-order kernel estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

def selectedTarget {ι : Type*} (f : ι → Option ι) (i : ι) : ι := (f i).getD i

def selectedVertices {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Option ι) : Finset ι :=
  Finset.univ.filter (fun i => selectedTarget f i ≠ i)

def selectedEdges {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Option ι) : Finset (ι × ι) :=
  (selectedVertices f).image (fun i => (i,selectedTarget f i))

lemma selectedEdges_outgoing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) :
    ∀ e ∈ selectedEdges f, ∀ d ∈ selectedEdges f, e.1=d.1 → e=d := by
  intro e he d hd h
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
  exact congrArg (fun i => (i,selectedTarget f i)) h

lemma selectedEdges_loopfree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) : ∀ e ∈ selectedEdges f, e.1≠e.2 := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp hi).2.symm

lemma graphKernel_selectedEdges {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (f : ι → Option ι) (x : ι → ℂ) :
    graphKernel α (selectedEdges f) x =
      ∏ i, if selectedTarget f i=i then 1 else distanceKernel α (x i) (x (selectedTarget f i)) := by
  unfold graphKernel selectedEdges
  rw [Finset.prod_image]
  · simp only [selectedVertices,Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : selectedTarget f i=i <;> simp [h]
  · intro i _ j _ h
    exact congrArg Prod.fst h

def capCoefficient (α b : ℝ) : ℝ≥0∞ := max 1 (ENNReal.ofReal (b^(-α)))

lemma capCoefficient_finite (α b : ℝ) : capCoefficient α b < ⊤ := by
  unfold capCoefficient
  exact max_lt (by simp) ENNReal.ofReal_lt_top

lemma rowChoice_le_graph_factor {ι : Type*} [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) (f : ι → Option ι) (i : ι) :
    rowChoice α b x i (f i) ≤ capCoefficient α b *
      (if selectedTarget f i=i then 1 else distanceKernel α (x i) (x (selectedTarget f i))) := by
  cases h : f i with
  | none =>
    simp only [rowChoice,selectedTarget,h,Option.getD_none,ite_true,mul_one]
    exact le_max_right _ _
  | some j =>
    simp only [rowChoice,selectedTarget,h,Option.getD_some]
    by_cases hji : j=i
    · simp only [hji,ite_true]
      exact bot_le
    · simp only [hji,ite_false]
      have hc : 1 ≤ capCoefficient α b := le_max_left _ _
      calc
        distanceKernel α (x i) (x j) = 1 * distanceKernel α (x i) (x j) := (one_mul _).symm
        _ ≤ capCoefficient α b * distanceKernel α (x i) (x j) := by gcongr

lemma rowProduct_le_graph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) (f : ι → Option ι) :
    (∏ i, rowChoice α b x i (f i)) ≤
      capCoefficient α b ^ Fintype.card ι * graphKernel α (selectedEdges f) x := by
  rw [graphKernel_selectedEdges,← Finset.card_univ,← Finset.prod_const,← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => rowChoice_le_graph_factor α b x f i)

lemma cappedDistanceKernel_le_graph_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α b : ℝ) (x : ι → ℂ) :
    cappedDistanceKernel α b x ≤
      ∑ f : ι → Option ι, capCoefficient α b ^ Fintype.card ι * graphKernel α (selectedEdges f) x :=
  (cappedDistanceKernel_le_expansion α b x).trans
    (Finset.sum_le_sum (fun f _ => rowProduct_le_graph α b x f))

/-- Integrate all graph vertices. The empty index set is included. -/
theorem graphKernel_marginal_le {ι : Type*} [DecidableEq ι]
    (α : ℝ) (K : Set ℂ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (S : Finset ι) (E : Finset (ι × ι))
    (hends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f)
    (hloop : ∀ e ∈ E, e.1≠e.2) (x : ι → ℂ) :
    lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α E) x ≤ C^S.card := by
  induction S using Finset.strongInductionOn generalizing E with
  | _ S ih =>
    by_cases hempty : S=∅
    · have hE : E=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        simpa only [hempty,Finset.notMem_empty] using (hends e he).1
      simp only [hempty,hE,lmarginal_empty,graphKernel,Finset.prod_empty,Finset.card_empty,pow_zero,le_rfl]
    · obtain ⟨v,hv,hdegree⟩ := exists_vertex_incident_card_le_two S
        (Finset.nonempty_iff_ne_empty.mpr hempty) E hends hout
      obtain ⟨hends',hout',hloop'⟩ := eraseVertex_properties S E v hends hout hloop
      have hsmall := ih (S.erase v) (Finset.erase_ssubset hv) (eraseVertex E v) hends' hout' hloop'
      calc
        lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α E) x =
            lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (fun x => ∫⁻ y in K, graphKernel α E (Function.update x v y)) x := by
          exact congrFun (lmarginal_erase' (μ := fun _ : ι => volume.restrict K)
            (graphKernel α E) (measurable_graphKernel α E) hv) x
        _ ≤ lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (fun x => C*graphKernel α (eraseVertex E v) x) x :=
          lmarginal_mono (fun x => graphKernel_section_le α K C hC0 hC1 hC2 E v x hdegree hloop) x
        _ = C*lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (graphKernel α (eraseVertex E v)) x := by
          exact lintegral_const_mul' C _ hC.ne
        _ ≤ C*C^(S.erase v).card := by gcongr
        _ = C^S.card := by rw [← Finset.card_erase_add_one hv,pow_succ,mul_comm]

lemma selectedGraph_integral_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (K : Set ℂ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (f : ι → Option ι) :
    (∫⁻ x, graphKernel α (selectedEdges f) x ∂Measure.pi (fun _ : ι => volume.restrict K)) ≤
      C^Fintype.card ι := by
  simpa only [lmarginal_univ,Finset.card_univ] using
    graphKernel_marginal_le α K C hC hC0 hC1 hC2 Finset.univ (selectedEdges f)
      (fun _ _ => ⟨Finset.mem_univ _,Finset.mem_univ _⟩)
      (selectedEdges_outgoing f) (selectedEdges_loopfree f) (fun _ => 0)

/-- The exact capped inverse-distance kernel has a finite integral on every
bounded planar product set, for every fixed order. -/
theorem cappedDistanceKernel_integral_lt_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (b : ℝ)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    (∫⁻ x, cappedDistanceKernel (ι := ι) α b x
      ∂Measure.pi (fun _ : ι => volume.restrict K)) < ⊤ := by
  obtain ⟨C,hC,_,hC0,hC1,hC2⟩ := distanceKernel_uniform_local_bounds hα hα1 K hK
  apply lt_of_le_of_lt (lintegral_mono (cappedDistanceKernel_le_graph_sum α b))
  rw [lintegral_finsetSum]
  · apply ENNReal.sum_lt_top.mpr
    intro f _
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (capCoefficient_finite α b).ne)]
    exact lt_of_le_of_lt (by gcongr; exact selectedGraph_integral_le α K C hC hC0 hC1 hC2 f)
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top (capCoefficient_finite α b)) (ENNReal.pow_lt_top hC))
  · intro f _
    exact measurable_const.mul (measurable_graphKernel α (selectedEdges f))

end SLEExactGauge.Multipoint

end

end OAI
