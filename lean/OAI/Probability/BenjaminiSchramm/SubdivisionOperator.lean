import OAI.Probability.BenjaminiSchramm.SubdivisionGeometry
import OAI.Probability.UnimodularPercolation.Subdivision.Operator

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable
noncomputable local instance : DecidableEq (V ⊕ E) := Classical.decEq _

noncomputable def endpointRow (G : BondGraph V E) : V ⊕ E → Finset V
  | .inl x => {x}
  | .inr e => (G e).toFinset

theorem endpointRow_card_le (G : BondGraph V E) (z : V ⊕ E) :
    (endpointRow G z).card ≤ 2 := by
  cases z with
  | inl x => simp [endpointRow]
  | inr e => simp only [endpointRow, Sym2.card_toFinset]; split_ifs <;> omega

noncomputable def incidenceKernel (G : BondGraph V E) (z w : V ⊕ E) : ℝ :=
  if w ∈ (endpointRow G z).map ⟨Sum.inl, Sum.inl_injective⟩ then 1 else 0

theorem exists_incidence_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) :
    ∃ Q : Hilbert (V ⊕ E) →L[ℂ] Hilbert (V ⊕ E),
      ∀ z w, matrixCoeff Q z w = (incidenceKernel G z w : ℂ) := by
  have hrow : ∀ z (s : Finset (V ⊕ E)), ∑ w ∈ s, incidenceKernel G z w ≤ (d : ℝ) + 3 := by
    intro z s
    have hs : (s.filter fun w => w ∈ (endpointRow G z).map
          ⟨Sum.inl, Sum.inl_injective⟩) ⊆
          (endpointRow G z).map ⟨Sum.inl, Sum.inl_injective⟩ := by
      intro w hw; exact (Finset.mem_filter.mp hw).2
    have hc := (Finset.card_le_card hs).trans (by simpa using endpointRow_card_le G z)
    simp only [incidenceKernel, Finset.sum_boole]
    exact_mod_cast (show (s.filter fun w => w ∈ (endpointRow G z).map
      ⟨Sum.inl, Sum.inl_injective⟩).card ≤ d + 3 by omega)
  have hcol : ∀ w (s : Finset (V ⊕ E)), ∑ z ∈ s, incidenceKernel G z w ≤ (d : ℝ) + 3 := by
    intro w s
    cases w with
      | inr e => simpa [incidenceKernel, Finset.mem_map] using (show (0 : ℝ) ≤ d + 3 by positivity)
      | inl x =>
        let F : Finset (V ⊕ E) := {Sum.inl x} ∪ (hloc x).toFinset.map
          ⟨Sum.inr, Sum.inr_injective⟩
        have hs : (s.filter fun z : V ⊕ E => (Sum.inl x : V ⊕ E) ∈ (endpointRow G z).map
            ⟨Sum.inl, Sum.inl_injective⟩) ⊆ F := by
          intro z hz
          have hm := (Finset.mem_filter.mp hz).2
          cases z with
          | inl y => simpa [endpointRow, F, eq_comm] using hm
          | inr e =>
            have hx : x ∈ G e := by simpa [endpointRow, Finset.mem_map] using hm
            simp [F, (hloc x).mem_toFinset.mpr hx]
        have hc : F.card ≤ d + 1 := by
          calc
            F.card ≤ 1 + (hloc x).toFinset.card := by
              simpa only [F, Finset.card_singleton, Finset.card_map] using
                Finset.card_union_le ({Sum.inl x} : Finset (V ⊕ E))
                  ((hloc x).toFinset.map ⟨Sum.inr, Sum.inr_injective⟩)
            _ ≤ d + 1 := by
              have hh := (incident_ncard_le_degree G hloc x).trans (hd x)
              rw [Set.ncard_eq_toFinset_card _ (hloc x)] at hh
              omega
        simp only [incidenceKernel, Finset.sum_boole]
        exact_mod_cast (show (s.filter fun z => Sum.inl x ∈ (endpointRow G z).map
          ⟨Sum.inl, Sum.inl_injective⟩).card ≤ d + 3 from
          (Finset.card_le_card hs).trans (hc.trans (by omega)))
  obtain ⟨Q, _, hQ⟩ := exists_operator_of_row_column_bound (incidenceKernel G)
    (d + 3) (by positivity) (by intros; dsimp [incidenceKernel]; split_ifs <;> norm_num)
    hrow hcol
  exact ⟨Q, hQ⟩

theorem conn_subdivision_endpoints (G : BondGraph V E) (ν : Set (E × Bool))
    (z w : V ⊕ E) (hc : Conn (subdivision G) (subdivisionOpen G ν) z w) :
    ∃ x ∈ endpointRow G z, ∃ y ∈ endpointRow G w, Conn G (seriesOpen ν) x y := by
  cases z with
  | inl x =>
    cases w with
    | inl y => exact ⟨x, by simp [endpointRow], y, by simp [endpointRow],
        (conn_subdivision_iff G ν x y).mp hc⟩
    | inr e =>
      obtain ⟨y, hxy, hy⟩ := conn_subdivision_inr G ν x e hc
      exact ⟨x, by simp [endpointRow], y, Sym2.mem_toFinset.mpr hy, hxy⟩
  | inr e =>
    cases w with
    | inl y =>
      obtain ⟨x, hyx, hx⟩ := conn_subdivision_inr G ν y e (conn_symm _ _ hc)
      exact ⟨x, Sym2.mem_toFinset.mpr hx, y, by simp [endpointRow], conn_symm _ _ hyx⟩
    | inr f =>
      rcases hc.cases_head with h | ⟨z, hez, hzf⟩
      · have hef : e = f := Sum.inr.inj h
        subst f
        exact ⟨(G e).out.1, Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _),
          (G e).out.1, Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _), conn_refl _ _ _⟩
      · cases z with
        | inl x =>
          obtain ⟨hx, _⟩ := (subdivision_open_adj_iff G ν x e).mp
            (by obtain ⟨a, ha, he⟩ := hez; exact ⟨a, ha, he.trans Sym2.eq_swap⟩)
          obtain ⟨y, hxy, hy⟩ := conn_subdivision_inr G ν x f hzf
          exact ⟨x, Sym2.mem_toFinset.mpr hx, y, Sym2.mem_toFinset.mpr hy, hxy⟩
        | inr a =>
          obtain ⟨b, _, hb⟩ := hez
          exact (subdivision_adj_inr_inr G e a ⟨b, hb⟩).elim

theorem twoPoint_subdivision_le_endpoint_sum [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval) (z w : V ⊕ E) :
    twoPoint (subdivision G) q z w ≤
      ∑ x ∈ endpointRow G z, ∑ y ∈ endpointRow G w, twoPoint G (q ^ 2) x y := by
  let μ : Measure (Set (E × Bool)) := law q
  have : IsProbabilityMeasure μ := inferInstance
  have ht (x y : V) : μ.real {ν | Conn G (seriesOpen ν) x y} = twoPoint G (q ^ 2) x y := by
    unfold twoPoint
    rw [← law_map_seriesOpen q, Measure.map_apply measurable_seriesOpen (measurableSet_conn G x y)]
    rfl
  have hh : twoPoint (subdivision G) q z w =
      μ.real {ν | Conn (subdivision G) (subdivisionOpen G ν) z w} := by
    unfold twoPoint
    rw [← law_map_subdivisionOpen G q, Measure.map_apply (measurable_subdivisionOpen G)
      (measurableSet_conn (subdivision G) z w)]
    rfl
  rw [hh]
  calc
    _ ≤ μ.real (⋃ ab ∈ endpointRow G z ×ˢ endpointRow G w,
        {ν | Conn G (seriesOpen ν) ab.1 ab.2}) := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ν hν
      obtain ⟨x, hx, y, hy, hxy⟩ := conn_subdivision_endpoints G ν z w hν
      exact Set.mem_iUnion.mpr ⟨(x, y), Set.mem_iUnion.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩
    _ ≤ ∑ ab ∈ endpointRow G z ×ˢ endpointRow G w,
        μ.real {ν | Conn G (seriesOpen ν) ab.1 ab.2} := measureReal_biUnion_finset_le _ _
    _ = _ := by simp only [ht, Finset.sum_product]

theorem incidence_operator_apply (G : BondGraph V E)
    (Q : Hilbert (V ⊕ E) →L[ℂ] Hilbert (V ⊕ E))
    (hQ : ∀ z w, matrixCoeff Q z w = (incidenceKernel G z w : ℂ))
    (f : Hilbert (V ⊕ E)) (z : V ⊕ E) :
    Q f z = ∑ x ∈ endpointRow G z, f (Sum.inl x) := by
  rw [← (operator_kernel_hasSum Q f z).tsum_eq]
  have hs : (∑' w, matrixCoeff Q z w * f w) =
      ∑ w ∈ (endpointRow G z).map ⟨Sum.inl, Sum.inl_injective⟩,
        matrixCoeff Q z w * f w := by
    apply tsum_eq_sum
    intro w hw
    rw [hQ]
    simp [incidenceKernel, hw]
  rw [hs, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hQ]
  simp [incidenceKernel, hx]

theorem incidence_adjoint_single (G : BondGraph V E)
    (Q : Hilbert (V ⊕ E) →L[ℂ] Hilbert (V ⊕ E))
    (hQ : ∀ z w, matrixCoeff Q z w = (incidenceKernel G z w : ℂ))
    (w : V ⊕ E) :
    hilbertRestrictInl (star Q (lp.single 2 w (1 : ℂ))) =
      ∑ y ∈ endpointRow G w, lp.single 2 y (1 : ℂ) := by
  apply lp.ext
  funext x
  rw [hilbertRestrictInl_apply]
  change matrixCoeff (star Q) (Sum.inl x) w = _
  rw [matrixCoeff_adjoint, hQ]
  simp only [incidenceKernel, Finset.mem_map, Function.Embedding.coeFn_mk, Sum.inl.injEq,
    exists_eq_right, lp.coeFn_sum, lp.coeFn_single]
  by_cases hx : x ∈ endpointRow G w <;> simp [Pi.single_apply, hx]

theorem operatorBounded_subdivision_of_bounded [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (q : unitInterval) (hb : OperatorBounded G (q ^ 2)) :
    OperatorBounded (subdivision G) q := by
  obtain ⟨d, _, hd⟩ := exists_degree_bound G hqt
  obtain ⟨Q, hQ⟩ := exists_incidence_operator G hloc d hd
  obtain ⟨A, hA⟩ := hb
  dsimp only [HasKernel] at hA
  let B : Hilbert (V ⊕ E) →L[ℂ] Hilbert (V ⊕ E) :=
    Q ∘L hilbertInl ∘L A ∘L hilbertRestrictInl ∘L star Q
  let U (z w : V ⊕ E) : ℝ :=
    ∑ x ∈ endpointRow G z, ∑ y ∈ endpointRow G w, twoPoint G (q ^ 2) x y
  have hB (z w : V ⊕ E) : B (lp.single 2 w (1 : ℂ)) z = (U z w : ℂ) := by
    simp only [B, ContinuousLinearMap.comp_apply]
    rw [incidence_operator_apply G Q hQ, incidence_adjoint_single G Q hQ]
    simp only [hilbertInl_apply_inl, map_sum, lp.coeFn_sum, Finset.sum_apply, hA,
      U, Complex.ofReal_sum]
  obtain ⟨T, _, hT⟩ := exists_operator_of_matrix_domination U
    (twoPoint (subdivision G) q)
    (fun z w => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      twoPoint_nonneg G (q ^ 2) x y)
    (fun z w => by
      rw [abs_of_nonneg (twoPoint_nonneg _ _ _ _)]
      exact twoPoint_subdivision_le_endpoint_sum G q z w) B hB
  exact ⟨T, hT⟩

theorem operatorBounded_subdivision_iff [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (q : unitInterval) :
    OperatorBounded (subdivision G) q ↔ OperatorBounded G (q ^ 2) :=
  ⟨operatorBounded_of_subdivision G q,
    operatorBounded_subdivision_of_bounded G hloc hqt q⟩

theorem ptwo_subdivision_sq [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) :
    ptwo (subdivision G) ^ 2 = ptwo G := by
  change squareParameter (sSup {q | OperatorBounded (subdivision G) q}) =
    sSup {p | OperatorBounded G p}
  have he : squareParameter '' {q | OperatorBounded (subdivision G) q} =
      {p | OperatorBounded G p} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (operatorBounded_subdivision_iff G hloc hqt q).mp hq
    · intro hp
      change OperatorBounded G p at hp
      refine ⟨squareParameter.symm p, ?_, squareParameter.apply_symm_apply p⟩
      apply (operatorBounded_subdivision_iff G hloc hqt _).mpr
      change OperatorBounded G (squareParameter (squareParameter.symm p))
      simpa only [squareParameter.apply_symm_apply] using hp
  rw [squareParameter.map_sSup, ← sSup_image, he]

end Percolation.BenjaminiSchramm

end OAI
