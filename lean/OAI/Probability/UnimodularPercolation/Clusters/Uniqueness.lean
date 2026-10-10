import Mathlib
import OAI.Probability.UnimodularPercolation.ProductMeasure.Association

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section InfiniteOrbits
attribute [local instance] Classical.propDecidable

def vertexOrbit (G : BondGraph V E) (x : V) : Set V :=
  {y | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a x = y}

theorem adj_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} (hxy : Adj G x y) : Adj G (a x) (a y) := by
  obtain ⟨e, he⟩ := hxy
  exact ⟨b e, by rw [h e, he, Sym2.map_mk]⟩

theorem mem_reachBall_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} {n : ℕ} (hy : y ∈ reachBall G x n) :
    a y ∈ reachBall G (a x) n := by
  induction n generalizing y with
  | zero => simpa only [reachBall, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq] using hy
  | succ n ih =>
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · change a y ∈ reachBall G (a x) n ∪ ⋃ z ∈ reachBall G (a x) n, {w | Adj G z w}
      apply Or.inr
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy ⊢
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨a z, ih hz, adj_aut G h hzy⟩

 

theorem vertexOrbit_infinite [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (x : V) :
    (vertexOrbit G x).Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := hqt
  choose n hn using (fun y => exists_mem_reachBall (hconn x y))
  have hS : (⋃ o ∈ (R : Set V), ⋃ z ∈ vertexOrbit G x, reachBall G z (n o)).Finite :=
    R.finite_toSet.biUnion fun o _ => hfin.biUnion fun z _ => finite_reachBall hloc z (n o)
  have he : Set.univ ⊆ ⋃ o ∈ (R : Set V), ⋃ z ∈ vertexOrbit G x, reachBall G z (n o) := by
    intro y _
    obtain ⟨o, ho, a, b, hab, hay⟩ := hR y
    simp only [Set.mem_iUnion]
    exact ⟨o, ho, a x, ⟨a, b, hab, rfl⟩, hay ▸ mem_reachBall_aut G hab (hn o)⟩
  exact Set.infinite_univ (hS.subset he)

end InfiniteOrbits

section FinitePairBound
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

noncomputable def deltaSum (F : Finset V) : Hilbert V := ∑ x ∈ F, lp.single 2 x (1 : ℂ)

@[simp] theorem deltaSum_apply (F : Finset V) (x : V) :
    deltaSum F x = if x ∈ F then 1 else 0 := by
  simp only [deltaSum, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

@[simp] theorem inner_deltaSum (F : Finset V) (f : Hilbert V) :
    inner ℂ (deltaSum F) f = ∑ x ∈ F, f x := by
  simp [deltaSum, lp.inner_single_left]

theorem norm_deltaSum_sq (F : Finset V) : ‖deltaSum F‖ ^ 2 = (F.card : ℝ) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_deltaSum]
  simp only [map_sum, deltaSum_apply]
  trans ∑ _x ∈ F, (1 : ℝ)
  · apply Finset.sum_congr rfl
    intro x hx
    simp [hx]
  · simp

 
theorem sum_twoPoint_le_norm_card (G : BondGraph V E) (p : unitInterval)
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (F : Finset V) :
    ∑ x ∈ F, ∑ y ∈ F, twoPoint G p x y ≤ ‖A‖ * F.card := by
  have he : inner ℂ (deltaSum F) (A (deltaSum F)) =
      ((∑ x ∈ F, ∑ y ∈ F, twoPoint G p x y : ℝ) : ℂ) := by
    rw [inner_deltaSum]
    simp only [deltaSum, map_sum]
    simp only [lp.coeFn_sum, Finset.sum_apply, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hA x y
  have h := (Complex.re_le_norm (inner ℂ (deltaSum F) (A (deltaSum F)))).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)))
  rw [he, Complex.ofReal_re] at h
  calc
    _ ≤ ‖deltaSum F‖ * (‖A‖ * ‖deltaSum F‖) := h
    _ = ‖A‖ * ‖deltaSum F‖ ^ 2 := by ring
    _ = _ := by rw [norm_deltaSum_sq]

end FinitePairBound

section PairCounting
attribute [local instance] Classical.propDecidable

 
theorem card_sq_le_image_card_mul_pairs {W : Type*} (S : Finset V) (c : V → W) :
    (S.card : ℝ) ^ 2 ≤ ((S.image c).card : ℝ) *
      ∑ x ∈ S, ∑ y ∈ S, if c x = c y then (1 : ℝ) else 0 := by
  let t := S.image c
  let f := fun w => ((S.filter (fun x => c x = w)).card : ℝ)
  have hsum : ∑ w ∈ t, f w = (S.card : ℝ) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (fun x (hx : x ∈ S) => Finset.mem_image_of_mem c hx) (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, t, f] using h
  have hsq : ∑ w ∈ t, f w ^ 2 =
      ∑ x ∈ S, ∑ y ∈ S, if c x = c y then (1 : ℝ) else 0 := by
    calc
      ∑ w ∈ t, f w ^ 2 = ∑ w ∈ t, ∑ x ∈ S with c x = w, f (c x) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [show ∑ x ∈ S with c x = w, f (c x) =
            ∑ _x ∈ S with c _x = w, f w from
          Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
        simp only [Finset.sum_const, nsmul_eq_mul, f]
        ring
      _ = ∑ x ∈ S, f (c x) := Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image_of_mem c hx) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, f]
        congr 2
        ext y
        simp [eq_comm]
  have h := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) f
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hsq, t] using h

end PairCounting

section PairIntegral
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem square_sum_probability_le (F : Finset V) (S : V → Set Ω)
    (C : V → V → Set Ω) (hS : ∀ x, MeasurableSet (S x))
    (hC : ∀ x y, MeasurableSet (C x y)) (n : ℝ)
    (hpoint : ∀ ω, (∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) ω) ^ 2 ≤
      n * ∑ x ∈ F, ∑ y ∈ F, (C x y).indicator (fun _ => (1 : ℝ)) ω) :
    (∑ x ∈ F, μ.real (S x)) ^ 2 ≤ n * ∑ x ∈ F, ∑ y ∈ F, μ.real (C x y) := by
  let X := fun ω => ∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) ω
  have hX : MemLp X 2 μ := memLp_finsetSum F
    (fun x _ => (memLp_const (1 : ℝ)).indicator (hS x))
  have hCi (x y) : Integrable ((C x y).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hC x y)
  have hY : Integrable (fun ω => ∑ x ∈ F, ∑ y ∈ F,
      (C x y).indicator (fun _ => (1 : ℝ)) ω) μ :=
    integrable_finsetSum F (fun x _ => integrable_finsetSum F (fun y _ => hCi x y))
  have hv := variance_nonneg X μ
  rw [variance_eq_sub hX] at hv
  have hi := integral_mono hX.integrable_sq (hY.const_mul n) hpoint
  have hx : (∫ ω, X ω ∂μ) = ∑ x ∈ F, μ.real (S x) := by
    dsimp only [X]
    rw [integral_finsetSum F (fun x _ => (integrable_const (1 : ℝ)).indicator (hS x))]
    simp only [integral_indicator_const _ (hS _), smul_eq_mul, mul_one]
  have hy : (∫ ω, n * ∑ x ∈ F, ∑ y ∈ F,
      (C x y).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      n * ∑ x ∈ F, ∑ y ∈ F, μ.real (C x y) := by
    rw [integral_const_mul, integral_finsetSum F
      (fun x _ => integrable_finsetSum F (fun y _ => hCi x y))]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum F (fun y _ => hCi x y)]
    simp only [integral_indicator_const _ (hC x _), smul_eq_mul, mul_one]
  rw [hx] at hv
  rw [hy] at hi
  exact (sub_nonneg.mp hv).trans hi

end PairIntegral

section CoupledCovers
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem cluster_eq_iff_conn (G : BondGraph V E) (ω : Set E) (x y : V) :
    cluster G ω x = cluster G ω y ↔ Conn G ω x y := by
  constructor
  · intro h
    have hh := mem_cluster_self G ω y
    rwa [← h] at hh
  · exact cluster_eq_of_conn G ω

 
def TouchedCover (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    (labels : E → unitInterval) : Prop :=
  ∃ f : Fin n → V, ∀ x, (cluster G (openEdges labels p) x).Infinite →
    ∃ i, Conn G (openEdges labels q) x (f i)

theorem measurableSet_touchedCover (G : BondGraph V E) (p q : unitInterval) (n : ℕ) :
    MeasurableSet {labels | TouchedCover G p q n labels} := by
  have he : {labels | TouchedCover G p q n labels} =
      ⋃ f : Fin n → V, ⋂ x : V, ({labels | (cluster G (openEdges labels p) x).Infinite}ᶜ ∪
        ⋃ i : Fin n, {labels | Conn G (openEdges labels q) x (f i)}) := by
    ext labels
    simp only [TouchedCover, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    simp only [← imp_iff_not_or]
  rw [he]
  apply MeasurableSet.iUnion
  intro f
  apply MeasurableSet.iInter
  intro x
  exact ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p)).compl.union
    (MeasurableSet.iUnion fun i => (measurableSet_conn G x (f i)).preimage (measurable_openEdges q))

omit [Countable V] [Countable E] in
 
theorem survivor_count_sq_le (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    (F : Finset V) (labels : E → unitInterval) (h : TouchedCover G p q n labels) :
    ((F.filter fun x => (cluster G (openEdges labels p) x).Infinite).card : ℝ) ^ 2 ≤
      n * ∑ x ∈ F, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
  obtain ⟨f, hf⟩ := h
  let S := F.filter fun x => (cluster G (openEdges labels p) x).Infinite
  let c := cluster G (openEdges labels q)
  have hsub : S.image c ⊆ Finset.univ.image (fun i : Fin n => c (f i)) := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨i, hi⟩ := hf x (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (cluster_eq_of_conn G _ hi).symm⟩
  have hcard : (S.image c).card ≤ n :=
    (Finset.card_le_card hsub).trans (by simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => c (f i))))
  have hpair := card_sq_le_image_card_mul_pairs S c
  have hpairs : ∑ x ∈ S, ∑ y ∈ S, (if c x = c y then (1 : ℝ) else 0) ≤
      ∑ x ∈ F, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
    simp only [c, cluster_eq_iff_conn] 
    calc
      _ ≤ ∑ x ∈ S, ∑ y ∈ F, if Conn G (openEdges labels q) x y then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by split_ifs <;> positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
  exact hpair.trans ((mul_le_mul_of_nonneg_left hpairs (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)))

end CoupledCovers

section CoverInvariance
attribute [local instance] Classical.propDecidable

 
theorem labelLaw_map_precomp (b : E ≃ E) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => labels ∘ b) = labelLaw := by
  have he : (fun labels : E → unitInterval => labels ∘ b) =
      MeasurableEquiv.piCongrLeft (fun _ : E => unitInterval) b.symm := by
    funext labels e
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => unitInterval)
      b.symm labels (b e)
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using h.symm
  unfold labelLaw
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => (volume : Measure unitInterval)) b.symm

theorem infinite_cluster_precomp (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (labels : E → unitInterval) (p : unitInterval) (x : V) :
    (cluster G (openEdges (labels ∘ b) p) x).Infinite ↔
      (cluster G (openEdges labels p) (a x)).Infinite := by
  change (cluster G (b ⁻¹' openEdges labels p) x).Infinite ↔ _
  rw [← cluster_aut G h]
  exact (Set.infinite_image_iff (fun _ _ _ _ hab => a.injective hab)).symm

variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem touchedCover_precomp (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (labels : E → unitInterval) (p q : unitInterval) (n : ℕ) :
    TouchedCover G p q n (labels ∘ b) ↔ TouchedCover G p q n labels := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => a (f i), fun x hx => ?_⟩
    have hs : (cluster G (openEdges (labels ∘ b) p) (a.symm x)).Infinite :=
      (infinite_cluster_precomp G h labels p (a.symm x)).mpr (by simpa using hx)
    obtain ⟨i, hi⟩ := hf _ hs
    exact ⟨i, by simpa using (conn_aut_iff G h (openEdges labels q) (a.symm x) (f i)).mp hi⟩
  · rintro ⟨f, hf⟩
    refine ⟨fun i => a.symm (f i), fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hf (a x) ((infinite_cluster_precomp G h labels p x).mp hx)
    exact ⟨i, (conn_aut_iff G h (openEdges labels q) x (a.symm (f i))).mpr (by simpa using hi)⟩

theorem cover_survival_aut (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    (labelLaw : Measure (E → unitInterval)).real
      {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) (a x)).Infinite} =
    labelLaw.real {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite} := by
  have hm : Measurable (fun labels : E → unitInterval => labels ∘ b) :=
    Measurable.of_eval (fun e => measurable_pi_apply (b e))
  have hs : MeasurableSet {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite} :=
    (measurableSet_touchedCover G p q n).inter
      ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p))
  have he : {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) (a x)).Infinite} =
      (fun labels : E → unitInterval => labels ∘ b) ⁻¹'
        {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite} := by
    ext labels
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, touchedCover_precomp G h,
      infinite_cluster_precomp G h]
  simp only [Measure.real]
  rw [he, ← Measure.map_apply hm hs, labelLaw_map_precomp]

end CoverInvariance

section CoverObstruction
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

theorem cover_survival_square_sum_le (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G q A) (F : Finset V) :
    (∑ x ∈ F, (labelLaw : Measure (E → unitInterval)).real {labels |
      TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite}) ^ 2 ≤
      n * ‖A‖ * F.card := by
  let S := fun x => {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite}
  let C := fun x y => {labels | Conn G (openEdges labels q) x y}
  have hS (x) : MeasurableSet (S x) :=
    (measurableSet_touchedCover G p q n).inter
      ((measurableSet_infinite_cluster G x).preimage (measurable_openEdges p))
  have hC (x y) : MeasurableSet (C x y) :=
    (measurableSet_conn G x y).preimage (measurable_openEdges q)
  have hpoint (labels : E → unitInterval) :
      (∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) labels) ^ 2 ≤
      (n : ℝ) * ∑ x ∈ F, ∑ y ∈ F, (C x y).indicator (fun _ => (1 : ℝ)) labels := by
    by_cases hc : TouchedCover G p q n labels
    · have he : ∑ x ∈ F, (S x).indicator (fun _ => (1 : ℝ)) labels =
          ((F.filter fun x => (cluster G (openEdges labels p) x).Infinite).card : ℝ) := by
        simp only [S, Set.indicator, Set.mem_ofPred_eq, hc, true_and]
        rw [← Finset.sum_filter]
        simp
      rw [he]
      simpa only [C, Set.indicator, Set.mem_ofPred_eq] using
        survivor_count_sq_le G p q n F labels hc
    · simp only [S, Set.indicator, Set.mem_ofPred_eq, hc, false_and, ite_false,
        Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have h := square_sum_probability_le (labelLaw : Measure (E → unitInterval)) F S C hS hC
    (n : ℝ) hpoint
  have he (x y) : labelLaw.real (C x y) = twoPoint G q x y :=
    (twoPoint_eq_labelLaw G q x y).symm
  simp only [he] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (sum_twoPoint_le_norm_card G q hA F) (Nat.cast_nonneg n))

 

theorem measure_cover_survival_eq_zero [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p q : unitInterval) (hq : OperatorBounded G q) (n : ℕ) (x : V) :
    (labelLaw : Measure (E → unitInterval)) {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  by_contra hnz
  let θ := (labelLaw : Measure (E → unitInterval)).real {labels | TouchedCover G p q n labels ∧
      (cluster G (openEdges labels p) x).Infinite}
  have hθ : 0 < θ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hnz)
  obtain ⟨A, hA⟩ := hq
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) * ‖A‖ / θ ^ 2 + 1)
  obtain ⟨F, hF, hcard⟩ := (vertexOrbit_infinite G hconn hloc hqt x).exists_subset_card_eq m
  have he (y : V) (hy : y ∈ F) : (labelLaw : Measure (E → unitInterval)).real
      {labels | TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) y).Infinite} = θ := by
    obtain ⟨a, b, hab, hay⟩ := hF hy
    rw [← hay]
    exact cover_survival_aut G p q n hab x
  have hh := cover_survival_square_sum_le G p q n hA F
  rw [Finset.sum_congr rfl he] at hh
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hh
  have hθsq : 0 < θ ^ 2 := sq_pos_of_pos hθ
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity : (0 : ℝ) < (n : ℝ) * ‖A‖ / θ ^ 2 + 1) hm
  have hlt : (n : ℝ) * ‖A‖ < (m : ℝ) * θ ^ 2 := by
    apply (div_lt_iff₀ hθsq).mp
    linarith
  nlinarith

end CoverObstruction

section FiniteChanges
attribute [local instance] Classical.propDecidable

 
theorem cluster_union_subset (G : BondGraph V E) (ω : Set E) (F : Set E) (x : V) :
    cluster G (ω ∪ F) x ⊆ cluster G ω x ∪ ⋃ e ∈ F, ⋃ z ∈ {z | z ∈ G e}, cluster G ω z := by
  intro y hy
  induction hy with
  | refl => exact Or.inl (mem_cluster_self G ω x)
  | @tail y z hy hed ih =>
    obtain ⟨e, he, heq⟩ := hed
    rcases he with he | he
    · have hyz : Conn G ω y z := (conn_refl G ω y).tail ⟨e, he, heq⟩
      rcases ih with ih | ih
      · exact Or.inl (conn_trans G ω ih hyz)
      · right
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at ih ⊢
        obtain ⟨e', he', w, hw, hwy⟩ := ih
        exact ⟨e', he', w, hw, conn_trans G ω hwy hyz⟩
    · right
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨e, he, z, heq ▸ by simp, conn_refl G ω z⟩

theorem exists_infinite_cluster_mono (G : BondGraph V E) {ω ω' : Set E} (h : ω ⊆ ω') :
    (∃ x, (cluster G ω x).Infinite) → ∃ x, (cluster G ω' x).Infinite := by
  rintro ⟨x, hx⟩
  exact ⟨x, hx.mono (fun _ hy => conn_mono G h hy)⟩

 
theorem exists_infinite_cluster_sdiff (G : BondGraph V E) (ω : Set E)
    {F : Set E} (hF : F.Finite) :
    (∃ x, (cluster G (ω \ F) x).Infinite) ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · exact exists_infinite_cluster_mono G Set.sdiff_subset
  · contrapose!
    intro h x
    have hs : (cluster G (ω \ F) x ∪
        ⋃ e ∈ F, ⋃ z ∈ {z | z ∈ G e}, cluster G (ω \ F) z).Finite := by
      apply (h x).union
      apply hF.biUnion
      intro e _
      have he : {z | z ∈ G e}.Finite := by
        exact (G e).toFinset.finite_toSet.subset (fun z hz => by simpa using hz)
      exact he.biUnion (fun z _ => h z)
    apply hs.subset
    apply Set.Subset.trans (fun y hy => conn_mono G (Set.subset_sdiff_union _ _) hy)
    exact cluster_union_subset G (ω \ F) F x

end FiniteChanges

section PercolationZeroOne
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] [Countable E] in
theorem infiniteClusters_nonempty_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hC, x, rfl⟩
    exact ⟨x, hC⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

 theorem measurableSet_exists_infinite_cluster (G : BondGraph V E) :
    MeasurableSet {ω : Set E | ∃ x, (cluster G ω x).Infinite} := by
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (fun x => measurableSet_infinite_cluster G x)

 theorem infinite_cluster_zero_one (G : BondGraph V E) (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} = 0 ∨
    (labelLaw : Measure (E → unitInterval))
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} = 1 := by
  let σ : E → MeasurableSpace (E → unitInterval) := fun e =>
    MeasurableSpace.comap (fun labels : E → unitInterval => labels e) inferInstance
  have hle (e) : σ e ≤ (inferInstance : MeasurableSpace (E → unitInterval)) := (measurable_pi_apply e).comap_le
  have hi : iIndep σ (labelLaw : Measure (E → unitInterval)) :=
    iIndepFun_infinitePi (X := fun (_ : E) (x : unitInterval) => x) (fun _ => measurable_id)
  have htail : MeasurableSet[Filter.limsup σ Filter.cofinite]
      {labels | ∃ x, (cluster G (openEdges labels p) x).Infinite} := by
    rw [Filter.limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro hs
    have hfin : sᶜ.Finite := Filter.mem_cofinite.mp hs
    let m := ⨆ e ∈ s, σ e
    have hm : @Measurable (E → unitInterval) (Set E) m inferInstance
        (fun labels => openEdges labels p ∩ s) := by
      apply measurable_setOfPred.comp
      apply Measurable.of_eval
      intro e
      change @Measurable (E → unitInterval) Prop m inferInstance (fun labels => labels e ≤ p ∧ e ∈ s)
      by_cases he : e ∈ s
      · have hev : @Measurable (E → unitInterval) unitInterval m inferInstance
            (fun labels => labels e) :=
          Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
        simpa only [he, and_true, Function.comp_def]
          using (measurable_threshold p).comp hev
      · simpa only [he, and_false]
          using (measurable_const : @Measurable (E → unitInterval) Prop m inferInstance
            (fun _ => False))
    have heq : {labels : E → unitInterval | ∃ x, (cluster G (openEdges labels p) x).Infinite} =
        {labels | ∃ x, (cluster G (openEdges labels p ∩ s) x).Infinite} := by
      ext labels
      simpa only [Set.sdiff_compl, Set.mem_ofPred_eq] using
        (exists_infinite_cluster_sdiff G (openEdges labels p) hfin).symm
    rw [heq]
    exact (measurableSet_exists_infinite_cluster G).preimage hm
  exact measure_zero_or_one_of_measurableSet_limsup
    (s := σ) (f := Filter.cofinite) (p := Set.Finite)
    (ns := fun F : Finset E => (F : Set E)) hle hi
    (fun t ht => by simpa using ht)
    (fun F H => ⟨F ∪ H, Finset.coe_subset.mpr Finset.subset_union_left,
      Finset.coe_subset.mpr Finset.subset_union_right⟩)
    (fun F => F.finite_toSet) (fun e => ⟨{e}, by simp⟩) htail

end PercolationZeroOne

section CoupledInterval
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

 theorem exists_infinite_cluster_probability_mono (G : BondGraph V E) {p q : unitInterval}
    (hpq : p ≤ q) :
    law p {ω | (infiniteClusters G ω).Nonempty} ≤
      law q {ω | (infiniteClusters G ω).Nonempty} := by
  have hm : MeasurableSet {ω : Set E | (infiniteClusters G ω).Nonempty} := by
    simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  rw [← map_openEdges p, ← map_openEdges q,
    Measure.map_apply (measurable_openEdges p) hm,
    Measure.map_apply (measurable_openEdges q) hm]
  apply measure_mono
  intro labels h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, infiniteClusters_nonempty_iff] at h ⊢
  exact exists_infinite_cluster_mono G (openEdges_mono labels hpq) h

 theorem ae_exists_infinite_cluster_of_pc_lt (G : BondGraph V E) (p : unitInterval)
    (hp : pc G < p) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∃ x, (cluster G (openEdges labels p) x).Infinite := by
  obtain ⟨q, hq, hqp⟩ := sInf_lt_iff.mp hp
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} :=
    lt_of_lt_of_le hq (exists_infinite_cluster_probability_mono G hqp.le)
  have hm : MeasurableSet {ω : Set E | (infiniteClusters G ω).Nonempty} := by
    simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  rw [← map_openEdges p, Measure.map_apply (measurable_openEdges p) hm] at hpos
  simp only [Set.preimage_ofPred_eq, infiniteClusters_nonempty_iff] at hpos
  have hpone := (infinite_cluster_zero_one G p).resolve_left (ne_of_gt hpos)
  exact (mem_ae_iff_prob_eq_one
    ((measurableSet_exists_infinite_cluster G).preimage (measurable_openEdges p))).mpr hpone

omit [Countable V] [Countable E] in
 theorem touchedCover_of_finite_infiniteClusters (G : BondGraph V E)
    (labels : E → unitInterval) {p r q : unitInterval} (hpr : p ≤ r) (hrq : r ≤ q)
    (hfinite : (infiniteClusters G (openEdges labels r)).Finite) :
    ∃ n, TouchedCover G p q n labels := by
  let C := infiniteClusters G (openEdges labels r)
  let : Fintype C := hfinite.fintype
  let f : C → V := fun c => Classical.choose c.property.2
  have hf (c : C) : c.val = cluster G (openEdges labels r) (f c) :=
    Classical.choose_spec c.property.2
  refine ⟨Fintype.card C, fun i => f ((Fintype.equivFin C).symm i), ?_⟩
  intro x hx
  have hx' : (cluster G (openEdges labels r) x).Infinite :=
    hx.mono (fun _ hy => conn_mono G (openEdges_mono labels hpr) hy)
  let c : C := ⟨cluster G (openEdges labels r) x, hx', x, rfl⟩
  refine ⟨Fintype.equivFin C c, ?_⟩
  simp only [Equiv.symm_apply_apply]
  apply conn_mono G (openEdges_mono labels hrq)
  change f c ∈ cluster G (openEdges labels r) x
  change f c ∈ c.val
  rw [hf c]
  exact mem_cluster_self G _ _

 

 theorem coupled_interval [Infinite V] (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p q : unitInterval) (hp : pc G < p) (hq : OperatorBounded G q) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ r ∈ Set.Icc p q, (infiniteClusters G (openEdges labels r)).Infinite := by
  have hall : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ n x,
      ¬(TouchedCover G p q n labels ∧ (cluster G (openEdges labels p) x).Infinite) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro x
    apply ae_iff.mpr
    simpa only [not_not] using measure_cover_survival_eq_zero G hconn hloc hqt p q hq n x
  filter_upwards [hall, ae_exists_infinite_cluster_of_pc_lt G p hp] with labels hlabels hex
  intro r hr
  by_contra hfinite
  obtain ⟨n, hn⟩ := touchedCover_of_finite_infiniteClusters G labels hr.1 hr.2
    (Set.not_infinite.mp hfinite)
  obtain ⟨x, hx⟩ := hex
  exact hlabels n x ⟨hn, hx⟩

end CoupledInterval

end Percolation

end OAI
