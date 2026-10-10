import Mathlib
import OAI.Analysis.BoundedHochschild.WalkEndpoints

namespace OAI

/-! Concatenation estimates and finite and countable random-walk selection. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

 
def flattenRows {t n : ℕ} (w : Fin t → Fin n → G) : Fin (t*n) → G :=
  fun q => w (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma word_flattenRows {t n : ℕ} (w : Fin t → Fin n → G) :
    word (flattenRows w) = word (fun i => word (w i)) := by
  unfold word
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply]
  congr 1
  congr 1
  funext j
  have he : (⟨i*n+j, by nlinarith [i.isLt,j.isLt]⟩ : Fin (t*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    dsimp [finProdFinEquiv]
    ac_rfl
  change flattenRows w ⟨i*n+j, _⟩ = w i j
  rw [he]
  simp [flattenRows]

 
def orientRow {n : ℕ} (s : Bool) (w : Fin n → G) : Fin n → G :=
  fun i => signed s (w (if s then i else i.rev))

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma word_orientRow {n : ℕ} (s : Bool) (w : Fin n → G) :
    word (orientRow s w) = signed s (word w) := by
  cases s
  · exact reversePath_prod n w
  · rfl

 
def blockIndex {t m n : ℕ} (index : Fin t → Fin m) (sign : Fin t → Bool) :
    Fin t × Fin n → Fin m × Fin n :=
  fun p => (index p.1, if sign p.1 then p.2 else p.2.rev)

lemma blockIndex_injective {t m n : ℕ} (index : Fin t → Fin m) (hi : Function.Injective index)
    (sign : Fin t → Bool) : Function.Injective (blockIndex (n := n) index sign) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  have hii : i=i' := hi (congrArg Prod.fst he)
  subst i'
  have hj := congrArg Prod.snd he
  dsimp [blockIndex] at hj
  by_cases hs : sign i = true
  · simp only [hs, ↓reduceIte] at hj
    exact Prod.ext rfl hj
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hj
    exact Prod.ext rfl (Fin.rev_injective hj)

lemma concatenated_preserving (hsym : μ.map (fun g => g⁻¹) = μ)
    {t m n : ℕ} (index : Fin t → Fin m) (hi : Function.Injective index) (sign : Fin t → Bool) :
    MeasurePreserving
      (fun w : Fin m × Fin n → G => flattenRows (fun i => orientRow (sign i) (fun j => w (index i,j))))
      (Measure.pi (fun _ : Fin m × Fin n => μ)) (Measure.pi (fun _ : Fin (t*n) => μ)) := by
  have hi' : Function.Injective (fun q : Fin (t*n) => blockIndex index sign (finProdFinEquiv.symm q)) :=
    (blockIndex_injective index hi sign).comp finProdFinEquiv.symm.injective
  have he := iid_signed_extract μ hsym _ hi' (fun q => sign (finProdFinEquiv.symm q).1)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma flattenRows_prefix {t n : ℕ} (w : Fin (t+1) → Fin n → G)
    (hle : n ≤ (t+1)*n) :
    (fun i : Fin n => flattenRows w (Fin.castLE hle i)) = w 0 := by
  funext i
  have he : Fin.castLE hle i = finProdFinEquiv ((0 : Fin (t+1)),i) := by
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [he]
  simp [flattenRows]

variable {H : Type*} [NormedAddCommGroup H]

 

theorem concatenated_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    {t m n : ℕ} (index : Fin (t+1) → Fin m) (hi : Function.Injective index)
    (sign : Fin (t+1) → Bool) :
    ∫ w : Fin m × Fin n → G,
      ‖D (word (fun i => signed (sign i) (word (fun j => w (index i,j))))) -
        D (signed (sign 0) (word (fun j => w (index 0,j))))‖^2
      ∂Measure.pi (fun _ : Fin m × Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ := by
  have hn : n ≤ (t+1)*n := by nlinarith
  let F (w : Fin ((t+1)*n) → G) :=
    ‖D (word w)-D (word (fun i : Fin n => w (Fin.castLE hn i)))‖^2
  have he := (integral_map_of_stronglyMeasurable
    (μ := Measure.pi (fun _ : Fin m × Fin n => μ))
    (concatenated_preserving μ hsym index hi sign).measurable
    (StronglyMeasurable.of_discrete (f := F))).symm
  rw [(concatenated_preserving μ hsym index hi sign).map_eq] at he
  calc
    _ = ∫ w : Fin m × Fin n → G,
        F (flattenRows (fun i => orientRow (sign i) (fun j => w (index i,j))))
        ∂Measure.pi (fun _ : Fin m × Fin n => μ) := by
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro w
      dsimp [F]
      rw [word_flattenRows, flattenRows_prefix _ hn]
      simp only [word_orientRow]
    _ = ∫ w, F w ∂Measure.pi (fun _ : Fin ((t+1)*n) => μ) := he
    _ ≤ _ := finite_cauchy_bound μ D z hc n ((t+1)*n) hn

omit [Group G] in
 
lemma rows_preserving (m n : ℕ) :
    MeasurePreserving (fun w : Fin m × Fin n → G => fun i j => w (i,j))
      (Measure.pi (fun _ : Fin m × Fin n => μ))
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => μ))) := by
  refine ⟨measurable_of_countable _, ?_⟩
  have he := Measure.infinitePi_map_curry (μ := fun _ : Fin m => fun _ : Fin n => μ)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Group G] in
 
lemma rows_event_mass (m n : ℕ) (E : Set (Fin n → G)) :
    (Measure.pi (fun _ : Fin m × Fin n => μ)).real {w | ∀ i, (fun j => w (i,j)) ∈ E} =
      ((Measure.pi (fun _ : Fin n => μ)).real E)^m := by
  have hm := (rows_preserving μ m n).measureReal_preimage
    (s := Set.pi Set.univ (fun _ : Fin m => E)) (Set.to_countable _).measurableSet.nullMeasurableSet
  simp only [MeasureTheory.measureReal_def] at hm
  rw [Measure.pi_pi] at hm
  simpa [Set.pi, ENNReal.toReal_pow, MeasureTheory.measureReal_def] using hm

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildProbability

 

theorem finite_requirements_eventually {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsFiniteMeasure (μ n)]
    (E : ∀ n, Set (X n)) {c : ℝ} (hc : 0 < c)
    (hE : ∀ᶠ n in atTop, c ≤ (μ n).real (E n))
    {I : Type*} (s : Finset I) (B : ∀ n, I → Set (X n))
    (hB : ∀ i ∈ s, Tendsto (fun n => (μ n).real (B n i)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ∃ x ∈ E n, ∀ i ∈ s, x ∉ B n i := by
  classical
  have ht : Tendsto (fun n => ∑ i ∈ s, (μ n).real (B n i)) atTop (nhds 0) := by
    simpa using tendsto_finsetSum s hB
  filter_upwards [hE, ht.eventually (gt_mem_nhds hc)] with n hEn hBn
  by_contra h
  push Not at h
  have he : E n ⊆ ⋃ i ∈ s, B n i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hxi⟩⟩
  have hl := (measureReal_mono (μ := μ n) he (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le s (B n))
  exact (not_lt_of_ge (hEn.trans hl)) hBn

 

theorem select_finite_stages {X : ℕ → ℕ → Type*}
    [∀ m n, MeasurableSpace (X m n)]
    (μ : ∀ m n, Measure (X m n)) [∀ m n, IsFiniteMeasure (μ m n)]
    (E : ∀ m n, Set (X m n))
    (hE : ∀ m, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ (μ m n).real (E m n))
    {I : ℕ → Type*} (s : ∀ m, Finset (I m))
    (B : ∀ m n, I m → Set (X m n))
    (hB : ∀ m i, i ∈ s m → Tendsto (fun n => (μ m n).real (B m n i)) atTop (nhds 0)) :
    ∃ (time : ℕ → ℕ) (x : ∀ m, X m (time m)), Tendsto time atTop atTop ∧
      ∀ m, x m ∈ E m (time m) ∧ ∀ i ∈ s m, x m ∉ B m (time m) i := by
  classical
  have hex (m : ℕ) : ∃ n ≥ m, ∃ x ∈ E m n, ∀ i ∈ s m, x ∉ B m n i := by
    obtain ⟨c, hc, hEc⟩ := hE m
    have he := finite_requirements_eventually (μ m) (E m) hc hEc (s m) (B m) (hB m)
    obtain ⟨n, hn, h⟩ := (he.and (eventually_ge_atTop m)).exists
    exact ⟨n, h, hn⟩
  choose time htime x hx using hex
  exact ⟨time, x, tendsto_atTop_mono htime tendsto_id, hx⟩

end HochschildProbability

namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

 
def evalList {I : Type*} (u : I → G) (l : List (I × Bool)) : G :=
  (l.map (fun a => signed a.2 (u a.1))).prod

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma evalList_ofFn {I : Type*} {t : ℕ} (u : I → G) (f : Fin t → I × Bool) :
    evalList u (List.ofFn f) = word (fun i => signed (f i).2 (u (f i).1)) := by
  simp [evalList, word, List.map_ofFn, Function.comp_def]

 
lemma list_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    {m n : ℕ} (a : Fin m × Bool) (l : List (Fin m × Bool))
    (hl : ((a::l).map Prod.fst).Nodup) :
    ∫ w : Fin m × Fin n → G,
      ‖D (evalList (fun i => word (fun j => w (i,j))) (a::l)) -
        D (signed a.2 (word (fun j => w (a.1,j))))‖^2
      ∂Measure.pi (fun _ : Fin m × Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ := by
  let f : Fin (l.length+1) → Fin m × Bool := (a::l).get
  have hi : Function.Injective (fun k => (f k).1) := by
    intro i j he
    have he' : ((a::l).map Prod.fst).get ⟨i, by simpa using i.isLt⟩ =
        ((a::l).map Prod.fst).get ⟨j, by simpa using j.isLt⟩ := by
      dsimp [f] at he
      simpa only [List.get_eq_getElem, List.getElem_map] using he
    exact Fin.ext (congrArg (fun q : Fin (((a::l).map Prod.fst).length) => q.val)
      (hl.injective_get he'))
  have hb := concatenated_cauchy_bound μ hsym D z hc (n := n) (fun k => (f k).1) hi (fun k => (f k).2)
  have he : List.ofFn f = a::l := List.ofFn_get (a::l)
  have hev (w : Fin m × Fin n → G) :
      evalList (fun i => word (fun j => w (i,j))) (a::l) =
        word (fun k => signed (f k).2 (word (fun j => w ((f k).1,j)))) := by
    rw [← he, evalList_ofFn]
  simpa only [← hev, f, List.get_cons_zero] using hb

 

theorem finite_walk_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (m : ℕ) {I : Type*} (Q : Finset I) (obs : I → (Fin m → G) → ℝ)
    (V : Finset ((Fin m × Bool) × List (Fin m × Bool)))
    (hV : ∀ v ∈ V, ((v.1::v.2).map Prod.fst).Nodup)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (δ : ℝ) (hδ : 0 < δ)
    (hmom : ∀ q ∈ Q, Tendsto (fun k =>
      (Measure.pi (fun _ : Fin m × Fin (time k) => μ)).real
        {w | δ ≤ obs q (fun i => word (fun j => w (i,j)))}) atTop (nhds 0)) :
    ∃ u : Fin m → G,
      (∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ) ∧
      (∀ q ∈ Q, obs q u < δ) ∧
      ∀ v ∈ V, ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖ < δ := by
  classical
  let ν (k : ℕ) := Measure.pi (fun _ : Fin m × Fin (time k) => μ)
  let E (k : ℕ) : Set (Fin m × Fin (time k) → G) :=
    {w | ∀ i, ‖D (word (fun j => w (i,j)))-a‖ < δ ∧
      ‖D ((word (fun j => w (i,j)))⁻¹)-b‖ < δ}
  obtain ⟨η,hη,N,hN⟩ := endpoint_mass_eventually μ hsym D C hD z hz hc a b ha hb δ hδ
  have hmass : ∀ᶠ k in atTop, η^m ≤ (ν k).real (E k) := by
    filter_upwards [htime.eventually (eventually_ge_atTop N)] with k hk
    rw [show (ν k).real (E k) =
        ((Measure.pi (fun _ : Fin (time k) => μ)).real
          {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ})^m from
      rows_event_mass μ m (time k)
        {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ}]
    exact pow_le_pow_left₀ hη.le (hN _ hk) m
  let B (k : ℕ) : I ⊕ ((Fin m × Bool) × List (Fin m × Bool)) →
      Set (Fin m × Fin (time k) → G)
    | Sum.inl q => {w | δ ≤ obs q (fun i => word (fun j => w (i,j)))}
    | Sum.inr v => {w | δ ≤ ‖D (evalList (fun i => word (fun j => w (i,j))) (v.1::v.2)) -
        D (signed v.1.2 (word (fun j => w (v.1.1,j))))‖}
  have hbad (q) (hq : q ∈ Q.disjSum V) :
      Tendsto (fun k => (ν k).real (B k q)) atTop (nhds 0) := by
    cases q with
    | inl q => exact hmom q (Finset.inl_mem_disjSum.mp hq)
    | inr v =>
      have hv := hV v (Finset.inr_mem_disjSum.mp hq)
      have hbound (k : ℕ) : (ν k).real (B k (.inr v)) ≤
          (∫ ω, ‖z ω-D (walk (time k) ω)‖^2 ∂pathMeasure μ)/δ^2 := by
        let f (w : Fin m × Fin (time k) → G) :=
          D (evalList (fun i => word (fun j => w (i,j))) (v.1::v.2)) -
            D (signed v.1.2 (word (fun j => w (v.1.1,j))))
        have hf : MemLp f 2 (ν k) := MemLp.of_bound
          StronglyMeasurable.of_discrete.aestronglyMeasurable (C+C)
          (Eventually.of_forall fun w => (norm_sub_le _ _).trans (add_le_add (hD _) (hD _)))
        exact (HochschildProbability.norm_error_mass (ν k) f hf hδ).trans
          (div_le_div_of_nonneg_right (list_cauchy_bound μ hsym D z hc v.1 v.2 hv) (sq_nonneg _))
      apply squeeze_zero (fun k => measureReal_nonneg) hbound
      simpa using (hz.comp htime).div_const (δ^2)
  obtain ⟨k,w,hwE,hwB⟩ := (HochschildProbability.finite_requirements_eventually ν E
    (pow_pos hη m) hmass (Q.disjSum V) B hbad).exists
  refine ⟨fun i => word (fun j => w (i,j)), hwE, ?_, ?_⟩
  · intro q hq
    exact lt_of_not_ge (hwB (.inl q) (Finset.inl_mem_disjSum.mpr hq))
  · intro v hv
    exact lt_of_not_ge (hwB (.inr v) (Finset.inr_mem_disjSum.mpr hv))

end HochschildWalk

open Filter Topology
namespace HochschildFiniteTests

 
theorem finite_alphabet (F : Finset ℕ) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : ℕ → Fin r, ∀ i ∈ F, (c i : ℕ) = i := by
  let r := F.sup id + 1
  have hr : 0 < r := Nat.succ_pos _
  refine ⟨r, hr, fun i => ⟨i % r, Nat.mod_lt i hr⟩, ?_⟩
  intro i hi
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))

lemma map_back_word {r : ℕ} (c : ℕ → Fin r) (g : FreeGroup ℕ)
    (hc : ∀ p ∈ g.toWord, (c p.1 : ℕ) = p.1) :
    FreeGroup.map (fun i : Fin r => (i : ℕ)) (FreeGroup.map c g) = g := by
  have he : (g.toWord.map (fun p => (c p.1,p.2))).map
      (fun p : Fin r × Bool => ((p.1 : ℕ),p.2)) = g.toWord := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id g.toWord]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply, hc p hp, id_eq]
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
  rw [FreeGroup.map.mk, FreeGroup.map.mk, he, FreeGroup.mk_toWord]

lemma map_ne_one {r : ℕ} (c : ℕ → Fin r) (g : FreeGroup ℕ)
    (hc : ∀ p ∈ g.toWord, (c p.1 : ℕ) = p.1) (hg : g ≠ 1) :
    FreeGroup.map c g ≠ 1 := by
  intro h
  apply hg
  rw [← map_back_word c g hc, h, map_one]

lemma map_nodup {r : ℕ} (c : ℕ → Fin r) (l : List (ℕ × Bool))
    (hc : ∀ p ∈ l, (c p.1 : ℕ) = p.1) (hl : (l.map Prod.fst).Nodup) :
    ((l.map (fun p => (c p.1,p.2))).map Prod.fst).Nodup := by
  have hinj : ∀ i ∈ l.map Prod.fst, ∀ j ∈ l.map Prod.fst, c i = c j → i = j := by
    intro i hi j hj he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
    have hv := congrArg Fin.val he
    simpa only [hc p hp, hc q hq] using hv
  simpa only [List.map_map, Function.comp_def] using List.Nodup.map_on hinj hl

lemma lift_map {α β G : Type*} [Group G] (f : α → β) (u : β → G) (g : FreeGroup α) :
    FreeGroup.lift u (FreeGroup.map f g) = FreeGroup.lift (u ∘ f) g := by
  have he : (FreeGroup.lift u).comp (FreeGroup.map f) = FreeGroup.lift (u ∘ f) := by
    ext i
    simp
  exact DFunLike.congr_fun he g

 

theorem countable_constraints {X I : Type*} [Nonempty I] [Countable I]
    (P : I → Prop) (E : I → X → ℝ) (hE : ∀ i x, 0 ≤ E i x)
    (R : ℝ → X → Prop)
    (hfinite : ∀ (s : Finset I) (δ : ℝ), 0 < δ →
      ∃ x : X, R δ x ∧ ∀ i ∈ s, P i → E i x < δ) :
    ∃ x : ℕ → X, (∀ n : ℕ, R (1/(n+1:ℝ)) (x n)) ∧
      ∀ i, P i → Tendsto (fun n => E i (x n)) atTop (nhds 0) := by
  classical
  obtain ⟨enum,henum⟩ := exists_surjective_nat I
  have hex (n : ℕ) : ∃ x : X, R (1/(n+1:ℝ)) x ∧
      ∀ i ∈ (Finset.range (n+1)).image enum, P i → E i x < 1/(n+1:ℝ) :=
    hfinite _ _ (by positivity)
  choose x hx using hex
  refine ⟨x, fun n => (hx n).1, ?_⟩
  intro i hi
  obtain ⟨k,rfl⟩ := henum i
  apply squeeze_zero' (Eventually.of_forall fun n => hE _ _)
    (g := fun n : ℕ => 1/(n+1:ℝ))
  · filter_upwards [eventually_ge_atTop k] with n hn
    exact ((hx n).2 _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩) hi).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

end HochschildFiniteTests

 

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
open HochschildFiniteTests
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

 
def FreeMomentsInProbability (φ : G → ℝ) (time : ℕ → ℕ) : Prop :=
  ∀ r (q : FreeGroup (Fin r)), q ≠ 1 → ∀ δ > 0,
    Tendsto (fun k => (Measure.pi (fun _ : Fin r × Fin (time k) => μ)).real
      {w | δ ≤ φ (FreeGroup.lift (fun i => word (fun j => w (i,j))) q)}) atTop (nhds 0)

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma evalList_map {I J : Type*} (c : I → J) (u : J → G) (l : List (I × Bool)) :
    evalList u (l.map (fun p => (c p.1,p.2))) = evalList (u ∘ c) l := by
  simp [evalList, List.map_map, Function.comp_def]

 

theorem finite_countable_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (φ : G → ℝ) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ φ time)
    (Q : Finset (FreeGroup ℕ)) (hQ : ∀ q ∈ Q, q ≠ 1)
    (V : Finset ((ℕ × Bool) × List (ℕ × Bool)))
    (hV : ∀ v ∈ V, ((v.1::v.2).map Prod.fst).Nodup)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ u : ℕ → G,
      (∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ) ∧
      (∀ q ∈ Q, φ (FreeGroup.lift u q) < δ) ∧
      ∀ v ∈ V, ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖ < δ := by
  classical
  let F := Q.biUnion (fun q => (q.toWord.map Prod.fst).toFinset) ∪
    V.biUnion (fun v => ((v.1::v.2).map Prod.fst).toFinset)
  obtain ⟨r,hr,c,hcF⟩ := finite_alphabet F
  have hcQ (q) (hq : q ∈ Q) (p) (hp : p ∈ q.toWord) : (c p.1 : ℕ) = p.1 := by
    apply hcF
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨q,hq,List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩
  have hcV (v) (hv : v ∈ V) (p) (hp : p ∈ v.1::v.2) : (c p.1 : ℕ) = p.1 := by
    apply hcF
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨v,hv,List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩
  let clip : ((ℕ × Bool) × List (ℕ × Bool)) → ((Fin r × Bool) × List (Fin r × Bool)) :=
    fun v => ((c v.1.1,v.1.2), v.2.map (fun p => (c p.1,p.2)))
  have hclip (v) (hv : v ∈ V.image clip) : ((v.1::v.2).map Prod.fst).Nodup := by
    obtain ⟨v',hv',rfl⟩ := Finset.mem_image.mp hv
    exact map_nodup c (v'.1::v'.2) (hcV v' hv') (hV v' hv')
  have hobs (q) (hq : q ∈ Q) := hmom r (FreeGroup.map c q)
    (map_ne_one c q (hcQ q hq) (hQ q hq)) δ hδ
  obtain ⟨u,hu,hq,hv⟩ := finite_walk_selection μ hsym D C hD z hz hc a b ha hb r Q
    (fun q u => φ (FreeGroup.lift u (FreeGroup.map c q))) (V.image clip) hclip time htime δ hδ hobs
  refine ⟨u ∘ c, fun i => hu (c i), ?_, ?_⟩
  · intro q hqQ
    simpa only [lift_map] using hq q hqQ
  · intro v hvV
    have hh := hv (clip v) (Finset.mem_image.mpr ⟨v,hvV,rfl⟩)
    change ‖D (evalList u ((v.1::v.2).map (fun p => (c p.1,p.2)))) -
      D (signed v.1.2 (u (c v.1.1)))‖ < δ at hh
    rw [evalList_map] at hh
    exact hh

 

theorem infinite_walk_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (φ : G → ℝ) (hφ : ∀ g, 0 ≤ φ g) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ φ time) :
    ∃ u : ℕ → ℕ → G,
      (∀ n i, ‖D (u n i)-a‖ < 1/(n+1:ℝ) ∧ ‖D ((u n i)⁻¹)-b‖ < 1/(n+1:ℝ)) ∧
      (∀ q : FreeGroup ℕ, q ≠ 1 → Tendsto (fun n => φ (FreeGroup.lift (u n) q)) atTop (nhds 0)) ∧
      ∀ v : ((ℕ × Bool) × List (ℕ × Bool)), ((v.1::v.2).map Prod.fst).Nodup →
        Tendsto (fun n => ‖D (evalList (u n) (v.1::v.2))-D (signed v.1.2 (u n v.1.1))‖)
          atTop (nhds 0) := by
  classical
  let I := FreeGroup ℕ ⊕ ((ℕ × Bool) × List (ℕ × Bool))
  let P : I → Prop
    | .inl q => q ≠ 1
    | .inr v => ((v.1::v.2).map Prod.fst).Nodup
  let E : I → (ℕ → G) → ℝ
    | .inl q, u => φ (FreeGroup.lift u q)
    | .inr v, u => ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖
  let R : ℝ → (ℕ → G) → Prop := fun δ u =>
    ∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ
  have hE (i : I) (u : ℕ → G) : 0 ≤ E i u := by
    cases i with
    | inl q => exact hφ _
    | inr v => exact norm_nonneg _
  have hf (s : Finset I) (δ : ℝ) (hδ : 0 < δ) :
      ∃ u, R δ u ∧ ∀ i ∈ s, P i → E i u < δ := by
    let Q := s.toLeft.filter (fun q => q ≠ 1)
    let V := s.toRight.filter (fun v => ((v.1::v.2).map Prod.fst).Nodup)
    obtain ⟨u,hu,hq,hv⟩ := finite_countable_selection μ hsym D C hD z hz hc a b ha hb
      φ time htime hmom Q (fun _ h => (Finset.mem_filter.mp h).2)
      V (fun _ h => (Finset.mem_filter.mp h).2) δ hδ
    refine ⟨u,hu,?_⟩
    intro i hi hPi
    cases i with
    | inl q => exact hq q (Finset.mem_filter.mpr ⟨Finset.mem_toLeft.mpr hi,hPi⟩)
    | inr v => exact hv v (Finset.mem_filter.mpr ⟨Finset.mem_toRight.mpr hi,hPi⟩)
  obtain ⟨u,hu,hall⟩ := countable_constraints P E hE R hf
  exact ⟨u,hu,fun q hq => hall (.inl q) hq, fun v hv => hall (.inr v) hv⟩

end HochschildWalk
end

end OAI
