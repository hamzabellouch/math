import Mathlib
import OAI.Analysis.SymmetricDomains.FiberPolynomialNatDegree

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem fiber_card_of_sheets {X Y K : Type*} [Fintype K]
    (π : X → Y) (hfin : ∀ y, (π ⁻¹' {y}).Finite) (y : Y)
    (s : K → X) (hinj : Function.Injective s)
    (hs : ∀ x, π x = y ↔ ∃ j, s j = x) :
    (hfin y).toFinset.card = Fintype.card K := by
  classical
  rw [← Finset.card_univ]
  symm
  apply Finset.card_bij (fun j _ => s j)
  · intro j _
    exact (hfin y).mem_toFinset.mpr ((hs (s j)).mpr ⟨j,rfl⟩)
  · intro j _ k _ hjk
    exact hinj hjk
  · intro x hx
    obtain ⟨j,hj⟩ := (hs x).mp ((hfin y).mem_toFinset.mp hx)
    exact ⟨j,Finset.mem_univ _,hj⟩

theorem coeff_X_sub_C_mul_all (p : Polynomial ℂ) (r : ℂ) (k : ℕ) :
    ((X - C r) * p).coeff k = (if k = 0 then 0 else p.coeff (k-1)) - r * p.coeff k := by
  cases k with
  | zero => simp [sub_mul]
  | succ k => simp [coeff_X_sub_C_mul]

theorem analyticAt_coeff_prod_X_sub_C {E J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : Finset J) (f : J → E → ℂ) {a : E}
    (hf : ∀ j ∈ I, AnalyticAt ℂ (f j) a) (k : ℕ) :
    AnalyticAt ℂ (fun y => (∏ j ∈ I, (X - C (f j y))).coeff k) a := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : Polynomial ℂ).coeff k) a)
  | @insert j I hj ih =>
    simp only [Finset.prod_insert hj, coeff_X_sub_C_mul_all]
    by_cases hk : k = 0
    · subst k
      simpa using ((hf j (Finset.mem_insert_self _ _)).fun_mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) 0)).fun_neg
    · simpa [hk] using (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) (k-1)).fun_sub
        ((hf j (Finset.mem_insert_self _ _)).fun_mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) k))

theorem norm_coeff_prod_X_sub_C_le {J : Type*} (I : Finset J) (f : J → ℂ)
    (hf : ∀ j ∈ I, ‖f j‖ ≤ 1) (k : ℕ) :
    ‖(∏ j ∈ I, (X - C (f j))).coeff k‖ ≤ (2 : ℝ) ^ I.card := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> simp
  | @insert j I hj ih =>
    simp only [Finset.prod_insert hj, coeff_X_sub_C_mul_all, Finset.card_insert_of_notMem hj,
      pow_succ]
    have hI := fun k => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) k
    have hmul : ‖f j * (∏ l ∈ I, (X - C (f l))).coeff k‖ ≤ (2 : ℝ) ^ I.card := by
      rw [norm_mul]
      exact (mul_le_mul (hf j (Finset.mem_insert_self _ _)) (hI k)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have hfirst : ‖if k = 0 then 0 else (∏ l ∈ I, (X - C (f l))).coeff (k-1)‖ ≤
        (2 : ℝ) ^ I.card := by
      split_ifs <;> simp_all
    exact (norm_sub_le _ _).trans (by nlinarith [hfirst, hmul])

theorem monic_natDegree_prod_X_sub_C {J : Type*} (I : Finset J) (f : J → ℂ) :
    (∏ j ∈ I, (X - C (f j))).Monic ∧
    (∏ j ∈ I, (X - C (f j))).natDegree = I.card := by
  exact ⟨monic_prod_of_monic _ _ (fun index _ => monic_X_sub_C (f index)), by
    rw [natDegree_prod _ _ (fun j _ => (monic_X_sub_C (f j)).ne_zero)]
    simp⟩

theorem exists_vector_prod_X_sub_C {J : Type*} (I : Finset J) (f : J → ℂ)
    {r : ℕ} (hr : I.card = r) :
    ∃ v : (Fin r → ℂ),
      (∀ j, ∃ x ∈ I, v j = f x) ∧
      (∏ x ∈ I, (X - C (f x))) = ∏ j : Fin r, (X - C (v j)) := by
  classical
  let e : I ≃ Fin r := Finset.equivFinOfCardEq hr
  refine ⟨fun j => f (e.symm j).val, fun j => ⟨(e.symm j).val, (e.symm j).property, rfl⟩, ?_⟩
  rw [← Finset.prod_coe_sort]
  exact Fintype.prod_equiv e _ _ (fun j => by simp)

theorem continuous_coeff_prod_fin (r k : ℕ) :
    Continuous (fun v : Fin r → ℂ => (∏ j : Fin r, (X - C (v j))).coeff k) := by
  rw [continuous_iff_continuousAt]
  intro v
  have ha : ∀ j : Fin r, AnalyticAt ℂ (fun w : Fin r → ℂ => w j) v :=
    fun j => (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).analyticAt _
  exact (analyticAt_coeff_prod_X_sub_C (E := Fin r → ℂ) (J := Fin r) Finset.univ (fun j w => w j)
    (fun j _ => ha j) k).continuousAt

theorem tendsto_coeff_prod_of_values_coalesce {A J : Type*}
    (l : Filter A) (I : A → Finset J) (h : A → J → ℂ) {r : ℕ}
    (hr : ∀ᶠ y in l, (I y).card = r) (b : ℂ)
    (hb : ∀ ε > 0, ∀ᶠ y in l, ∀ j ∈ I y, dist (h y j) b < ε) (k : ℕ) :
    Filter.Tendsto (fun y => (∏ j ∈ I y, (X - C (h y j))).coeff k) l
      (nhds (((X - C b) ^ r).coeff k)) := by
  classical
  let c : (Fin r → ℂ) → ℂ := fun v => (∏ j : Fin r, (X - C (v j))).coeff k
  have hc : ContinuousAt c (fun _ => b) := (continuous_coeff_prod_fin r k).continuousAt
  rw [Metric.continuousAt_iff] at hc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcδ⟩ := hc ε hε
  filter_upwards [hr, hb δ hδ] with y hyr hyb
  obtain ⟨v, hv, hprod⟩ := exists_vector_prod_X_sub_C (I y) (h y) hyr
  have hvδ : dist v (fun _ => b) < δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro j
    obtain ⟨x, hx, hj⟩ := hv j
    rw [hj]
    exact hyb x hx
  have ht := hcδ hvδ
  change dist ((∏ j : Fin r, (X - C (v j))).coeff k)
    ((∏ _j : Fin r, (X - C b)).coeff k) < ε at ht
  rw [← hprod] at ht
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using ht

def ScalarAnalyticAt {n : ℕ} {V : Set (Fin n → ℂ)} (h : V → ℂ) (q : V) : Prop :=
  ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F q.val ∧
    h =ᶠ[𝓝 q] (fun x => F x.val)

theorem ScalarAnalyticAt.continuousAt {n : ℕ} {V : Set (Fin n → ℂ)}
    {h : V → ℂ} {q : V} (hh : ScalarAnalyticAt h q) : ContinuousAt h q := by
  obtain ⟨F,hF,he⟩ := hh
  exact (hF.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq he

theorem ScalarAnalyticAt.congr {n : ℕ} {V : Set (Fin n → ℂ)}
    {h g : V → ℂ} {q : V} (hh : ScalarAnalyticAt h q) (he : g =ᶠ[𝓝 q] h) :
    ScalarAnalyticAt g q := by
  obtain ⟨F,hF,hFe⟩ := hh
  exact ⟨F,hF,he.trans hFe⟩

theorem scalarAnalyticAt_const {n : ℕ} {V : Set (Fin n → ℂ)} (b : ℂ) (q : V) :
    ScalarAnalyticAt (fun _ : V => b) q :=
  ⟨fun _ => b, analyticAt_const, Filter.EventuallyEq.rfl⟩

theorem ScalarAnalyticAt.comp {n d : ℕ} {V : Set (Fin n → ℂ)}
    {h : V → ℂ} {s : (Fin d → ℂ) → V} {a : Fin d → ℂ}
    (hh : ScalarAnalyticAt h (s a))
    (hs : AnalyticAt ℂ (fun y => (s y).val) a) :
    AnalyticAt ℂ (fun y => h (s y)) a := by
  obtain ⟨F,hF,he⟩ := hh
  have hsc : ContinuousAt s a := by
    exact (Topology.IsEmbedding.subtypeVal.isInducing.continuousAt_iff).mpr hs.continuousAt
  apply (hF.comp (f := fun y => (s y).val) hs).congr
  exact (he.comp_tendsto hsc.tendsto).symm

theorem scalarAnalyticAt_padded {n : ℕ} {V : Set (Fin n → ℂ)}
    {B Ω C : Set V} [DecidablePred (· ∈ Ω)]
    (hΩ : IsOpen Ω) (hC : IsClosed C) (hΩC : Ω = C ∩ B)
    {h : V → ℂ} (hh : ∀ q ∈ Ω, ScalarAnalyticAt h q) (b : ℂ) :
    ∀ q ∈ B, ScalarAnalyticAt (Ω.piecewise h (fun _ => b)) q := by
  intro q hq
  by_cases hqΩ : q ∈ Ω
  · apply (hh q hqΩ).congr
    filter_upwards [hΩ.mem_nhds hqΩ] with x hx
    exact piecewise_eq_of_mem _ _ _ hx
  · have hqC : q ∉ C := fun hc => hqΩ (hΩC ▸ ⟨hc,hq⟩)
    apply (scalarAnalyticAt_const b q).congr
    filter_upwards [hC.isOpen_compl.mem_nhds hqC] with x hx
    apply piecewise_eq_of_notMem
    exact fun hxΩ => hx ((hΩC ▸ hxΩ).1)

theorem fiberPolynomial_coeff_analyticAt_of_sheets {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → (Fin d → ℂ))
    (hfin : ∀ y, ((fun x : V => π x.val) ⁻¹' {y}).Finite)
    (h : V → ℂ) {a : Fin d → ℂ}
    (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
    {W : Set (Fin d → ℂ)} (hW : IsOpen W) (haW : a ∈ W)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) W)
    (hs : ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
      ∀ z : Fin n → ℂ, (z ∈ V ∧ π z = y) ↔ ∃ i, g i y = z)
    (hh : ∀ x : V, π x.val = a → ScalarAnalyticAt h x) (k : ℕ) :
    AnalyticAt ℂ (fun y => (fiberPolynomial (fun x : V => π x.val) hfin h y).coeff k) a := by
  classical
  have hgV : ∀ i y, y ∈ W → g i y ∈ V := fun i y hy =>
    (((hs y hy).2 (g i y)).mpr ⟨i,rfl⟩).1
  let s : I → (Fin d → ℂ) → V := fun i y =>
    if hy : y ∈ W then ⟨g i y, hgV i y hy⟩ else ⟨g i a, hgV i a haW⟩
  have hse : ∀ i y, y ∈ W → (s i y).val = g i y := fun i y hy => by
    simp only [s, dite_eq_left hy]
  have hsa : ∀ i, AnalyticAt ℂ (fun y => h (s i y)) a := by
    intro i
    apply ScalarAnalyticAt.comp
    · apply hh
      rw [hse i a haW]
      exact (((hs a haW).2 (g i a)).mpr ⟨i,rfl⟩).2
    · apply (hg i a haW).congr
      filter_upwards [hW.mem_nhds haW] with y hy
      exact (hse i y hy).symm
  have hprod : ∀ y ∈ W,
      fiberPolynomial (fun x : V => π x.val) hfin h y =
        ∏ i : I, (Polynomial.X - C (h (s i y))) := by
    intro y hy
    apply fiberPolynomial_eq_prod
    · intro i j hij
      apply (hs y hy).1
      simpa only [hse i y hy, hse j y hy] using congrArg Subtype.val hij
    · intro x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := ((hs y hy).2 x.val).mp ⟨x.property,hx⟩
        exact ⟨i, Subtype.ext ((hse i y hy).trans hi)⟩
      · rintro ⟨i,rfl⟩
        rw [hse i y hy]
        exact (((hs y hy).2 (g i y)).mpr ⟨i,rfl⟩).2
  apply (analyticAt_coeff_prod_X_sub_C (E := Fin d → ℂ) (J := I)
    Finset.univ (fun i y => h (s i y)) (fun i _ => hsa i) k).congr
  filter_upwards [hW.mem_nhds haW] with y hy
  exact congrArg (fun p : Polynomial ℂ => p.coeff k) (hprod y hy).symm

theorem proper_eventually_fiber_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (hπ : IsProperMap π) {a : Y} {O : Set X} (hO : IsOpen O)
    (ha : π ⁻¹' {a} ⊆ O) :
    ∀ᶠ y in 𝓝 a, ∀ x, π x = y → x ∈ O := by
  have hc : IsClosed (π '' Oᶜ) := hπ.isClosedMap _ hO.isClosed_compl
  have hn : a ∉ π '' Oᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (ha hxa)
  filter_upwards [hc.isOpen_compl.mem_nhds hn] with y hy x hx
  by_contra hxO
  exact hy ⟨x, hxO, hx⟩

end Release061

end OAI
