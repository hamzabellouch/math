import Mathlib
import OAI.Analysis.SymmetricDomains.FiberCardAmbientSheets

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem scalar_equicontinuousAt_of_finite_analytic_map {n d : ℕ} {ι : Type*}
    (V : Set (Fin n → ℂ)) (π₀ : (Fin n → ℂ) → (Fin d → ℂ))
    (hπ : IsProperMap (fun x : V => π₀ x.val))
    (hπo : IsOpenMap (fun x : V => π₀ x.val))
    (hfin : ∀ y, ((fun x : V => π₀ x.val) ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ)
    (hsheets : ∀ a, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (A : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen A ∧ a ∈ A ∧ (∀ i, AnalyticOnNhd ℂ (g i) A) ∧
        ∀ y ∈ A, Function.Injective (fun i => g i y) ∧
          ∀ z, (z ∈ V ∧ π₀ z = y) ↔ ∃ i, g i y = z)
    {W : Set V} (hW : IsOpen W) (h : ι → V → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1) {q : V} (hq : q ∈ W) :
    EquicontinuousAt h q := by
  classical
  let π : V → (Fin d → ℂ) := fun x => π₀ x.val
  obtain ⟨B,hB,hqB,Ω,C,hΩ,hqΩ,hΩW,hC,hΩC,hfiber⟩ :=
    finite_fiber_localization hπ q (hfin (π q)) hW hq
  let H : ι → V → ℂ := fun i => Ω.piecewise (h i) (fun _ => h i q)
  have hHhol : ∀ i x, π x ∈ B → ScalarAnalyticAt (H i) x := by
    intro i
    exact scalarAnalyticAt_padded hΩ hC hΩC (fun x hx => hh i x (hΩW hx)) (h i q)
  have hHc : ∀ i, ContinuousOn (H i) (π ⁻¹' B) :=
    fun i x hx => (hHhol i x hx).continuousAt.continuousWithinAt
  have hHb : ∀ i x, π x ∈ B → ‖H i x‖ ≤ 1 := by
    intro i x _
    by_cases hx : x ∈ Ω
    · simpa only [H, piecewise_eq_of_mem Ω (h i) _ hx] using hb i x (hΩW hx)
    · simpa only [H, piecewise_eq_of_notMem Ω (h i) _ hx] using hb i q hq
  have hHq : ∀ i x, π x = π q → H i x = h i q := by
    intro i x hx
    by_cases hxΩ : x ∈ Ω
    · have hxq : x = q := by
        have : x ∈ Ω ∩ π ⁻¹' {π q} := ⟨hxΩ,hx⟩
        rw [hfiber] at this
        exact this
      simp [H, hxq, hqΩ]
    · simp [H, hxΩ]
  have hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r := by
    intro y hy
    obtain ⟨I,g,A,hIr,hA,hyA,_,hs⟩ := hsheets y hy
    exact (fiber_card_of_ambient_sheets V π₀ hfin y I (fun i => g i y)
      (hs y hyA).1 (hs y hyA).2).trans hIr
  have hcoef : ∀ i k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin (H i) y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}) := by
    intro i k a ha
    obtain ⟨I,g,A,_,hA,haA,hg,hs⟩ := hsheets a ha.2
    apply fiberPolynomial_coeff_analyticAt_of_sheets V π₀ hfin (H i) I g hA haA hg hs
    intro x hx
    apply hHhol i x
    change π₀ x.val ∈ B
    rw [hx]
    exact ha.1
  choose c hcd hcb hce hcq using fun i => extended_fiber_coefficients V π hπ hfin D hD r
    hcard hB hqB (H i) (hHc i) (hHb i) (hcoef i) (h i q) (hHq i)
  have hroot : ∀ i x, π x ∈ B → (H i x)^r +
      ∑ j : Fin r, c i j (π x) * H i x ^ (j : ℕ) = 0 := by
    intro i
    exact finite_fiber_root_identity_extend π hπ.continuous hπo hfin
      (dense_polynomial_nonzero D hD) hB r hcard (H i) (hHc i) (c i)
      (fun j => (hcd i j).continuousOn) (hce i)
  obtain ⟨R,hR,hRB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hqB)
  apply equicontinuousAt_of_local_coalescing_polynomials (hΩ.mem_nhds hqΩ)
    hπ.continuous.continuousAt hR h c
  · intro i j
    exact (hcd i j).mono hRB
  · intro i j z hz
    exact hcb i j z (hRB hz)
  · intro i x hx
    exact hb i x (hΩW hx)
  · intro i x hx
    have hxB : π x ∈ B := (hΩC ▸ hx).2
    have hrx := hroot i x hxB
    have hHx : H i x = h i x := piecewise_eq_of_mem _ _ _ hx
    rw [hHx] at hrx
    have he := coalescing_coeff_identity (fun j => c i j (π x)) (h i x) (h i q) hrx
    simpa only [hcq] using he

theorem prime_zeroLocus_equicontinuousAt {n : ℕ} {ι : Type*}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ι → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) : EquicontinuousAt h q := by
  obtain ⟨d, _, g, hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ I (g (MvPolynomial.X j))
  obtain ⟨hπ,hfin⟩ := normalization_proper_finite I g hgi P hP
  have ho := normalization_isOpenMap I g hg hgi P hP
  obtain ⟨D,r,hD,_,hs⟩ := normalization_analytic_sheets I g hg hgi P hP
  exact scalar_equicontinuousAt_of_finite_analytic_map _ _ hπ ho hfin D hD r hs hW h hh hb hq

theorem zeroLocus_closed {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
      {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
    ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

theorem zeroLocus_eq_union_minimalPrimes {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial.zeroLocus ℂ I = ⋃ J : I.minimalPrimes, MvPolynomial.zeroLocus ℂ J.val := by
  ext x
  constructor
  · intro hx
    have hIx : I ≤ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin n → ℂ)) := by
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hx p hp)
    obtain ⟨J,hJ,hJx⟩ := Ideal.exists_minimalPrimes_le hIx
    refine mem_iUnion.mpr ⟨⟨J,hJ⟩, ?_⟩
    intro p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp (hJx hp)
  · intro hx
    rcases mem_iUnion.mp hx with ⟨J,hxJ⟩
    exact MvPolynomial.zeroLocus_anti_mono J.property.le hxJ

theorem equicontinuousAt_precomp {X Y Z ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [UniformSpace Z] {h : ι → X → Z} {f : Y → X} {p : Y}
    (hh : EquicontinuousAt h (f p)) (hf : ContinuousAt f p) :
    EquicontinuousAt (fun i y => h i (f y)) p := by
  intro U hU
  exact hf.eventually (hh U hU)

theorem equicontinuousWithinAt_of_notMem_closed {X Z ι : Type*}
    [TopologicalSpace X] [UniformSpace Z] (h : ι → X → Z)
    {S : Set X} (hS : IsClosed S) {p : X} (hp : p ∉ S) :
    EquicontinuousWithinAt h S p := by
  have he : 𝓝[S] p = ⊥ := by
    rw [← notMem_closure_iff_nhdsWithin_eq_bot]
    simpa only [hS.closure_eq] using hp
  intro U _
  simp [he]

theorem equicontinuousAt_of_finite_cover {X Z ι κ : Type*} [Finite κ]
    [TopologicalSpace X] [UniformSpace Z] (h : ι → X → Z)
    (S : κ → Set X) (hS : ⋃ j, S j = univ) {p : X}
    (hh : ∀ j, EquicontinuousWithinAt h (S j) p) : EquicontinuousAt h p := by
  intro U hU
  have he : 𝓝 p = ⨆ j, 𝓝[S j] p := by
    rw [← nhdsWithin_iUnion, hS, nhdsWithin_univ]
  rw [he, Filter.eventually_iSup]
  exact fun j => hh j U hU

theorem ScalarAnalyticAt.restrict {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hST : S ⊆ T) {h : T → ℂ} {q : S}
    (hh : ScalarAnalyticAt h ⟨q.val,hST q.property⟩) :
    ScalarAnalyticAt (fun x : S => h ⟨x.val,hST x.property⟩) q := by
  obtain ⟨F,hF,he⟩ := hh
  refine ⟨F,hF,?_⟩
  exact he.comp_tendsto (continuous_subtype_val.subtype_mk (fun x => hST x.property)).continuousAt

theorem zeroLocus_equicontinuousAt {n : ℕ} {ι : Type*}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ι → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) : EquicontinuousAt h q := by
  have : Finite I.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).to_subtype
  let T : I.minimalPrimes → Set (MvPolynomial.zeroLocus ℂ I) :=
    fun J => {x | x.val ∈ MvPolynomial.zeroLocus ℂ J.val}
  have hT : ⋃ J, T J = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := (zeroLocus_eq_union_minimalPrimes I).subset x.property
    rcases mem_iUnion.mp hx with ⟨J,hJ⟩
    exact mem_iUnion.mpr ⟨J,hJ⟩
  apply equicontinuousAt_of_finite_cover h T hT
  intro J
  by_cases hqJ : q ∈ T J
  · let : J.val.IsPrime := J.property.isPrime
    have hJI : MvPolynomial.zeroLocus ℂ J.val ⊆ MvPolynomial.zeroLocus ℂ I :=
      MvPolynomial.zeroLocus_anti_mono J.property.le
    let s : MvPolynomial.zeroLocus ℂ J.val → MvPolynomial.zeroLocus ℂ I :=
      fun x => ⟨x.val, hJI x.property⟩
    have hs : Continuous s := continuous_subtype_val.subtype_mk _
    have he := prime_zeroLocus_equicontinuousAt J.val (hW.preimage hs)
      (fun i x => h i (s x))
      (fun i x hx => (hh i (s x) hx).restrict hJI)
      (fun i x hx => hb i (s x) hx) (q := ⟨q.val,hqJ⟩) hq
    apply (equicontinuousAt_restrict_iff h ⟨q,hqJ⟩).mp
    let f : T J → MvPolynomial.zeroLocus ℂ J.val := fun x => ⟨x.val.val,x.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact equicontinuousAt_precomp (f := f) (p := ⟨q,hqJ⟩) he hf.continuousAt
  · exact equicontinuousWithinAt_of_notMem_closed h
      ((zeroLocus_closed J.val).preimage continuous_subtype_val) hqJ

theorem scalarAnalyticAt_of_open_extension {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hST : S ⊆ T) (hSo : IsOpen ((Subtype.val : T → Fin n → ℂ) ⁻¹' S))
    {h : S → ℂ} {H : T → ℂ} (hH : ∀ x : S, H (Set.inclusion hST x) = h x)
    {q : S} (hh : ScalarAnalyticAt h q) : ScalarAnalyticAt H (Set.inclusion hST q) := by
  obtain ⟨F,hF,he⟩ := hh
  refine ⟨F,hF,?_⟩
  rw [← (Topology.IsOpenEmbedding.inclusion hST hSo).map_nhds_eq q]
  change ∀ᶠ x : S in 𝓝 q, H (Set.inclusion hST x) = F x.val
  filter_upwards [he] with x hx
  rw [hH]
  exact hx

theorem scalar_equicontinuous_of_holomorphy {n : ℕ} {ι : Type*}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (h : ι → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) : Equicontinuous h := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  have hUI : U ⊆ MvPolynomial.zeroLocus ℂ I := by
    simpa only [I, hV.zeroLocus_vanishingIdeal] using hUV
  have hUo : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
    rw [show MvPolynomial.zeroLocus ℂ I = V from hV.zeroLocus_vanishingIdeal]
    exact hU
  let H : ι → MvPolynomial.zeroLocus ℂ I → ℂ :=
    fun i x => if hx : x.val ∈ U then h i ⟨x.val,hx⟩ else 0
  have hH : ∀ i (x : U), H i (Set.inclusion hUI x) = h i x := by
    intro i x
    simp only [H, Set.inclusion, x.property, dite_true]
  have hHg : ∀ i x, x.val ∈ U → ScalarAnalyticAt (H i) x := by
    intro i x hx
    exact scalarAnalyticAt_of_open_extension hUI hUo (hH i) (hh i ⟨x.val,hx⟩)
  have hHb : ∀ i x, x.val ∈ U → ‖H i x‖ ≤ 1 := by
    intro i x hx
    simpa only [← hH i ⟨x.val,hx⟩] using hb i ⟨x.val,hx⟩
  intro q
  have he := zeroLocus_equicontinuousAt I hUo H hHg hHb (q := Set.inclusion hUI q) q.property
  simpa only [hH] using equicontinuousAt_precomp (f := Set.inclusion hUI) (p := q)
    he (Topology.IsEmbedding.inclusion hUI).continuous.continuousAt

end Release061

end OAI
