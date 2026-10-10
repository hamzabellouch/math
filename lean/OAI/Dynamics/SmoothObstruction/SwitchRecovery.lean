import OAI.Dynamics.SmoothObstruction.PairLaw
import OAI.Dynamics.SmoothObstruction.ProductCoordinates
import OAI.Dynamics.SmoothObstruction.GridCells

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Cellwise pair domination sums with the ORIGINAL weights 1/μ(Q). There
is no renormalization after restricting to G or to endpoint patterns. -/
theorem law_domination (μ : Measure X) (P : X → α)
    (G : Set (X × X)) (Φ : X × X → X × X) (hΦ : Measurable Φ)
    (C : ℝ≥0∞)
    (hc : ∀ a,(((cell μ P a).prod (cell μ P a)).restrict G).map Φ≤
      C • (cell μ P a).prod (cell μ P a)) :
    ((law μ P).restrict G).map Φ≤C • law μ P := by
  have he : ((law μ P).restrict G).map Φ=
      ∑ a,(μ (P ⁻¹' {a}))⁻¹ • (((cell μ P a).prod (cell μ P a)).restrict G).map Φ := by
    rw [law,←Measure.restrictₗ_apply,map_sum,
      ←Measure.mapₗ_apply_of_measurable hΦ,map_sum]
    simp only [Measure.restrictₗ_apply,Measure.restrict_smul,
      Measure.mapₗ_apply_of_measurable hΦ,Measure.map_smul _ hΦ.aemeasurable]
  rw [he,law,Finset.smul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [smul_smul,mul_comm] using
    smul_le_smul_left ((μ (P ⁻¹' {a}))⁻¹) (hc a)

/-- Joint domination yields exactly the first-output switch law 2μ, not
a law normalized by the retained mass. -/
theorem first_output_domination (μ : Measure X) [IsFiniteMeasure μ]
    (P : X → α) (hP : Measurable P) (G : Set (X × X))
    (Φ : X × X → X × X) (hΦ : Measurable Φ) (C : ℝ≥0∞)
    (hdom : ((law μ P).restrict G).map Φ≤C • law μ P) :
    ((law μ P).restrict G).map (fun z => (Φ z).1)≤C • μ := by
  have h := Measure.map_mono hdom measurable_fst
  rw [Measure.map_map measurable_fst hΦ,
    Measure.map_smul _ measurable_fst.aemeasurable,first_marginal μ P hP] at h
  exact h
end SmoothObstruction.PairLaw

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The original cell-weighted experiment is carried by pairs in the same
cell, including zero-mass cells without any special convention. -/
lemma same_cell_ae (μ : Measure X) [IsFiniteMeasure μ] (P : X → α)
    (hP : Measurable P) : ∀ᵐ z ∂law μ P,P z.1=P z.2 := by
  classical
  rw [law,ae_finsetSum_measure_iff]
  intro a _
  apply Measure.ae_smul_measure
  have hQ : MeasurableSet (P ⁻¹' {a}) := hP (measurableSet_singleton a)
  rw [cell,Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hQ.prod hQ)] with z hz
  exact (show P z.1=a from hz.1).trans (show P z.2=a from hz.2).symm

/-- Retention is measured in the original pair probability, rather than in
any conditional law on the good set. -/
theorem retained_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → α) (hP : Measurable P) (R : Set X) (hR : MeasurableSet R) :
    let G := (R ×ˢ R) ∩ {z : X×X | P z.1=P z.2}
    MeasurableSet G ∧ (law μ P) Gᶜ≤2*μ Rᶜ ∧
      1-2*μ.real Rᶜ≤(law μ P).real G := by
  intro G
  have hsame : MeasurableSet {z : X×X | P z.1=P z.2} :=
    measurableSet_eq_fun (hP.comp measurable_fst) (hP.comp measurable_snd)
  have hG : MeasurableSet G := (hR.prod hR).inter hsame
  have he : G=ᵐ[law μ P] R ×ˢ R := by
    filter_upwards [same_cell_ae μ P hP] with z hz
    apply propext
    change (z∈R ×ˢ R ∧ P z.1=P z.2) ↔ z∈R ×ˢ R
    simp only [hz,and_true]
  have hl : (law μ P) Gᶜ≤2*μ Rᶜ := by
    rw [measure_congr he.compl]
    exact bad_pair_bound μ P hP R hR
  let := law_probability μ P hP
  refine ⟨hG,hl,?_⟩
  have hreal : (law μ P).real Gᶜ≤2*μ.real Rᶜ := by
    have h := ENNReal.toReal_mono (show 2*μ Rᶜ≠∞ by finiteness) hl
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,Measure.real] using h
  rw [probReal_compl_eq_one_sub hG] at hreal
  linarith

/-- A measurable canonical pair map can be checked using any cellwise local
extension agreeing on the retained set. Different extensions off that set do
not affect the ORIGINAL unnormalized pushforward. -/
theorem glue_cell_domination (μ : Measure X) [IsFiniteMeasure μ]
    (P : X → α) (hP : Measurable P) (G : Set (X×X)) (hG : MeasurableSet G)
    (Φ : X×X → X×X) (hΦ : Measurable Φ) (C : ℝ≥0∞)
    (hc : ∀ a,∃ F : X×X → X×X,Measurable F ∧
      EqOn F Φ G ∧
      (((cell μ P a).prod (cell μ P a)).restrict G).map F≤
        C • (cell μ P a).prod (cell μ P a)) :
    ((law μ P).restrict G).map Φ≤C • law μ P ∧
      ((law μ P).restrict G).map (fun z => (Φ z).1)≤C • μ := by
  have hd : ((law μ P).restrict G).map Φ≤C • law μ P := by
    apply law_domination μ P G Φ hΦ C
    intro a
    obtain ⟨F,_,he,hF⟩ := hc a
    have he' : F=ᵐ[((cell μ P a).prod (cell μ P a)).restrict G] Φ :=
      (ae_restrict_of_forall_mem hG (fun _ hz => he hz))
    rwa [Measure.map_congr he'] at hF
  exact ⟨hd,first_output_domination μ P hP G Φ hΦ C hd⟩
end SmoothObstruction.PairLaw

namespace SmoothObstruction.OrbitSafety
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

/-- A finite two-sided safety exclusion is charged to the original invariant
measure at every time, without conditioning the retained law. -/
theorem bilateral_bad_bound (μ : Measure X) (f g : X → X)
    (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (W : Set X) (hW : MeasurableSet W) (n : ℕ) :
    let Z := (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' W) ∪
      (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' W)
    MeasurableSet Z ∧ μ Z≤(2*(n+1) : ℝ≥0∞)*μ W ∧
      ∀ x,x∉Z → ∀ t≤n,(f^[t]) x∉W ∧ (g^[t]) x∉W := by
  intro Z
  have hm : MeasurableSet Z :=
    (MeasurableSet.iUnion (fun t : Fin (n+1) => hW.preimage (hf.iterate t.val).measurable)).union
      (MeasurableSet.iUnion (fun t : Fin (n+1) => hW.preimage (hg.iterate t.val).measurable))
  have h1 : μ (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' W)≤(n+1 : ℝ≥0∞)*μ W := by
    calc
      _ ≤ ∑ t : Fin (n+1),μ ((f^[t.val]) ⁻¹' W) := measure_iUnion_fintype_le μ _
      _ = _ := by simp only [(hf.iterate _).measure_preimage hW.nullMeasurableSet,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have h2 : μ (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' W)≤(n+1 : ℝ≥0∞)*μ W := by
    calc
      _ ≤ ∑ t : Fin (n+1),μ ((g^[t.val]) ⁻¹' W) := measure_iUnion_fintype_le μ _
      _ = _ := by simp only [(hg.iterate _).measure_preimage hW.nullMeasurableSet,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  refine ⟨hm,?_,?_⟩
  · exact (measure_union_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  · intro x hx t ht
    constructor
    · intro h
      exact hx (Or.inl (mem_iUnion.mpr ⟨⟨t,Nat.lt_succ_of_le ht⟩,h⟩))
    · intro h
      exact hx (Or.inr (mem_iUnion.mpr ⟨⟨t,Nat.lt_succ_of_le ht⟩,h⟩))
end SmoothObstruction.OrbitSafety

namespace SmoothObstruction.RetainedGlobal
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

lemma real_union_le (μ : Measure X) [IsFiniteMeasure μ] (A B : Set X) :
    μ.real (A∪B)≤μ.real A+μ.real B := by
  have h := ENNReal.toReal_mono (show μ A+μ B≠∞ by finiteness) (measure_union_le A B)
  simpa only [Measure.real,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using h

/-- The actual one-point retained carrier. The fixed atlas core is checked
only at 0 and the two endpoints. Coarse margins, product margins, and all
boundary-tube checks are charged in the original stationary measure. -/
theorem exists_retained (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → X) (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (G V Wc Wp Wb : Set X) (hG : MeasurableSet G) (hV : MeasurableSet V)
    (hWc : MeasurableSet Wc) (hWp : MeasurableSet Wp) (hWb : MeasurableSet Wb) (n : ℕ) :
    ∃ R : Set X,MeasurableSet R ∧ R⊆G ∧
      μ.real Rᶜ≤μ.real Gᶜ+3*(μ.real Vᶜ+μ.real Wc)+μ.real Wp+
        2*((n:ℝ)+1)*μ.real Wb ∧
      ∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
        f^[n] x∈V ∧ f^[n] x∉Wc ∧ g^[n] x∈V ∧ g^[n] x∉Wc ∧
        ∀ t≤n,f^[t] x∉Wb ∧ g^[t] x∉Wb := by
  let B := Vᶜ∪Wc
  have hB : MeasurableSet B := hV.compl.union hWc
  let Z := (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' Wb) ∪
    (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' Wb)
  obtain ⟨hZ,hZm,hZsafe⟩ := OrbitSafety.bilateral_bad_bound μ f g hf hg Wb hWb n
  let R := G∩(B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z)ᶜ
  have hR : MeasurableSet R := hG.inter
    (((((hB.union (hB.preimage (hf.iterate n).measurable)).union
      (hB.preimage (hg.iterate n).measurable)).union hWp).union hZ).compl)
  have hmB : μ.real B≤μ.real Vᶜ+μ.real Wc := real_union_le μ _ _
  have hmF : μ.real ((f^[n]) ⁻¹' B)=μ.real B := by
    exact congrArg ENNReal.toReal ((hf.iterate n).measure_preimage hB.nullMeasurableSet)
  have hmG : μ.real ((g^[n]) ⁻¹' B)=μ.real B := by
    exact congrArg ENNReal.toReal ((hg.iterate n).measure_preimage hB.nullMeasurableSet)
  have hmZ : μ.real Z≤2*((n:ℝ)+1)*μ.real Wb := by
    have hh := ENNReal.toReal_mono (show (2*((n:ℝ≥0∞)+1))*μ Wb≠∞ by finiteness) hZm
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_add (by finiteness : (n:ℝ≥0∞)≠∞) (by norm_num : (1:ℝ≥0∞)≠∞),
      ENNReal.toReal_natCast,ENNReal.toReal_one] using hh
  refine ⟨R,hR,inter_subset_left,?_,?_⟩
  · have he : Rᶜ=Gᶜ∪(B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z) := by
      simp only [R,compl_inter,compl_compl]
    rw [he]
    have h0 := real_union_le μ Gᶜ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z)
    have h1 := real_union_le μ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp) Z
    have h2 := real_union_le μ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B) Wp
    have h3 := real_union_le μ (B∪(f^[n]) ⁻¹' B) ((g^[n]) ⁻¹' B)
    have h4 := real_union_le μ B ((f^[n]) ⁻¹' B)
    rw [hmF] at h4
    rw [hmG] at h3
    linarith
  · intro x hx
    have hh : x∉B ∧ f^[n] x∉B ∧ g^[n] x∉B ∧ x∉Wp ∧ x∉Z := by
      have h := hx.2
      simp only [mem_compl_iff,mem_union,Set.mem_preimage,not_or] at h
      exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩
    have hb0 : x∈V ∧ x∉Wc := by simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.1
    have hbp : f^[n] x∈V ∧ f^[n] x∉Wc := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.2.1
    have hbm : g^[n] x∈V ∧ g^[n] x∉Wc := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.2.2.1
    exact ⟨hb0.1,hb0.2,hh.2.2.2.1,hbp.1,hbp.2,hbm.1,hbm.2,hZsafe x hh.2.2.2.2⟩

/-- Retained original cell-pair probability, with all exclusion losses and
without replacing cell weights by good-set weights. -/
theorem pair_mass {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α) (hP : Measurable P)
    (R : Set X) (hR : MeasurableSet R) {η : ℝ} (hm : μ.real Rᶜ≤η/2) :
    let G := (R ×ˢ R)∩{z : X×X | P z.1=P z.2}
    MeasurableSet G ∧ 1-η≤(PairLaw.law μ P).real G := by
  intro G
  obtain ⟨hG,_,hb⟩ := PairLaw.retained_bound μ P hP R hR
  exact ⟨hG,by linarith⟩
end SmoothObstruction.RetainedGlobal

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι C : Type*} [Fintype ι] [Fintype C]
    [MeasurableSpace C] [MeasurableSingletonClass C]
open ChartDensity

/-- The actual full finite product partition is constructed from one original
gauge reference per active starting bin. Wall strips are charged to the ORIGINAL
measure. No endpoint or orbit chart code is included in the cell alphabet. The
recovery assertion is precisely the ideal exchange needed by both joins. -/
theorem finite_product_partition [IsManifold I ∞ M] (μ : Measure M) [IsProbabilityMeasure μ]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (c : M → ι) (hc : ∀ x,x∈K (c x)) :
    ∃ D : ℝ,1≤D ∧ ∀ (P : M → C),Measurable P → ∀ (chart : C → ι),
      (∀ x,chart (P x)=c x) → ∀ (G : Set M) (n : ℕ) (B R : ℝ),0≤B →
      ∀ (A : ∀ x:G,BilateralGauge I S a c n B R x) (T : G → Finset (Fin d))
        (δ : ℝ),0<δ → ∀ N : ℕ,0<N →
      let H₀ := Real.sqrt 2*Real.exp (2*B)
      let m := ⌈H₀*D/(δ*N)+1⌉₊
      ∃ (L : M → C × (Fin d → Fin (2*m+1))) (W : Set M),
        Measurable L ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
        (∀ x,(L x).1=P x) ∧
        (∀ x y,L x=L y →
          ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖≤
            Real.sqrt 2*((d:ℝ)+1)*(δ*N)) ∧
        (∀ (x y z : M) (hx : x∈G),L x=L y → x∉W → y∉W → P z=P x →
          let ref : G := (reference P G (key P G ⟨x,hx⟩)).val
          H₀*‖coordinates I (a (c x)) z-(coordinates I (a (c x)) x+
            (((A ref).forward I S a c).splitting (T ref)ᶜ).slow 0
              (coordinates I (a (c x)) y-coordinates I (a (c x)) x))‖≤δ/4 →
          L z=L x) ∧
        Fintype.card (C × (Fin d → Fin (2*m+1)))=Fintype.card C*(2*m+1)^d := by
  obtain ⟨D,hD,hbound⟩ := selected_coordinate_bound I a K hK hKU c hc
  refine ⟨D,hD,?_⟩
  intro P hP chart hchart G n B R hB A T δ hδ N hN H₀ m
  let ref (Q : Active P G) : G := (reference P G Q).val
  obtain ⟨E,hE,hEi,hmix⟩ := product_coordinates P G hB
    (fun Q => (A (ref Q)).forward I S a c) (fun Q => (T (ref Q))ᶜ)
  let φ (Q : C) (x : M) := coordinates I (a (chart Q)) x
  have hb (x : M) : ‖φ (P x) x‖≤D := by simpa only [φ,hchart] using hbound x
  obtain ⟨L,W,hL,hW,hWm,hLP,hdiam,hstable,hcard⟩ := ProductCells.exists_cells μ P hP φ
    (fun Q => measurable_coordinates I (a (chart Q))) E (show 0≤D by linarith)
    (show 0≤H₀ by dsimp [H₀]; positivity) (Real.sqrt_nonneg _) hδ hb hEi hE hN
  refine ⟨L,W,hL,hW,hWm,hLP,?_,?_,hcard⟩
  · intro x y hxy
    simpa only [φ,hchart] using hdiam x y hxy
  · intro x y z hx hxy hxW hyW hz ref₀ herror
    apply hstable x y z hxy hxW hyW hz
    let Q : Active P G := key P G ⟨x,hx⟩
    let ideal := φ (P x) x+(((A (ref Q)).forward I S a c).splitting (T (ref Q))ᶜ).slow 0
      (φ (P x) y-φ (P x) x)
    have herr : H₀*‖φ (P x) z-ideal‖≤δ/4 := by
      simpa only [ideal,φ,hchart,ref,Q] using herror
    have he (i : Fin d) : |((E (P x)).symm (φ (P x) z)) i-((E (P x)).symm ideal) i|≤δ/4 := by
      calc
        _ = ‖(((E (P x)).symm (φ (P x) z-ideal)) i)‖ := by rw [map_sub]; rfl
        _ ≤ ‖(E (P x)).symm (φ (P x) z-ideal)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖(E (P x)).symm.toContinuousLinearMap‖*‖φ (P x) z-ideal‖ :=
          (E (P x)).symm.toContinuousLinearMap.le_opNorm _
        _ ≤ H₀*‖φ (P x) z-ideal‖ := mul_le_mul_of_nonneg_right (hEi _) (norm_nonneg _)
        _ ≤ δ/4 := herr
    intro i
    have hh := hmix Q (φ (P x) x) (φ (P x) y) i
    change ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) x)) i ∨
      ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) y)) i at hh
    rcases hh with hh|hh
    · exact Or.inl (by simpa only [hh] using he i)
    · exact Or.inr (by simpa only [hh] using he i)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniform comparison of actual chart displacements on the retained interior
balls. This is a consequence of the identity diffeomorphism's genuine smooth
coordinate maps, not an assumed Riemannian/Lipschitz metric. -/
theorem uniform_chart_transfer (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ (i j : ι) (x y : M) (δ : ℝ),
      x∈K i → x∈K j → 0≤δ → δ≤r →
      closedBall ((extChartAt I (a i)) x) δ⊆interior (range I) →
      y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ →
      y∈(chartAt H (a j)).source ∧
      ‖(extChartAt I (a j)) y-(extChartAt I (a j)) x‖≤
        C*‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖ := by
  let Id : Diffeomorph I I M M ∞ := Diffeomorph.refl I M ∞
  obtain ⟨r,C,hr,hC,ht⟩ := actual_tube_data I hclosed Id a K hK hKU
  refine ⟨r,C,hr,hC,fun i j x y δ hxi hxj hδ hδr hsafe hyi hxy => ?_⟩
  have hd := ht i j x δ hxi hxj hδ hδr hsafe
  have hyb : (extChartAt I (a i)) y∈closedBall ((extChartAt I (a i)) x) δ :=
    mem_closedBall_iff_norm.mpr hxy
  have hyj := (hd.2.1 hyb).2
  have hiy : (extChartAt I (a i)).symm ((extChartAt I (a i)) y)=y :=
    (extChartAt I (a i)).left_inv (by simpa only [extChartAt_source] using hyi)
  have hix : (extChartAt I (a i)).symm ((extChartAt I (a i)) x)=x :=
    (extChartAt I (a i)).left_inv (by simpa only [extChartAt_source] using hKU i hxi)
  change Id ((extChartAt I (a i)).symm ((extChartAt I (a i)) y))∈(chartAt H (a j)).source at hyj
  rw [hiy] at hyj
  refine ⟨hyj,?_⟩
  have hbound := (convex_closedBall ((extChartAt I (a i)) x) δ).norm_image_sub_le_of_norm_fderiv_le
    (𝕜:=ℝ) (f:=localMap I Id (a i) (a j))
    (fun u hu => (hd.2.2 u hu).1.differentiableAt (by norm_num))
    (fun u hu => (hd.2.2 u hu).2.1) (mem_closedBall_self hδ) hyb
  simpa only [localMap,Function.comp_apply,hix,hiy,Id,Diffeomorph.coe_refl,id_eq] using hbound
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A common output in two small selected tubes puts their centers in each
other's original chart, with a uniform linear coordinate bound. The chart
selector can be discontinuous: only its finite compact carrying patches are
used. This is the comparison needed to invoke old-tube rigidity when two
canonical switches have the same output. -/
theorem uniform_common_output (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ (i j : ι) (x y z : M) (ρ : ℝ),
      x∈K i → y∈K j → 0≤ρ → ρ≤r →
      closedBall ((extChartAt I (a j)) y) ρ⊆interior (range I) →
      z∈(chartAt H (a i)).source → z∈(chartAt H (a j)).source →
      ‖(extChartAt I (a i)) z-(extChartAt I (a i)) x‖≤ρ →
      ‖(extChartAt I (a j)) z-(extChartAt I (a j)) y‖≤ρ →
      y∈(chartAt H (a i)).source ∧
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤C*ρ := by
  have hex (i : ι) : ∃ v : ℝ,0<v ∧ cthickening v (K i)⊆(chartAt H (a i)).source :=
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  choose v hv hvU using hex
  obtain ⟨v₀,hv₀,hv₀i⟩ := CarriedCharts.finite_positive_lower v hv
  let L (i : ι) := cthickening v₀ (K i)
  have hL (i : ι) : IsCompact (L i) := (hK i).cthickening
  have hLU (i : ι) : L i⊆(chartAt H (a i)).source :=
    (cthickening_mono (hv₀i i) (K i)).trans (hvU i)
  obtain ⟨r,C,hr,hC,ht⟩ := uniform_chart_transfer I hclosed a L hL hLU
  obtain ⟨s,hs,hm⟩ := CoordinateTubes.uniform_inverse_modulus I hclosed a K hK hKU
    (ε:=v₀/3) (by positivity)
  refine ⟨min r s,C+1,lt_min hr hs,by linarith,?_⟩
  intro i j x y z ρ hxi hyj hρ hρr hsafe hzi hzj hzx hzy
  have hρs : ρ ≤ s := hρr.trans (min_le_right _ _)
  have hzx' := hm i x hxi z hzi (hzx.trans hρs)
  have hzy' := hm j y hyj z hzj (hzy.trans hρs)
  have hyx : dist y x≤v₀ := by
    have hh := dist_triangle y z x
    rw [dist_comm y z] at hh
    linarith
  have hyi : y∈L i := mem_cthickening_of_dist_le _ _ _ _ hxi hyx
  have hyj' : y∈L j := self_subset_cthickening (K j) hyj
  have ht' := ht j i y z ρ hyj' hyi hρ (hρr.trans (min_le_left _ _)) hsafe hzj hzy
  refine ⟨hLU i hyi,?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub ((extChartAt I (a i)) y) ((extChartAt I (a i)) z)
    ((extChartAt I (a i)) x)
  rw [norm_sub_rev ((extChartAt I (a i)) y) ((extChartAt I (a i)) z)] at htri
  have hcz : C*‖(extChartAt I (a j)) z-(extChartAt I (a j)) y‖≤C*ρ :=
    mul_le_mul_of_nonneg_left hzy (by linarith)
  nlinarith [ht'.2]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.SwitchRecovery
open Set
variable {X α β E F : Type*}

/-- Exact recovered cell and endpoint labels force the same four endpoint
maps even when the two inputs were certified by different frame witnesses. -/
theorem global_injective_tubes
    (c : X → α) (b : X → β) (future past : X → X)
    (U : α → β → X → E) (V : α → β → X → F)
    (TF TB RF RB : X → X → Prop) (R : Set X) (G : Set (X × X))
    (Φ : X × X → X × X)
    (hcommonF : ∀ x∈R,∀ y∈R,∀ z,TF x z → TF y z → RF x y)
    (hcommonB : ∀ x∈R,∀ y∈R,∀ z,TB x z → TB y z → RB x y)
    (hgood : ∀ u∈G,u.1∈R ∧ u.2∈R)
    (hc : ∀ u∈G,c u.1=c u.2 ∧ c (Φ u).1=c u.1)
    (hb : ∀ u∈G,
      b (future (Φ u).1)=b (future u.1) ∧
      b (past (Φ u).2)=b (past u.1) ∧
      b (future (Φ u).2)=b (future u.2) ∧
      b (past (Φ u).1)=b (past u.2))
    (heq : ∀ u∈G,
      U (c u.1) (b (future u.1)) (Φ u).1=U (c u.1) (b (future u.1)) u.1 ∧
      V (c u.1) (b (past u.1)) (Φ u).2=V (c u.1) (b (past u.1)) u.1 ∧
      U (c u.2) (b (future u.2)) (Φ u).2=U (c u.2) (b (future u.2)) u.2 ∧
      V (c u.2) (b (past u.2)) (Φ u).1=V (c u.2) (b (past u.2)) u.2)
    (hshadow : ∀ u∈G,TF u.1 (Φ u).1 ∧ TB u.1 (Φ u).2 ∧
      TF u.2 (Φ u).2 ∧ TB u.2 (Φ u).1)
    (hrigid : ∀ x∈R,∀ y,
      U (c x) (b (future x)) y=U (c x) (b (future x)) x →
      V (c x) (b (past x)) y=V (c x) (b (past x)) x →
      RF x y → RB x y → y=x) :
    InjOn Φ G := by
  intro u hu v hv huv
  have hc₁ : c v.1=c u.1 := (hc v hv).2.symm.trans (by rw [←huv]; exact (hc u hu).2)
  have hc₂ : c v.2=c u.2 := (hc v hv).1.symm.trans (hc₁.trans (hc u hu).1)
  have hb₁ : b (future v.1)=b (future u.1) := (hb v hv).1.symm.trans (by rw [←huv]; exact (hb u hu).1)
  have hb₂ : b (past v.1)=b (past u.1) := (hb v hv).2.1.symm.trans (by rw [←huv]; exact (hb u hu).2.1)
  have hb₃ : b (future v.2)=b (future u.2) := (hb v hv).2.2.1.symm.trans (by rw [←huv]; exact (hb u hu).2.2.1)
  have hb₄ : b (past v.2)=b (past u.2) := (hb v hv).2.2.2.symm.trans (by rw [←huv]; exact (hb u hu).2.2.2)
  have he₁ := (heq v hv).1.symm
  have he₂ := (heq v hv).2.1.symm
  have he₃ := (heq v hv).2.2.1.symm
  have he₄ := (heq v hv).2.2.2.symm
  rw [hc₁,hb₁,←huv] at he₁
  rw [hc₁,hb₂,←huv] at he₂
  rw [hc₂,hb₃,←huv] at he₃
  rw [hc₂,hb₄,←huv] at he₄
  have hsu := hshadow u hu
  have hsv := hshadow v hv
  rw [←huv] at hsv
  have hxu := (hgood u hu).1
  have hyu := (hgood u hu).2
  have hxv := (hgood v hv).1
  have hyv := (hgood v hv).2
  exact Prod.ext
    (hrigid u.1 hxu v.1 (he₁.trans (heq u hu).1) (he₂.trans (heq u hu).2.1)
      (hcommonF u.1 hxu v.1 hxv (Φ u).1 hsu.1 hsv.1)
      (hcommonB u.1 hxu v.1 hxv (Φ u).2 hsu.2.1 hsv.2.1)).symm
    (hrigid u.2 hyu v.2 (he₃.trans (heq u hu).2.2.1) (he₄.trans (heq u hu).2.2.2)
      (hcommonF u.2 hyu v.2 hyv (Φ u).2 hsu.2.2.1 hsv.2.2.1)
      (hcommonB u.2 hyu v.2 hyv (Φ u).1 hsu.2.2.2 hsv.2.2.2)).symm
end SmoothObstruction.SwitchRecovery

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Common sharp outputs recover the original full orbit tube, despite all
intermediate selected charts being allowed to differ. -/
theorem original_common_tubes (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ (S : Diffeomorph I I M M ∞)
      (c : M → ι) (n : ℕ) (ρ δ : ℝ) (x y z : M),
      (∀ v,v∈K (c v)) → 0≤ρ → ρ≤r → C*ρ≤δ →
      (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ
        ⊆interior (range I)) →
      originalTube I S a c (n:=n) ρ x z → originalTube I S a c (n:=n) ρ y z →
      originalTube I S a c (n:=n) δ x y := by
  obtain ⟨r,C,hr,hC,hh⟩ := uniform_common_output I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro S c n ρ δ x y z hc hρ hρr hδ hsafe hx hy t
  obtain ⟨hs,hb⟩ := hh (c (S^[t.val] x)) (c (S^[t.val] y))
    (S^[t.val] x) (S^[t.val] y) (S^[t.val] z) ρ (hc _) (hc _)
    hρ hρr (hsafe t) (hx t).1 (hy t).1 (hx t).2 (hy t).2
  exact ⟨hs,hb.trans hδ⟩

omit [ProperSpace M] [IsManifold I ∞ M] [Fintype ι] in
/-- Original cell and endpoint recovery makes the measurable canonical
switch globally one-to-one. The four endpoint equations are the original
ones, and rigidity is invoked in OLD charts, not independently chosen ones. -/
theorem original_switch_injective {C J : Type*}
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
    (hπ : ∀ x,π (L x)=P x) (hchart : ∀ x,chart (P x)=c x)
    (n : ℕ) (δ ρ : ℝ) (R : Set M) (G : Set (M×M)) (Φ : M×M → M×M)
    (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hcommonF : ∀ x∈R,∀ y∈R,∀ z,
      originalTube I S a c (n:=n) ρ x z → originalTube I S a c (n:=n) ρ y z →
      originalTube I S a c (n:=n) δ x y)
    (hcommonB : ∀ x∈R,∀ y∈R,∀ z,
      originalTube I S.symm a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
      originalTube I S.symm a c (n:=n) δ x y)
    (hgood : ∀ u∈G,u.1∈R ∧ u.2∈R)
    (hcell : ∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1)
    (hlabels : ∀ u∈G,
      P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
      P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
      P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
      P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2))
    (heq : ∀ u∈G,
      originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
      originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1)
    (hshadow : ∀ u∈G,
      originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
      originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
      originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
      originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1)
    (hrigid : ∀ x∈R,∀ z,
      originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
      originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
      originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) :
    InjOn Φ G := by
  let U : J → C → M → EuclideanSpace ℝ (Fin d) := fun Q b z =>
    (Wf (π Q,b)).starProjection ((extChartAt I (a (chart b))) (S^[n] z))
  let V : J → C → M → EuclideanSpace ℝ (Fin d) := fun Q b z =>
    (Wb (π Q,b)).starProjection ((extChartAt I (a (chart b))) (S.symm^[n] z))
  have hf (x z : M) : U (L x) (P (S^[n] x)) z=U (L x) (P (S^[n] x)) x ↔
      originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z := by
    simp only [U,hπ,hchart,originalEndpoint]
  have hb (x z : M) : V (L x) (P (S.symm^[n] x)) z=V (L x) (P (S.symm^[n] x)) x ↔
      originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z := by
    simp only [V,hπ,hchart,originalEndpoint]
  refine SwitchRecovery.global_injective_tubes L P (S^[n]) (S.symm^[n]) U V
    (originalTube I S a c (n:=n) ρ) (originalTube I S.symm a c (n:=n) ρ)
    (originalTube I S a c (n:=n) δ) (originalTube I S.symm a c (n:=n) δ)
    R G Φ hcommonF hcommonB hgood hcell hlabels ?_ hshadow ?_
  · intro u hu
    obtain ⟨h1,h2,h3,h4⟩ := heq u hu
    exact ⟨(hf _ _).mpr h1,(hb _ _).mpr h2,(hf _ _).mpr h3,(hb _ _).mpr h4⟩
  · intro x hx z h1 h2 h3 h4
    exact hrigid x hx z h3 h4 ((hf _ _).mp h1) ((hb _ _).mp h2)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.AtlasCores
open Set Filter Topology Metric
variable {X E ι C : Type*} [MetricSpace X] [NormedAddCommGroup E]

/-- No new label is introduced: positive old grid margin plus a stable
selected chart makes the original coarse label locally constant. -/
theorem coarse_label_germ (c : X → ι) (P : X → C) (φ : ι → X → E)
    (U : ι → Set X) (hU : ∀ i,IsOpen (U i))
    (hφ : ∀ i,ContinuousOn (φ i) (U i))
    (x : X) (hxU : x∈U (c x)) (s δ : ℝ) (hs : 0<s) (hδ : 0<δ)
    (hc : ∀ y,dist y x ≤ s → c y=c x)
    (hrec : ∀ y,c y=c x → ‖φ (c x) y-φ (c x) x‖≤δ → P y=P x) :
    ∀ᶠ y in 𝓝 x,P y=P x := by
  have hcont : ContinuousAt (fun y => ‖φ (c x) y-φ (c x) x‖) x :=
    (((hφ _).continuousAt ((hU _).mem_nhds hxU)).sub continuousAt_const).norm
  have hz : ‖φ (c x) x-φ (c x) x‖<δ := by simpa using hδ
  filter_upwards [Metric.ball_mem_nhds x hs,hcont.eventually (gt_mem_nhds hz)] with y hy hy'
  exact hrec y (hc y (Metric.mem_ball.mp hy).le) hy'.le

/-- Starting and final old labels can all be fixed on one neighborhood;
this finite local intersection is not charged to a partition alphabet. -/
theorem finite_label_germ {T : Type*} [Finite T]
    (P : X → C) (f : T → X → X) (x : X)
    (hf : ∀ t,ContinuousAt (f t) x)
    (hP : ∀ t,∀ᶠ y in 𝓝 (f t x),P y=P (f t x)) :
    ∀ᶠ y in 𝓝 x,∀ t,P (f t y)=P (f t x) := by
  exact Filter.eventually_all.mpr (fun t => (hf t).eventually (hP t))
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι : Type*} [Fintype ι]

/-- Uniform old-chart tubes give metric shadowing, with constants chosen
before the time length, orbit, chart selector, or frame witness. -/
theorem uniform_original_shadow (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {ε : ℝ} (hε : 0<ε) :
    ∃ σ : ℝ,0<σ ∧ ∀ (S : Diffeomorph I I M M ∞) (c : M → ι)
      (n : ℕ) (ρ : ℝ) (x z : M), (∀ u,u∈K (c u)) → ρ≤σ →
      originalTube I S a c (n:=n) ρ x z →
      ∀ t : Fin (n+1),dist (S^[t.val] z) (S^[t.val] x)<ε := by
  obtain ⟨σ,hσ,hm⟩ := CoordinateTubes.uniform_inverse_modulus I hclosed a K hK hKU hε
  refine ⟨σ,hσ,?_⟩
  intro S c n ρ x z hc hρ ht t
  exact hm _ _ (hc _) _ (ht t).1 ((ht t).2.trans hρ)

/-- Recovery of the ORIGINAL coarse label, without recording an orbit-chart
itinerary in the partition. The only exclusions are the fixed chart core and
old coarse-grid wall strip at the particular time under consideration. -/
theorem original_tube_labels
    (hclosed : IsClosed (range I)) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {s : ℝ} (hs : 0<s) :
    ∃ σ : ℝ,0<σ ∧ ∀ {C : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
      (P : M → C) (V W : Set M) (δ ρ : ℝ) (n : ℕ),
      (∀ u,u∈K (c u)) →
      (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
      (∀ x z,x∉W → c z=c x →
        ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δ/4 →
        P z=P x) → ρ≤σ → ρ≤δ/4 →
      ∀ x z,originalTube I S a c (n:=n) ρ x z →
      ∀ t : Fin (n+1),S^[t.val] x∈V → S^[t.val] x∉W → P (S^[t.val] z)=P (S^[t.val] x) := by
  obtain ⟨σ,hσ,hm⟩ := uniform_original_shadow I hclosed a K hK hKU hs
  refine ⟨σ,hσ,?_⟩
  intro C S c P V W δ ρ n hc hcore hrec hρσ hρδ x z ht t hv hw
  apply hrec _ _ hw (hcore _ hv _ ((hm S c n ρ x z hc hρσ ht t).le))
  rw [ChartDensity.coordinates_eq I _ _ (by simpa only [extChartAt_source] using (ht t).1),
    ChartDensity.coordinates_eq I _ _ (by simpa only [extChartAt_source] using hKU _ (hc _))]
  exact (ht t).2.trans hρδ

/-- The qualitative uniform shadowing assertion follows from the actual
sharp tube radii tending to zero. This does not assume a rate for an arbitrary
compatible metric on the compact manifold. -/
theorem original_shadow_tendsto (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (S : Diffeomorph I I M M ∞) (c : M → ι) (hc : ∀ u,u∈K (c u))
    (n : ℕ → ℕ) (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (G : ℕ → Set (M×M)) (Φ : ℕ → M×M → M×M)
    (ht : ∀ᶠ k in atTop,∀ u∈G k,
      originalTube I S a c (n:=n k) (ρ k) u.1 (Φ k u).1 ∧
      originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ k u).1) :
    ∀ ε : ℝ,0<ε → ∀ᶠ k in atTop,∀ u∈G k,∀ t v : Fin (n k+1),
      dist (S^[t.val] (Φ k u).1) (S^[t.val] u.1)+
      dist (S.symm^[v.val] (Φ k u).1) (S.symm^[v.val] u.2)<ε := by
  intro ε hε
  obtain ⟨σ,hσ,hm⟩ := uniform_original_shadow I hclosed a K hK hKU (half_pos hε)
  filter_upwards [ht,hρ.eventually (gt_mem_nhds hσ)] with k hk hkρ u hu t v
  have h₁ := hm S c (n k) (ρ k) u.1 (Φ k u).1 hc hkρ.le (hk u hu).1 t
  have h₂ := hm S.symm c (n k) (ρ k) u.2 (Φ k u).1 hc hkρ.le (hk u hu).2 v
  linarith

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Actual sharp tubes and old coarse/product grid margins recover both
full ORIGINAL cells and all four endpoint labels. Common-output old tubes
then prove global injectivity, even for unequal selected intermediate charts.
No partition is refined by an endpoint, frame witness, or orbit itinerary. -/
theorem recovered_original_pair (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {s : ℝ} (hs : 0<s) :
    ∃ σ r₁ C₁ : ℝ,0<σ ∧ 0<r₁ ∧ 1≤C₁ ∧
      ∀ {C J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
        (_ : ∀ x,π (L x)=P x) (_ : ∀ x,chart (P x)=c x)
        (n : ℕ) (δ ρ δc δp H₀ E : ℝ) (R V Wc Wp : Set M)
        (U : M → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (Φ : M×M → M×M) (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        (∀ x,x∈K (c x)) → 0≤ρ → ρ≤σ → ρ≤δc/4 → ρ≤r₁ → C₁*ρ≤δ →
        0≤H₀ → H₀*E≤δp/4 →
        (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
        (∀ x z,x∉Wc → c z=c x →
          ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
        (∀ x y z,x∈R → L x=L y → x∉Wp → y∉Wp → P z=P x →
          H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
            U x (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
        (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
          S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ u : M×M,u.1∈R → u.2∈R → L u.1=L u.2 →
          originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
          originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 ∧
          originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
          originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
          ‖(extChartAt I (a (c u.1))) (Φ u).1-(extChartAt I (a (c u.1))) u.1-
            U u.1 ((extChartAt I (a (c u.2))) u.2-(extChartAt I (a (c u.1))) u.1)‖≤E ∧
          ‖(extChartAt I (a (c u.2))) (Φ u).2-(extChartAt I (a (c u.2))) u.2-
            U u.2 ((extChartAt I (a (c u.1))) u.1-(extChartAt I (a (c u.2))) u.2)‖≤E) →
        (∀ u : M×M,u.1∈R → u.2∈R → L u.1=L u.2 →
          originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1) →
        (∀ x∈R,∀ z,
          originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) →
        let G := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
        (∀ u∈G,L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) ∧
        (∀ u∈G,P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
          P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
          P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
          P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2)) ∧ InjOn Φ G := by
  obtain ⟨σ,hσ,hl⟩ := original_tube_labels I hclosed a K hK hKU hs
  obtain ⟨r₁,C₁,hr₁,hC₁,hcommon⟩ := original_common_tubes I hclosed a K hK hKU
  refine ⟨σ,r₁,C₁,hσ,hr₁,hC₁,?_⟩
  intro C J S c P L π chart hπ hchart n δ ρ δc δp H₀ E R V Wc Wp U Φ Wf Wb
    hc hρ hρσ hρc hρr hρδ hH₀ hE hcore hcoarse hprod hret hsafe ht heq hrigid G
  have hρδ' : ρ≤δ := (le_mul_of_one_le_left hρ hC₁).trans hρδ
  have hPs {x y : M} (hh : L x=L y) : P x=P y := by rw [←hπ x,←hπ y,hh]
  have hcs {x y : M} (hh : L x=L y) : c x=c y := by rw [←hchart x,←hchart y,hPs hh]
  have hlabel (F : Diffeomorph I I M M ∞) (x z : M)
      (hh : originalTube I F a c (n:=n) ρ x z) (t : Fin (n+1))
      (hv : F^[t.val] x∈V) (hw : F^[t.val] x∉Wc) : P (F^[t.val] z)=P (F^[t.val] x) :=
    hl F c P V Wc δc ρ n hc hcore hcoarse hρσ hρc x z hh t hv hw
  have hret0 (x : M) (hx : x∈R) := hret x hx
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by
    simpa only [extChartAt_source] using hKU _ (hc x)
  have hcell (u : M×M) (hu : u∈G) : L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2 := by
    obtain ⟨htf,htb,hsf,hsb,hiz,hiw⟩ := ht u hu.1 hu.2.1 hu.2.2
    have hzP : P (Φ u).1=P u.1 := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply] using hlabel S u.1 (Φ u).1 htf 0
        (by simpa using (hret0 u.1 hu.1).1) (by simpa using (hret0 u.1 hu.1).2.1)
    have hwP : P (Φ u).2=P u.2 := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply] using hlabel S u.2 (Φ u).2 hsf 0
        (by simpa using (hret0 u.2 hu.2.1).1) (by simpa using (hret0 u.2 hu.2.1).2.1)
    have htz : (Φ u).1∈(extChartAt I (a (c u.1))).source := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (htf 0).1
    have htw : (Φ u).2∈(extChartAt I (a (c u.2))).source := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (hsf 0).1
    have hcross1 : u.2∈(extChartAt I (a (c u.1))).source := by rw [hcs hu.2.2]; exact hsrc u.2
    have hcross2 : u.1∈(extChartAt I (a (c u.2))).source := by rw [←hcs hu.2.2]; exact hsrc u.1
    constructor
    · apply hprod u.1 u.2 (Φ u).1 hu.1 hu.2.2 (hret0 u.1 hu.1).2.2.1 (hret0 u.2 hu.2.1).2.2.1 hzP
      rw [ChartDensity.coordinates_eq I _ _ htz,ChartDensity.coordinates_eq I _ _ (hsrc u.1),
        ChartDensity.coordinates_eq I _ _ hcross1]
      have hh := mul_le_mul_of_nonneg_left hiz hH₀
      rw [←hcs hu.2.2] at hh
      simpa only [sub_add_eq_sub_sub] using hh.trans hE
    · apply hprod u.2 u.1 (Φ u).2 hu.2.1 hu.2.2.symm (hret0 u.2 hu.2.1).2.2.1 (hret0 u.1 hu.1).2.2.1 hwP
      rw [ChartDensity.coordinates_eq I _ _ htw,ChartDensity.coordinates_eq I _ _ (hsrc u.2),
        ChartDensity.coordinates_eq I _ _ hcross2]
      have hh := mul_le_mul_of_nonneg_left hiw hH₀
      rw [hcs hu.2.2] at hh
      simpa only [sub_add_eq_sub_sub] using hh.trans hE
  have hlabels (u : M×M) (hu : u∈G) :
      P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
      P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
      P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
      P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2) := by
    obtain ⟨htf,htb,hsf,hsb,_,_⟩ := ht u hu.1 hu.2.1 hu.2.2
    have hfx := hlabel S u.1 (Φ u).1 htf (Fin.last n) (hret0 u.1 hu.1).2.2.2.1 (hret0 u.1 hu.1).2.2.2.2.1
    have hbx := hlabel S.symm u.1 (Φ u).2 hsb (Fin.last n) (hret0 u.1 hu.1).2.2.2.2.2.1 (hret0 u.1 hu.1).2.2.2.2.2.2
    have hfy := hlabel S u.2 (Φ u).2 hsf (Fin.last n) (hret0 u.2 hu.2.1).2.2.2.1 (hret0 u.2 hu.2.1).2.2.2.2.1
    have hby := hlabel S.symm u.2 (Φ u).1 htb (Fin.last n) (hret0 u.2 hu.2.1).2.2.2.2.2.1 (hret0 u.2 hu.2.1).2.2.2.2.2.2
    exact ⟨hfx,hbx,hfy,hby⟩
  refine ⟨hcell,hlabels,?_⟩
  apply original_switch_injective I S a c P L π chart hπ hchart n δ ρ R G Φ Wf Wb
  · intro x hx y hy z hxt hyt
    exact hcommon S c n ρ δ x y z hc hρ hρr hρδ
      (fun t => (closedBall_subset_closedBall hρδ').trans (hsafe y hy t).1) hxt hyt
  · intro x hx y hy z hxt hyt
    exact hcommon S.symm c n ρ δ x y z hc hρ hρr hρδ
      (fun t => (closedBall_subset_closedBall hρδ').trans (hsafe y hy t).2) hxt hyt
  · exact fun u hu => ⟨hu.1,hu.2.1⟩
  · exact fun u hu => ⟨hu.2.2,(hcell u hu).1⟩
  · exact hlabels
  · exact fun u hu => heq u hu.1 hu.2.1 hu.2.2
  · intro u hu
    obtain ⟨h1,h2,h3,h4,_,_⟩ := ht u hu.1 hu.2.1 hu.2.2
    exact ⟨h1,h4,h3,h2⟩
  · exact hrigid
end SmoothObstruction.ManifoldCoordinates

end

end OAI
