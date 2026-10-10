import OAI.Dynamics.MultipleMixing.ExactLines

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]

structure BorelFibreEnumeration (S : Set (U × Z)) where
  domain : ℕ → Set U
  section_ : ℕ → U → Z
  measurable_domain : ∀ n, MeasurableSet (domain n)
  measurable_section : ∀ n, Measurable (section_ n)
  mem : ∀ n u, u ∈ domain n → (u,section_ n u) ∈ S
  cover : ∀ u z, (u,z) ∈ S → ∃ n, u ∈ domain n ∧ section_ n u = z
  unique : ∀ u n m, u ∈ domain n → u ∈ domain m → section_ n u = section_ m u → n = m

namespace BorelFibreEnumeration
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)
def indexDomain : Set (U × ℕ) := {x | x.1 ∈ E.domain x.2}
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma measurable_indexDomain : MeasurableSet E.indexDomain := by
  have he : E.indexDomain = ⋃ n, E.domain n ×ˢ {n} := by
    ext x; simp [indexDomain]
  rw [he]
  exact MeasurableSet.iUnion (fun n => (E.measurable_domain n).prod (measurableSet_singleton n))
instance : StandardBorelSpace E.indexDomain := E.measurable_indexDomain.standardBorel

def point (x : E.indexDomain) : U × Z := (x.val.1,E.section_ x.val.2 x.val.1)
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma measurable_point : Measurable E.point := by
  apply measurable_subtype_coe.fst.prodMk
  have h : Measurable (fun x : U × ℕ => E.section_ x.2 x.1) :=
    measurable_from_prod_countable_left (fun n => E.measurable_section n)
  exact h.comp measurable_subtype_coe
omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma injective_point : Function.Injective E.point := by
  intro x y h
  have hu : x.val.1 = y.val.1 := congrArg (fun p : U × Z => p.1) h
  have hn : x.val.2 = y.val.2 := E.unique x.val.1 x.val.2 y.val.2 x.property
    (by rw [hu]; exact y.property) (by
      have hh := congrArg (fun p : U × Z => p.2) h
      change E.section_ x.val.2 x.val.1 = E.section_ y.val.2 y.val.1 at hh
      rwa [←hu] at hh)
  exact Subtype.ext (Prod.ext hu hn)
lemma measurableEmbedding_point : MeasurableEmbedding E.point :=
  E.measurable_point.measurableEmbedding E.injective_point

def indexMeasure (ν : Measure U) : Measure E.indexDomain :=
  (ν.prod Measure.count).comap Subtype.val

instance indexMeasure_sigmaFinite (ν : Measure U) [SigmaFinite ν] : SigmaFinite (E.indexMeasure ν) := by
  apply SigmaFinite.of_map (E.indexMeasure ν) measurable_subtype_coe.aemeasurable
  change SigmaFinite (Measure.map Subtype.val ((ν.prod Measure.count).comap Subtype.val))
  rw [map_comap_subtype_coe E.measurable_indexDomain]
  infer_instance

def measure (ν : Measure U) : Measure (U × Z) := (E.indexMeasure ν).map E.point
instance measure_sigmaFinite (ν : Measure U) [SigmaFinite ν] : SigmaFinite (E.measure ν) :=
  E.measurableEmbedding_point.sigmaFinite_map

lemma ae_mem (ν : Measure U) : ∀ᵐ x ∂E.measure ν, x ∈ S := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff]
  exact Filter.Eventually.of_forall (fun x => E.mem _ _ x.property)

lemma lintegral_measure (ν : Measure U) [SigmaFinite ν]
    (F : U × Z → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂E.measure ν = ∫⁻ u, ∑' n, (E.domain n).indicator
      (fun u => F (u,E.section_ n u)) u ∂ν := by
  rw [measure,E.measurableEmbedding_point.lintegral_map]
  change (∫⁻ x : E.indexDomain, F (x.val.1,E.section_ x.val.2 x.val.1)
    ∂(ν.prod Measure.count).comap Subtype.val) = _
  rw [MeasureTheory.lintegral_subtype_comap E.measurable_indexDomain
    (fun x : U × ℕ => F (x.1,E.section_ x.2 x.1))]
  rw [←lintegral_indicator E.measurable_indexDomain]
  have hm : Measurable (fun x : U × ℕ => E.indexDomain.indicator
      (fun x => F (x.1,E.section_ x.2 x.1)) x) := by
    apply Measurable.indicator _ E.measurable_indexDomain
    exact hF.comp (measurable_fst.prodMk
      (measurable_from_prod_countable_left E.measurable_section))
  rw [lintegral_prod _ hm.aemeasurable]
  congr 1
  funext u
  rw [lintegral_count]
  rfl
end BorelFibreEnumeration
end

section
open MeasureTheory ProbabilityTheory Set
variable {U Y : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]
lemma separated_family_enumeration (S : Set (U × HilbertCode κ)) (hS : MeasurableSet S)
    (hb : ∀ u q, (u,q) ∈ S → q.base = u)
    (hsep : ∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) :
    Nonempty (BorelFibreEnumeration S) := by
  obtain ⟨D,s,hD,hs,_,hm,hc⟩ := separated_family_sections κ S hS hb hsep
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition S D s hD hs hm hc
  exact ⟨⟨E,s,hE,hs,he,hec,heu⟩⟩
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z V W : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace V] [StandardBorelSpace V]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def fibreEquiv (u : U) : {n : ℕ // u ∈ E.domain n} ≃ {z : Z // (u,z) ∈ S} := by
  let f : {n : ℕ // u ∈ E.domain n} → {z : Z // (u,z) ∈ S} :=
    fun n => ⟨E.section_ n u,E.mem n u n.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro n m he
    exact Subtype.ext (E.unique u n m n.property m.property (congrArg Subtype.val he))
  · intro z
    obtain ⟨n,hn,he⟩ := E.cover u z.val z.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩

omit [StandardBorelSpace U] [StandardBorelSpace Z] in
lemma sum_sections (u : U) (g : U × Z → ℝ≥0∞) :
    ∑' n, (E.domain n).indicator (fun u => g (u,E.section_ n u)) u =
      ∑' z : {z : Z // (u,z) ∈ S}, g (u,z.val) := by
  classical
  have he := (E.fibreEquiv u).tsum_eq (fun z => g (u,z.val))
  change (∑' n : {n : ℕ // u ∈ E.domain n}, g (u,E.section_ n u)) = _ at he
  have hs := tsum_subtype {n : ℕ | u ∈ E.domain n} (fun n => g (u,E.section_ n u))
  simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using hs.symm.trans he

lemma measurePreserving_fibrewise {R : Set (V × W)} (D : BorelFibreEnumeration R)
    (ν : Measure U) [SigmaFinite ν] (ρ : Measure V) [SigmaFinite ρ]
    (t : U → V) (ht : MeasurePreserving t ν ρ)
    (f : U × Z → W) (hf : Measurable f)
    (he : ∀ᵐ u ∂ν, ∃ e : {z : Z // (u,z) ∈ S} ≃ {w : W // (t u,w) ∈ R},
      ∀ z, (e z).val = f (u,z.val)) :
    MeasurePreserving (fun x : U × Z => (t x.1,f x)) (E.measure ν) (D.measure ρ) := by
  have hm : Measurable (fun x : U × Z => (t x.1,f x)) := (ht.measurable.comp measurable_fst).prodMk hf
  refine ⟨hm,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  have hleft := E.lintegral_measure ν (fun x => F (t x.1,f x)) (hF.comp hm)
  rw [hleft,D.lintegral_measure ρ F hF]
  have hsum : Measurable (fun v => ∑' n, (D.domain n).indicator
      (fun v => F (v,D.section_ n v)) v) := by
    apply Measurable.tsum
    intro n
    exact (hF.comp (measurable_id.prodMk (D.measurable_section n))).indicator (D.measurable_domain n)
  rw [←ht.lintegral_comp hsum]
  apply lintegral_congr_ae
  filter_upwards [he] with u hu
  obtain ⟨e,he⟩ := hu
  rw [E.sum_sections u (fun x => F (t x.1,f x)),D.sum_sections (t u) F]
  have hh := e.tsum_eq (fun w => F (t u,w.val))
  simpa only [he] using hh
end BorelFibreEnumeration

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

lemma exactCode_enumeration (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    Nonempty (BorelFibreEnumeration (exactCodeSet κ Λ u)) := by
  obtain ⟨D,s,hD,hs,_,hm,_,hc⟩ := exactCode_sections κ Λ u hu hk hm hind
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition (exactCodeSet κ Λ u)
    D s hD hs hm (fun p a ha => hc (p,a) ha)
  exact ⟨⟨E,s,hE,hs,he,hec,heu⟩⟩

def exactFibreSlotEquiv (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    (S : Set (U × HilbertCode κ)) (p : P) (i : I)
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} =
      {q | (u p i,q) ∈ S}) :
    {a : I → HilbertCode κ // (p,a) ∈ exactCodeSet κ Λ u} ≃
      {q : HilbertCode κ // (u p i,q) ∈ S} := by
  let f : {a : I → HilbertCode κ // (p,a) ∈ exactCodeSet κ Λ u} →
      {q : HilbertCode κ // (u p i,q) ∈ S} := fun a =>
    ⟨a.val i,by exact (Set.ext_iff.mp hS _).mp ⟨a.val,a.property,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b he
    exact Subtype.ext (exactCode_unique_slot κ Λ u hk hm hind a.property b.property i
      (congrArg Subtype.val he))
  · intro q
    obtain ⟨a,ha,he⟩ := (Set.ext_iff.mp hS _).mpr q.property
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩

lemma exactCounting_slot_preserving (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    (S : Set (U × HilbertCode κ)) (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet κ Λ u))
    (π : Measure P) [SigmaFinite π] (ν : Measure U) [SigmaFinite ν]
    (i : I) (hui : MeasurePreserving (fun p => u p i) π ν)
    (hS : ∀ᵐ p ∂π, {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} =
      {q | (u p i,q) ∈ S}) :
    MeasurePreserving (fun x : P × (I → HilbertCode κ) => (u x.1 i,x.2 i))
      (Eπ.measure π) (E.measure ν) := by
  apply Eπ.measurePreserving_fibrewise E π ν (fun p => u p i) hui
    (fun x => x.2 i) ((measurable_pi_apply i).comp measurable_snd)
  filter_upwards [hS] with p hp
  exact ⟨exactFibreSlotEquiv κ Λ u hk hm hind S p i hp,fun _ => rfl⟩
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Q U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace Q] [StandardBorelSpace Q]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (row col : Q → I → P)

def exactSquareSet : Set (Q × (I → I → HilbertCode κ)) :=
  {eq | (∀ a, (row eq.1 a,eq.2 a) ∈ exactCodeSet κ Λ u) ∧
    (∀ s, (col eq.1 s,fun a => eq.2 a s) ∈ exactCodeSet κ Λ u)}

omit [StandardBorelSpace P] [StandardBorelSpace Q] [DecidableEq I] in
lemma measurableSet_exactSquareSet (hu : Measurable u) (hr : Measurable row) (hc : Measurable col) :
    MeasurableSet (exactSquareSet κ Λ u row col) := by
  have hrow (a : I) : MeasurableSet {eq : Q × (I → I → HilbertCode κ) |
      (row eq.1 a,eq.2 a) ∈ exactCodeSet κ Λ u} :=
    (measurableSet_exactCodeSet κ Λ u hu).preimage
      ((((measurable_pi_apply a).comp hr).comp measurable_fst).prodMk
        ((measurable_pi_apply a).comp measurable_snd))
  have hcol (s : I) : MeasurableSet {eq : Q × (I → I → HilbertCode κ) |
      (col eq.1 s,fun a => eq.2 a s) ∈ exactCodeSet κ Λ u} := by
    apply (measurableSet_exactCodeSet κ Λ u hu).preimage
    apply (((measurable_pi_apply s).comp hc).comp measurable_fst).prodMk
    exact Measurable.of_eval (fun a => (measurable_pi_apply s).comp
      ((measurable_pi_apply a).comp measurable_snd))
  convert (MeasurableSet.iInter hrow).inter (MeasurableSet.iInter hcol) using 1
  ext eq
  simp [exactSquareSet]

omit [StandardBorelSpace P] [MeasurableSpace Q] [StandardBorelSpace Q] [StandardBorelSpace U] in
lemma exactSquare_unique_cell (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {e : Q} {q r : I → I → HilbertCode κ}
    (hq : (e,q) ∈ exactSquareSet κ Λ u row col)
    (hr : (e,r) ∈ exactSquareSet κ Λ u row col) (a s : I) (he : q a s = r a s) : q = r := by
  have hc : (fun i => q i s) = fun i => r i s :=
    exactCode_unique_slot κ Λ u hk hm hind (hq.2 s) (hr.2 s) a he
  funext i
  exact exactCode_unique_slot κ Λ u hk hm hind (hq.1 i) (hr.1 i) s (congrFun hc i)

omit [StandardBorelSpace P] [MeasurableSpace Q] [StandardBorelSpace Q] [StandardBorelSpace U] in
lemma exactSquare_separated (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {e : Q} {q r : I → I → HilbertCode κ}
    (hq : (e,q) ∈ exactSquareSet κ Λ u row col)
    (hr : (e,r) ∈ exactSquareSet κ Λ u row col) (a s : I) (hne : q ≠ r) :
    1 ≤ HilbertCode.distance (q a s) (r a s) := by
  rcases HilbertCode.exact_codes_dichotomy hk (Λ (row e a)) (q a) (r a)
    (fun j => ((hq.1 a).1 j).trans ((hr.1 a).1 j).symm) (hq.1 a).2.1 (hr.1 a).2.1
    (fun j => by simpa only [(hq.1 a).1 j] using hm (row e a) j)
    (hind (row e a)) (hq.1 a).2.2 (hr.1 a).2.2 with h | h
  · exact (hne (exactSquare_unique_cell κ Λ u row col hk hm hind hq hr a s (congrFun h s))).elim
  · exact h s

omit [StandardBorelSpace P] in
lemma exactSquare_enumeration (hu : Measurable u) (hrow : Measurable row) (hcol : Measurable col)
    (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    Nonempty (BorelFibreEnumeration (exactSquareSet κ Λ u row col)) := by
  let A := exactSquareSet κ Λ u row col
  let : StandardBorelSpace A := (measurableSet_exactSquareSet κ Λ u row col hu hrow hcol).standardBorel
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C,_,hcover,_,hemb⟩ := HilbertCode.separated_branches
    (fun t : A => t.1.1) measurable_subtype_coe.fst
    (fun t : A => t.1.2 i₀ i₀)
    ((measurable_pi_apply i₀).comp ((measurable_pi_apply i₀).comp measurable_subtype_coe.snd))
    (by
      intro x y he
      exact ((x.property.1 i₀).1 i₀).trans
        ((congrArg (fun e => u (row e i₀) i₀) he).trans ((y.property.1 i₀).1 i₀).symm))
    1 (by norm_num) (by
      intro x y he hne
      have hy : (x.1.1,y.1.2) ∈ A := by rw [he]; exact y.property
      exact exactSquare_separated κ Λ u row col hk hm hind x.property hy i₀ i₀
        (fun h => hne (Subtype.ext (Prod.ext he h))))
  let d : Q → I → I → HilbertCode κ := fun e a s => HilbertCode.encode (u (row e a) s) 0
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro s
    exact MeasurableSection.zero (((measurable_pi_apply s).comp hu).comp
      ((measurable_pi_apply a).comp hrow))
  obtain ⟨D,sec,hD,hs,_,hmem,hcov⟩ := measurable_branch_sections
    (fun t : A => t.1.1) (fun t => t.1.2) measurable_subtype_coe.snd d hd C hcover hemb
  have hm' (n) (e) (he : e ∈ D n) : (e,sec n e) ∈ A := by
    obtain ⟨t,ht,he⟩ := hmem n e he
    rw [he,←ht]
    exact t.property
  have hc' (e) (q) (hq : (e,q) ∈ A) : ∃ n, e ∈ D n ∧ sec n e = q := hcov ⟨(e,q),hq⟩
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition A D sec hD hs hm' hc'
  exact ⟨⟨E,sec,hE,hs,he,hec,heu⟩⟩
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

def rawExactSquare : Set (Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0))) :=
  exactSquareSet (M.ownKernel 0) Λ (tupleParameter M)
    (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e)

lemma rawSquare_row_completion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (a : I) (r : I → HilbertCode (M.ownKernel 0)),
      (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ q a = r := by
  have hr (a : I) := (show MeasurePreserving (plane 1 0 a)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  have hc (s : I) := (show MeasurePreserving (plane 1 (Fin.last 1) s)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  filter_upwards [ae_all_iff.mpr hr,ae_all_iff.mpr hc,
    rawSquare_exact_consistency M hM (by omega) Λ hL hm] with e hrow hcol hcons a r hr
  have hex (s : I) : ∃ b : I → HilbertCode (M.ownKernel 0),
      (plane 1 (Fin.last 1) s e,b) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) ∧ b a = r s := by
    have hs : (tupleParameter M (plane 1 0 a e) s,r s) ∈ S :=
      (Set.ext_iff.mp (hrow a s) _).mp ⟨r,hr,rfl⟩
    rw [parameter_cell_commute M a s e] at hs
    exact (Set.ext_iff.mp (hcol s a) _).mpr hs
  choose b hb hba using hex
  let q : I → I → HilbertCode (M.ownKernel 0) := fun i s => b s i
  have hqa : q a = r := funext hba
  have hqc (s : I) : (plane 1 (Fin.last 1) s e,fun i => q i s) ∈
      exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) := hb s
  refine ⟨q,⟨hcons q a hqc ?_,hqc⟩,hqa⟩
  rwa [hqa]

lemma rawSquare_column_completion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (s : I) (c : I → HilbertCode (M.ownKernel 0)),
      (plane 1 (Fin.last 1) s e,c) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧
        (fun i => q i s) = c := by
  obtain ⟨a⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hr := (show MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  have hc (s : I) := (show MeasurePreserving (plane 1 (Fin.last 1) s)
    (M.parameterLaw 2) (M.parameterLaw 1) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hS
  filter_upwards [hr,ae_all_iff.mpr hc,rawSquare_row_completion M Λ hM hk hL hm S hS]
    with e hrow hcol hcompl s c hc
  have hs : (tupleParameter M (plane 1 (Fin.last 1) s e) a,c a) ∈ S :=
    (Set.ext_iff.mp (hcol s a) _).mp ⟨c,hc,rfl⟩
  rw [←parameter_cell_commute M a s e] at hs
  obtain ⟨r,hr,hrs⟩ := (Set.ext_iff.mp (hrow s) _).mpr hs
  obtain ⟨q,hq,hqa⟩ := hcompl a r hr
  refine ⟨q,hq,?_⟩
  exact exactCode_unique_slot (M.ownKernel 0) Λ (tupleParameter M) hk hm hind
    (hq.2 s) hc a ((congrFun hqa s).trans hrs)

lemma rawSquare_row_bijective (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (e : Arr I M.U 2) (a : I)
    (hc : ∀ r, (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ q a = r) :
    ∃ f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} ≃
        {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)},
      ∀ q, (f q).val = q.val a := by
  let f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} →
      {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 0 a e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} :=
    fun q => ⟨q.val a,q.property.1 a⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r he
      apply Subtype.ext
      exact exactSquare_unique_cell (M.ownKernel 0) Λ (tupleParameter M)
        (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e) hk hm hind
        q.property r.property a a (congrFun (congrArg Subtype.val he) a)
    · intro r
      obtain ⟨q,hq,he⟩ := hc r.val r.property
      exact ⟨⟨q,hq⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

lemma rawSquare_col_bijective (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (e : Arr I M.U 2) (s : I)
    (hc : ∀ r, (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∃ q : I → I → HilbertCode (M.ownKernel 0), (e,q) ∈ rawExactSquare M Λ ∧ (fun i => q i s) = r) :
    ∃ f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} ≃
        {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)},
      ∀ q, (f q).val = fun i => q.val i s := by
  let f : {q : I → I → HilbertCode (M.ownKernel 0) // (e,q) ∈ rawExactSquare M Λ} →
      {r : I → HilbertCode (M.ownKernel 0) //
          (plane 1 (Fin.last 1) s e,r) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} :=
    fun q => ⟨fun i => q.val i s,q.property.2 s⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r he
      apply Subtype.ext
      exact exactSquare_unique_cell (M.ownKernel 0) Λ (tupleParameter M)
        (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e) hk hm hind
        q.property r.property s s (congrFun (congrArg Subtype.val he) s)
    · intro r
      obtain ⟨q,hq,he⟩ := hc r.val r.property
      exact ⟨⟨q,hq⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f hf,fun _ => rfl⟩

lemma rawCounting_rows_preserving (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a : I) :
    MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
      (plane 1 0 a x.1,x.2 a)) (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eσ.measurePreserving_fibrewise Eπ _ _ (plane 1 0 a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd)
  filter_upwards [rawSquare_row_completion M Λ hM hk hL hm S hS] with e he
  exact rawSquare_row_bijective M Λ hk hm hind e a (he a)

lemma rawCounting_columns_preserving (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s : I) :
    MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
      (plane 1 (Fin.last 1) s x.1,fun i => x.2 i s))
      (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eσ.measurePreserving_fibrewise Eπ _ _ (plane 1 (Fin.last 1) s)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x i => x.2 i s) (Measurable.of_eval fun i =>
      (measurable_pi_apply s).comp ((measurable_pi_apply i).comp measurable_snd))
  filter_upwards [rawSquare_column_completion M Λ hM hk hL hm hind S hS] with e he
  exact rawSquare_col_bijective M Λ hk hm hind e s (he s)

lemma rawCounting_coordinate_preserving (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (i : I) :
    MeasurePreserving (fun x : Arr I M.U 1 × (I → HilbertCode (M.ownKernel 0)) =>
      (tupleParameter M x.1 i,x.2 i)) (Eπ.measure (M.parameterLaw 1)) (E.measure (M.parameterLaw 0)) := by
  apply exactCounting_slot_preserving (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S E Eπ _ _ i
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  exact hS.mono (fun _ hp => hp i)

lemma exists_raw_counting_data (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) :
    ∃ (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
      (E : BorelFibreEnumeration S)
      (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
      (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)),
      MeasurableSet S ∧
      (∀ u q, (u,q) ∈ S → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
      (∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (tupleParameter M p i,q) ∈ S}) ∧
      (∀ i, MeasurePreserving (fun x : Arr I M.U 1 × (I → HilbertCode (M.ownKernel 0)) =>
        (tupleParameter M x.1 i,x.2 i)) (Eπ.measure (M.parameterLaw 1)) (E.measure (M.parameterLaw 0))) ∧
      (∀ a, MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
        (plane 1 0 a x.1,x.2 a)) (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1))) ∧
      (∀ s, MeasurePreserving (fun x : Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0)) =>
        (plane 1 (Fin.last 1) s x.1,fun i => x.2 i s))
        (Eσ.measure (M.parameterLaw 2)) (Eπ.measure (M.parameterLaw 1))) := by
  obtain ⟨S,hSm,hSb,hSs,hSe⟩ := exists_commonLocalLineGraph M hM hk Λ hL hm hind
  obtain ⟨E⟩ := separated_family_enumeration (M.ownKernel 0) S hSm (fun u q hq => (hSb u q hq).1) hSs
  obtain ⟨Eπ⟩ := exactCode_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (measurable_tupleParameter M) hk hm hind
  obtain ⟨Eσ⟩ := exactSquare_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (fun e i => plane 1 0 i e) (fun e j => plane 1 (Fin.last 1) j e)
    (measurable_tupleParameter M) (Measurable.of_eval fun i => measurable_plane _ _ _)
    (Measurable.of_eval fun j => measurable_plane _ _ _) hk hm hind
  exact ⟨S,E,Eπ,Eσ,hSm,hSb,hSe,
    rawCounting_coordinate_preserving M Λ hk hm hind S hSe E Eπ,
    rawCounting_rows_preserving M Λ hM hk hL hm hind S hSe Eπ Eσ,
    rawCounting_columns_preserving M Λ hM hk hL hm hind S hSe Eπ Eσ⟩
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Z : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def comapBase (t : P → U) (ht : Measurable t) :
    BorelFibreEnumeration {x : P × Z | (t x.1,x.2) ∈ S} where
  domain n := t ⁻¹' E.domain n
  section_ n := E.section_ n ∘ t
  measurable_domain n := ht (E.measurable_domain n)
  measurable_section n := (E.measurable_section n).comp ht
  mem n p hp := E.mem n (t p) hp
  cover p z hz := E.cover (t p) z hz
  unique p n m hn hm he := E.unique (t p) n m hn hm he

lemma ae_base (ν : Measure U) [SigmaFinite ν] {P : U → Prop} (h : ∀ᵐ u ∂ν, P u) :
    ∀ᵐ x ∂E.measure ν, P x.1 := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff]
  have h' : ∀ᵐ x ∂ν.prod Measure.count, P x.1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := (Measure.count : Measure ℕ))).ae h
  have hs : ∀ᵐ x ∂(ν.prod Measure.count).restrict E.indexDomain, P x.1 :=
    ae_restrict_of_ae h'
  rw [←map_comap_subtype_coe E.measurable_indexDomain] at hs
  exact (MeasurableEmbedding.subtype_coe E.measurable_indexDomain).ae_map_iff.mp hs

lemma comapBase_preserving (π : Measure P) [SigmaFinite π] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t π ν) :
    MeasurePreserving (fun x : P × Z => (t x.1,x.2)) ((E.comapBase t ht.measurable).measure π)
      (E.measure ν) := by
  apply (E.comapBase t ht.measurable).measurePreserving_fibrewise E π ν t ht
    Prod.snd measurable_snd
  exact Filter.Eventually.of_forall (fun _ => ⟨Equiv.refl _,fun _ => rfl⟩)

omit [StandardBorelSpace P] [MeasurableSpace U] [StandardBorelSpace U] in
lemma lintegral_indicator_kernel (η : Measure P) (D : Set U) (u : U)
    (g : P → ℝ≥0∞) :
    D.indicator (fun _ => ∫⁻ p, g p ∂η) u = ∫⁻ p, D.indicator (fun _ => g p) u ∂η := by
  classical
  by_cases hu : u ∈ D <;> simp [hu]

lemma parameter_conditional (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (η : Kernel U P) [IsMarkovKernel η] (hη : HasCondDistrib id t η μ) :
    HasCondDistrib Prod.fst (fun x : P × Z => (t x.1,x.2))
      (η.comap (Prod.fst : U × Z → U) (@measurable_fst U Z _ ‹MeasurableSpace Z›)) ((E.comapBase t ht.measurable).measure μ) := by
  have hobs := E.comapBase_preserving μ ν t ht
  refine ⟨(hobs.measurable.prodMk measurable_fst).aemeasurable,?_⟩
  rw [hobs.map_eq]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (hobs.measurable.prodMk measurable_fst)]
  have hleft := (E.comapBase t ht.measurable).lintegral_measure μ
    (fun x : P × Z => F ((t x.1,x.2),x.1)) (hF.comp (hobs.measurable.prodMk measurable_fst))
  rw [hleft]
  rw [Measure.lintegral_compProd hF]
  have hg : Measurable (fun x : U × Z => ∫⁻ p, F (x,p) ∂η x.1) :=
    Measurable.lintegral_kernel_prod_right (f := fun x p => F (x,p)) hF (κ := η.comap (Prod.fst : U × Z → U) measurable_fst)
  simp only [Kernel.comap_apply]
  rw [E.lintegral_measure ν _ hg]
  let H : U × P → ℝ≥0∞ := fun up => ∑' n, (E.domain n).indicator
    (fun u => F ((u,E.section_ n u),up.2)) up.1
  have hH : Measurable H := by
    apply Measurable.tsum
    intro n
    exact ((hF.comp ((measurable_fst.prodMk ((E.measurable_section n).comp measurable_fst)).prodMk
      measurable_snd)).indicator ((E.measurable_domain n).preimage measurable_fst))
  have hpair : MeasurePreserving (fun p => (t p,p)) μ (ν ⊗ₘ η) :=
    ⟨ht.measurable.prodMk measurable_id,by simpa only [ht.map_eq,id_eq] using hη.map_eq⟩
  have he := hpair.lintegral_comp hH
  rw [Measure.lintegral_compProd hH] at he
  change (∫⁻ p, H (t p,p) ∂μ) = _
  rw [he]
  apply lintegral_congr
  intro u
  dsimp only [H]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    symm
    exact lintegral_indicator_kernel (η u) (E.domain n) u (fun p => F ((u,E.section_ n u),p))
  · intro n
    by_cases hu : u ∈ E.domain n
    · have hf : Measurable (fun p : P => F ((u,E.section_ n u),p)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      convert hf.aemeasurable using 1
      ext p
      exact Set.indicator_of_mem hu _
    · simp only [Set.indicator_of_notMem hu]
      exact measurable_const.aemeasurable
end BorelFibreEnumeration

namespace ConditionalTransport
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} [SFinite μ] {x : Ω → A} {y : Ω → B}
  {κ : Kernel A B} [IsSFiniteKernel κ]

lemma with_observation (h : HasCondDistrib y x κ μ) :
    HasCondDistrib (fun ω => (x ω,y ω)) x (Kernel.id ×ₖ κ) μ := by
  refine ⟨h.aemeasurable_fst.prodMk h.aemeasurable,?_⟩
  have hm : Measurable (fun ab : A × B => (ab.1,ab)) := measurable_fst.prodMk measurable_id
  have hmap : μ.map (fun ω => (x ω,x ω,y ω)) =
      ((μ.map x) ⊗ₘ κ).map (fun ab : A × B => (ab.1,ab)) := by
    rw [←h.map_eq, AEMeasurable.map_map_of_aemeasurable
      hm.aemeasurable h.aemeasurable]
    rfl
  rw [hmap]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  have hf' : Measurable (fun ab : A × B => f (ab.1,ab)) := hf.comp hm
  rw [Measure.lintegral_compProd hf',
    Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro a
  have hfa : Measurable (fun ab : A × B => f (a,ab)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [Kernel.lintegral_id_prod hfa κ a]

lemma map_observation (h : HasCondDistrib y x κ μ) (f : A × B → C) (hf : Measurable f) :
    HasCondDistrib (fun ω => f (x ω,y ω)) x ((Kernel.id ×ₖ κ).map f) μ :=
  (with_observation h).comp_left hf
end ConditionalTransport

namespace BorelFibreEnumeration
open MeasureTheory ProbabilityTheory Set
variable {P U Z W : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (P × Z)} (E : BorelFibreEnumeration S)
  {R : Set (U × W)} (D : BorelFibreEnumeration R)

include D in
lemma parameter_conditional_of_fibrewise
    (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (f : P × Z → W) (hf : Measurable f)
    (he : ∀ᵐ p ∂μ, ∃ e : {z : Z // (p,z) ∈ S} ≃ {w : W // (t p,w) ∈ R},
      ∀ z, (e z).val = f (p,z.val))
    (η : Kernel U P) [IsMarkovKernel η] (hη : HasCondDistrib id t η μ) :
    HasCondDistrib Prod.fst (fun x : P × Z => (t x.1,f x))
      (η.comap (Prod.fst : U × W → U) (@measurable_fst U W _ ‹MeasurableSpace W›))
      (E.measure μ) := by
  have hobs : MeasurePreserving (fun x : P × Z => (x.1,f x)) (E.measure μ)
      ((D.comapBase t ht.measurable).measure μ) :=
    E.measurePreserving_fibrewise (D.comapBase t ht.measurable) μ μ id
      (MeasurePreserving.id μ) f hf he
  have hp := D.comapBase_preserving μ ν t ht
  have hc := D.parameter_conditional μ ν t ht η hη
  change HasLaw _ _ _ at hc ⊢
  rw [hp.map_eq] at hc
  have hout : MeasurePreserving (fun x : P × Z => (t x.1,f x)) (E.measure μ) (D.measure ν) :=
    hp.comp hobs
  rw [hout.map_eq]
  exact hc.comp hobs.hasLaw
end BorelFibreEnumeration

namespace Kernel
open MeasureTheory ProbabilityTheory
variable {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]

def depMap (κ : ProbabilityTheory.Kernel A B) (f : A × B → C) : ProbabilityTheory.Kernel A C :=
  (ProbabilityTheory.Kernel.id ×ₖ κ).map f

instance depMap_sfinite (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    (f : A × B → C) : IsSFiniteKernel (depMap κ f) := by
  unfold depMap
  infer_instance

lemma depMap_markov (κ : ProbabilityTheory.Kernel A B) [IsMarkovKernel κ] (f : A × B → C)
    (hf : Measurable f) : IsMarkovKernel (depMap κ f) := by
  unfold depMap
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hf

lemma depMap_apply (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    {f : A × B → C} (hf : Measurable f) (a : A) :
    depMap κ f a = (κ a).map (fun b => f (a,b)) := by
  rw [depMap,ProbabilityTheory.Kernel.map_apply _ hf,
    ProbabilityTheory.Kernel.prod_apply,ProbabilityTheory.Kernel.id_apply,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

lemma depMap_comap (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    {f : A × B → C} (hf : Measurable f) (g : D → A) (hg : Measurable g) :
    (depMap κ f).comap g hg = depMap (κ.comap g hg) (fun db => f (g db.1,db.2)) := by
  have hfg : Measurable (fun db : D × B => f (g db.1,db.2)) :=
    hf.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  ext d : 1
  rw [ProbabilityTheory.Kernel.comap_apply,depMap_apply κ hf,
    depMap_apply _ hfg,
    ProbabilityTheory.Kernel.comap_apply]

lemma depMap_prod (κ : ProbabilityTheory.Kernel A B) (η : ProbabilityTheory.Kernel A C)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {f : A × B → D} {g : A × C → E} (hf : Measurable f) (hg : Measurable g) :
    depMap (κ ×ₖ η) (fun x => (f (x.1,x.2.1),g (x.1,x.2.2))) =
      depMap κ f ×ₖ depMap η g := by
  have hfg : Measurable (fun x : A × (B × C) => (f (x.1,x.2.1),g (x.1,x.2.2))) :=
    (hf.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hg.comp (measurable_fst.prodMk measurable_snd.snd))
  ext a : 1
  rw [depMap_apply _ hfg,
    ProbabilityTheory.Kernel.prod_apply,ProbabilityTheory.Kernel.prod_apply,
    depMap_apply _ hf,depMap_apply _ hg]
  exact (Measure.map_prod_map (κ a) (η a) (hf.comp measurable_prodMk_left)
    (hg.comp measurable_prodMk_left)).symm
end Kernel

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

abbrev RawLabel := Arr I M.U 0 × HilbertCode (M.ownKernel 0)
abbrev RawLabelTuple := Arr I M.U 1 × (I → HilbertCode (M.ownKernel 0))

def rawLabelSlot (a : I) (x : RawLabelTuple M) : RawLabel M :=
  (tupleParameter M x.1 a,x.2 a)

omit [DecidableEq I] in
lemma measurable_rawLabelSlot (a : I) : Measurable (rawLabelSlot M a) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    ((measurable_pi_apply a).comp measurable_snd)

def rawMatchedLabel (a b : I) (x : RawLabel M × Arr I M.U 1) : RawLabel M :=
  (tupleParameter M x.2 b,exactMatching (M.ownKernel 0) Λ (tupleParameter M) a (x.2,x.1.2) b)

lemma measurable_rawMatchedLabel (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a b : I) :
    Measurable (rawMatchedLabel M Λ a b) := by
  exact ((measurable_plane _ _ _).comp measurable_snd).prodMk
    ((measurable_pi_apply b).comp ((measurable_exactMatching (M.ownKernel 0) Λ
      (tupleParameter M) (measurable_tupleParameter M) hk hm hind a).comp
      (measurable_snd.prodMk measurable_fst.snd)))

def rawLabelTransition (a b : I) : Kernel (RawLabel M) (RawLabel M) :=
  Rokhlin.Kernel.depMap ((M.parameterCoordinateKernel a).comap Prod.fst measurable_fst)
    (rawMatchedLabel M Λ a b)

lemma rawLabelTransition_markov (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a b : I) :
    IsMarkovKernel (rawLabelTransition M Λ a b) :=
  Rokhlin.Kernel.depMap_markov _ _ (measurable_rawMatchedLabel M Λ hk hm hind a b)

lemma rawCounting_parameter_given_label (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (a : I) :
    HasCondDistrib Prod.fst (rawLabelSlot M a)
      ((M.parameterCoordinateKernel a).comap (Prod.fst : RawLabel M → Arr I M.U 0)
        (@measurable_fst (Arr I M.U 0) (HilbertCode (M.ownKernel 0)) _ inferInstance))
      (Eπ.measure (M.parameterLaw 1)) := by
  have he : ∀ᵐ p ∂M.parameterLaw 1, ∃ e :
      {q : I → HilbertCode (M.ownKernel 0) //
        (p,q) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} ≃
      {q : HilbertCode (M.ownKernel 0) // (tupleParameter M p a,q) ∈ S},
      ∀ z, (e z).val = z.val a := by
    filter_upwards [hS] with p hp
    exact ⟨exactFibreSlotEquiv (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S p a
      (hp a),fun _ => rfl⟩
  have hη : HasCondDistrib id (fun p => tupleParameter M p a)
      (M.parameterCoordinateKernel a) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩
  exact Eπ.parameter_conditional_of_fibrewise E (M.parameterLaw 1) (M.parameterLaw 0)
    (fun p => tupleParameter M p a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd) he
    (M.parameterCoordinateKernel a) hη

lemma rawCounting_label_transition (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) (a b : I) :
    HasCondDistrib (rawLabelSlot M b) (rawLabelSlot M a) (rawLabelTransition M Λ a b)
      (Eπ.measure (M.parameterLaw 1)) := by
  have h := ConditionalTransport.map_observation
    (rawCounting_parameter_given_label M Λ hk hm hind S hS E Eπ a)
    (rawMatchedLabel M Λ a b) (measurable_rawMatchedLabel M Λ hk hm hind a b)
  change HasLaw _ _ _ at h ⊢
  apply h.congr
  filter_upwards [Eπ.ae_mem (M.parameterLaw 1)] with v hv
  refine Prod.ext (by rfl) ?_
  refine Prod.ext (by rfl) ?_
  dsimp only [rawLabelSlot,rawMatchedLabel]
  rw [exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
    (measurable_tupleParameter M) hk hm hind a hv]
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P Q U Z : Type*} [MeasurableSpace Q] [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma observation_conditional (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (o : P → Q) (ho : Measurable o) (η : Kernel U Q) [IsMarkovKernel η] (hη : HasCondDistrib o t η μ) :
    HasCondDistrib (fun x : P × Z => o x.1) (fun x : P × Z => (t x.1,x.2))
      (η.comap (Prod.fst : U × Z → U) (@measurable_fst U Z _ ‹MeasurableSpace Z›)) ((E.comapBase t ht.measurable).measure μ) := by
  have hobs := E.comapBase_preserving μ ν t ht
  refine ⟨(hobs.measurable.prodMk (ho.comp measurable_fst)).aemeasurable,?_⟩
  rw [hobs.map_eq]
  apply Measure.ext_of_lintegral
  intro F hF
  have hjoint : Measurable (fun x : P × Z => ((t x.1,x.2),o x.1)) :=
    hobs.measurable.prodMk (ho.comp measurable_fst)
  rw [lintegral_map hF hjoint]
  have hleft := (E.comapBase t ht.measurable).lintegral_measure μ
    (fun x : P × Z => F ((t x.1,x.2),o x.1)) (hF.comp (hobs.measurable.prodMk (ho.comp measurable_fst)))
  rw [hleft]
  rw [Measure.lintegral_compProd hF]
  have hg : Measurable (fun x : U × Z => ∫⁻ p, F (x,p) ∂η x.1) :=
    Measurable.lintegral_kernel_prod_right (f := fun x p => F (x,p)) hF (κ := η.comap (Prod.fst : U × Z → U) measurable_fst)
  simp only [Kernel.comap_apply]
  rw [E.lintegral_measure ν _ hg]
  let H : U × Q → ℝ≥0∞ := fun up => ∑' n, (E.domain n).indicator
    (fun u => F ((u,E.section_ n u),up.2)) up.1
  have hH : Measurable H := by
    apply Measurable.tsum
    intro n
    exact ((hF.comp ((measurable_fst.prodMk ((E.measurable_section n).comp measurable_fst)).prodMk
      measurable_snd)).indicator ((E.measurable_domain n).preimage measurable_fst))
  have hpair : MeasurePreserving (fun p => (t p,o p)) μ (ν ⊗ₘ η) :=
    ⟨ht.measurable.prodMk ho,by simpa only [ht.map_eq] using hη.map_eq⟩
  have he := hpair.lintegral_comp hH
  rw [Measure.lintegral_compProd hH] at he
  change (∫⁻ p, H (t p,o p) ∂μ) = _
  rw [he]
  apply lintegral_congr
  intro u
  dsimp only [H]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    symm
    exact lintegral_indicator_kernel (η u) (E.domain n) u (fun p => F ((u,E.section_ n u),p))
  · intro n
    by_cases hu : u ∈ E.domain n
    · have hf : Measurable (fun p : Q => F ((u,E.section_ n u),p)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      convert hf.aemeasurable using 1
      ext p
      exact Set.indicator_of_mem hu _
    · simp only [Set.indicator_of_notMem hu]
      exact measurable_const.aemeasurable
end BorelFibreEnumeration

section
open MeasureTheory ProbabilityTheory Set
namespace BorelFibreEnumeration
variable {P Q U Z W : Type*} [MeasurableSpace Q] [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace W] [StandardBorelSpace W]
  {S : Set (P × Z)} (E : BorelFibreEnumeration S)
  {R : Set (U × W)} (D : BorelFibreEnumeration R)

include D in
lemma observation_conditional_of_fibrewise
    (μ : Measure P) [SigmaFinite μ] (ν : Measure U) [SigmaFinite ν]
    (t : P → U) (ht : MeasurePreserving t μ ν)
    (f : P × Z → W) (hf : Measurable f)
    (he : ∀ᵐ p ∂μ, ∃ e : {z : Z // (p,z) ∈ S} ≃ {w : W // (t p,w) ∈ R},
      ∀ z, (e z).val = f (p,z.val))
    (o : P → Q) (ho : Measurable o) (η : Kernel U Q) [IsMarkovKernel η] (hη : HasCondDistrib o t η μ) :
    HasCondDistrib (fun x : P × Z => o x.1) (fun x : P × Z => (t x.1,f x))
      (η.comap (Prod.fst : U × W → U) (@measurable_fst U W _ ‹MeasurableSpace W›))
      (E.measure μ) := by
  have hobs : MeasurePreserving (fun x : P × Z => (x.1,f x)) (E.measure μ)
      ((D.comapBase t ht.measurable).measure μ) :=
    E.measurePreserving_fibrewise (D.comapBase t ht.measurable) μ μ id
      (MeasurePreserving.id μ) f hf he
  have hp := D.comapBase_preserving μ ν t ht
  have hc := D.observation_conditional μ ν t ht o ho η hη
  change HasLaw _ _ _ at hc ⊢
  rw [hp.map_eq] at hc
  have hout : MeasurePreserving (fun x : P × Z => (t x.1,f x)) (E.measure μ) (D.measure ν) :=
    hp.comp hobs
  rw [hout.map_eq]
  exact hc.comp hobs.hasLaw
end BorelFibreEnumeration

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
abbrev RawLabelSquare := Arr I M.U 2 × (I → I → HilbertCode (M.ownKernel 0))
def rawLabelRow (a : I) (x : RawLabelSquare M) : RawLabelTuple M := (plane 1 0 a x.1,x.2 a)
omit [DecidableEq I] in
lemma measurable_rawLabelRow (a : I) : Measurable (rawLabelRow M a) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    ((measurable_pi_apply a).comp measurable_snd)

def rawLabelColumn (s : I) (x : RawLabelSquare M) : RawLabelTuple M :=
  (plane 1 (Fin.last 1) s x.1,fun a => x.2 a s)
omit [DecidableEq I] in
lemma measurable_rawLabelColumn (s : I) : Measurable (rawLabelColumn M s) :=
  ((measurable_plane _ _ _).comp measurable_fst).prodMk
    (Measurable.of_eval fun a => (measurable_pi_apply s).comp
      ((measurable_pi_apply a).comp measurable_snd))

lemma rawCounting_parameter_pair_given_row (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a s t : I) (hst : s ≠ t) :
    HasCondDistrib (fun x : RawLabelSquare M =>
      (plane 1 (Fin.last 1) s x.1,plane 1 (Fin.last 1) t x.1))
      (rawLabelRow M a)
      (((M.parameterCoordinateKernel a).comap (plane 0 0 s) (measurable_plane _ _ _) ×ₖ
        (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _)).comap
          (Prod.fst : RawLabelTuple M → Arr I M.U 1)
          (@measurable_fst (Arr I M.U 1) (I → HilbertCode (M.ownKernel 0)) _ inferInstance)) (Eσ.measure (M.parameterLaw 2)) := by
  have he := (rawSquare_row_completion M Λ hM hk hL hm S hS).mono
    (fun e he => rawSquare_row_bijective M Λ hk hm hind e a (he a))
  exact Eσ.observation_conditional_of_fibrewise Eπ _ _ (plane 1 0 a)
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun x => x.2 a) ((measurable_pi_apply a).comp measurable_snd) he
    (fun e => (plane 1 (Fin.last 1) s e,plane 1 (Fin.last 1) t e))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _)) _
    (parameter_pair_geometry M hM hk a s t hst)

lemma rawCounting_target_pair_given_row (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a b s t : I) (hst : s ≠ t) :
    HasCondDistrib (fun x : RawLabelSquare M =>
      (rawLabelSlot M s (rawLabelRow M b x),rawLabelSlot M t (rawLabelRow M b x)))
      (rawLabelRow M a)
      ((rawLabelTransition M Λ a b).comap (rawLabelSlot M s) (measurable_rawLabelSlot M s) ×ₖ
       (rawLabelTransition M Λ a b).comap (rawLabelSlot M t) (measurable_rawLabelSlot M t))
      (Eσ.measure (M.parameterLaw 2)) := by
  let κ := (M.parameterCoordinateKernel a).comap (Prod.fst : RawLabel M → Arr I M.U 0)
    (@measurable_fst (Arr I M.U 0) (HilbertCode (M.ownKernel 0)) _ inferInstance)
  let fs : RawLabelTuple M × Arr I M.U 1 → RawLabel M :=
    fun x => rawMatchedLabel M Λ a b (rawLabelSlot M s x.1,x.2)
  let ft : RawLabelTuple M × Arr I M.U 1 → RawLabel M :=
    fun x => rawMatchedLabel M Λ a b (rawLabelSlot M t x.1,x.2)
  have hfs : Measurable fs := (measurable_rawMatchedLabel M Λ hk hm hind a b).comp
    (((measurable_rawLabelSlot M s).comp measurable_fst).prodMk measurable_snd)
  have hft : Measurable ft := (measurable_rawMatchedLabel M Λ hk hm hind a b).comp
    (((measurable_rawLabelSlot M t).comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable (fun x : RawLabelTuple M × (Arr I M.U 1 × Arr I M.U 1) =>
      (fs (x.1,x.2.1),ft (x.1,x.2.2))) :=
    (hfs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hft.comp (measurable_fst.prodMk measurable_snd.snd))
  have hbase := rawCounting_parameter_pair_given_row M Λ hM hk hL hm hind S hS Eπ Eσ a s t hst
  have hker : (((M.parameterCoordinateKernel a).comap (plane 0 0 s) (measurable_plane _ _ _) ×ₖ
        (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _)).comap
          (Prod.fst : RawLabelTuple M → Arr I M.U 1)
            (@measurable_fst (Arr I M.U 1) (I → HilbertCode (M.ownKernel 0)) _ inferInstance)) =
      κ.comap (rawLabelSlot M s) (measurable_rawLabelSlot M s) ×ₖ
      κ.comap (rawLabelSlot M t) (measurable_rawLabelSlot M t) := by
    ext x : 1
    simp only [Kernel.comap_apply,Kernel.prod_apply,κ,rawLabelSlot,tupleParameter]
  rw [hker] at hbase
  have h := ConditionalTransport.map_observation hbase _ hpair
  change HasCondDistrib _ _ (Rokhlin.Kernel.depMap _ _) _ at h
  rw [Rokhlin.Kernel.depMap_prod _ _ hfs hft] at h
  have hs := Rokhlin.Kernel.depMap_comap κ
    (measurable_rawMatchedLabel M Λ hk hm hind a b) (rawLabelSlot M s) (measurable_rawLabelSlot M s)
  have ht := Rokhlin.Kernel.depMap_comap κ
    (measurable_rawMatchedLabel M Λ hk hm hind a b) (rawLabelSlot M t) (measurable_rawLabelSlot M t)
  change (rawLabelTransition M Λ a b).comap _ _ = Rokhlin.Kernel.depMap _ fs at hs
  change (rawLabelTransition M Λ a b).comap _ _ = Rokhlin.Kernel.depMap _ ft at ht
  rw [←hs,←ht] at h
  change HasLaw _ _ _ at h ⊢
  apply h.congr
  filter_upwards [Eσ.ae_mem (M.parameterLaw 2)] with x hx
  refine Prod.ext (by rfl) ?_
  dsimp only [fs,ft,rawMatchedLabel,rawLabelSlot,rawLabelRow]
  rw [exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
      (measurable_tupleParameter M) hk hm hind a (hx.2 s),
    exactMatching_exact (M.ownKernel 0) Λ (tupleParameter M)
      (measurable_tupleParameter M) hk hm hind a (hx.2 t)]
  rw [parameter_cell_commute M b s x.1,parameter_cell_commute M b t x.1]
end ArrayObjects.Object.Rolled
end

namespace SigmaFiniteConditional
open MeasureTheory ProbabilityTheory
variable {Ω A B : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} [SigmaFinite μ] {x : Ω → A} {y : Ω → B}
  {κ : Kernel A B} [IsMarkovKernel κ]

omit [SigmaFinite μ] in
lemma sigmaFinite_trim (hx : Measurable x) [hσ : SigmaFinite (μ.map x)] :
    SigmaFinite (μ.trim hx.comap_le) := by
  rw [←map_trim_comap hx] at hσ
  exact SigmaFinite.of_map _ (Measurable.of_comap_le (le_refl _)).aemeasurable hσ

lemma condExp_of_kernel (hx : Measurable x) [SigmaFinite (μ.map x)]
    (h : HasCondDistrib y x κ μ) (g : B → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ b, g b ∂κ (x ω)) := by
  let := sigmaFinite_trim (μ := μ) hx
  have hm : StronglyMeasurable (fun a => ∫ b, g b ∂κ a) := hg.integral_kernel
  have hj : Integrable (fun ab : A × B => g ab.2) ((μ.map x) ⊗ₘ κ) := by
    rw [←h.map_eq]
    exact (integrable_map_measure (hg.comp_measurable measurable_snd).aestronglyMeasurable
      h.aemeasurable).mpr hgi
  have hi : Integrable (fun a => ∫ b, g b ∂κ a) (μ.map x) := by
    exact hj.integral_compProd
  have hix : Integrable (fun ω => ∫ b, g b ∂κ (x ω)) μ :=
    (integrable_map_measure hm.aestronglyMeasurable hx.aemeasurable).mp hi
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hx.comap_le hgi
    (fun _ _ _ => hix.integrableOn) _
    ((hm.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable)
  rintro _ ⟨s,hs,rfl⟩ _
  rw [←setIntegral_map hs hm.aestronglyMeasurable hx.aemeasurable]
  have he := Measure.setIntegral_compProd hs MeasurableSet.univ hj.integrableOn
  simp only [Measure.restrict_univ] at he
  rw [←he,←h.map_eq]
  have hgm : AEStronglyMeasurable (fun ab : A × B => g ab.2)
      (μ.map (fun ω => (x ω,y ω))) := (hg.comp_measurable measurable_snd).aestronglyMeasurable
  rw [setIntegral_map (hs.prod MeasurableSet.univ) hgm h.aemeasurable]
  have hset : (fun ω => (x ω,y ω)) ⁻¹' (s ×ˢ Set.univ) = x ⁻¹' s := by
    ext ω
    simp
  rw [hset]
end SigmaFiniteConditional

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} [SigmaFinite μ] {ν : Measure X} [SigmaFinite ν]
  {ρ : Measure Y} {τ : Measure Z} [SigmaFinite τ]
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

omit [SigmaFinite μ] in
lemma operator_ae_eq_condExp_integrable
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) :
    (fun ω => operator hx hy g (x ω)) =ᵐ[μ]
      μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hσ : SigmaFinite (μ.map x) := by rw [hx.map_eq]; infer_instance
  let := SigmaFiniteConditional.sigmaFinite_trim (μ := μ) hx.measurable
  have hp := pull_adjoint_projection hx (pull hy g)
  have hi : Integrable (pull hy g : Ω → ℂ) μ :=
    ((hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi).congr (Lp.coeFn_compMeasurePreserving g hy).symm
  have hc := (Lp.memLp (pull hy g)).condExpL2_ae_eq_condExp' (𝕜 := ℂ) hx.measurable.comap_le hi
  rw [Lp.toLp_coeFn, ←hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy g) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving g hy)))

lemma screened_operator_integrable
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ)
    (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) :
    operator hx hy g = (pull hz ∘L operator (hz.comp hx) hy) g := by
  have hσx : SigmaFinite (μ.map x) := by rw [hx.map_eq]; infer_instance
  have hσz : SigmaFinite (μ.map (z ∘ x)) := by rw [(hz.comp hx).map_eq]; infer_instance
  apply (Lp.compMeasurePreservingₗᵢ ℂ x hx).injective
  change pull hx (operator hx hy g) = (pull hx ∘L pull hz) (operator (hz.comp hx) hy g)
  rw [←pull_comp]
  apply Lp.ext
  have hi : Integrable (fun ω => g (y ω)) μ := (hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi
  have hce := (SigmaFiniteConditional.condExp_of_kernel hx.measurable h g
    g.1.stronglyMeasurable hi).trans
    (SigmaFiniteConditional.condExp_of_kernel (hz.measurable.comp hx.measurable)
      h.comp_right g g.1.stronglyMeasurable hi).symm
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    ((operator_ae_eq_condExp_integrable hx hy g hgi).trans
      (hce.trans ((operator_ae_eq_condExp_integrable (hz.comp hx) hy g hgi).symm.trans
        (Lp.coeFn_compMeasurePreserving _ (hz.comp hx)).symm)))

theorem screened_operator_sigmaFinite
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ) :
    operator hx hy = pull hz ∘L operator (hz.comp hx) hy := by
  apply ContinuousLinearMap.ext
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun g => operator hx hy g = (pull hz ∘L operator (hz.comp hx) hy) g)
  · intro c s hs hμs
    apply screened_operator_integrable hx hy hz h
    change Integrable (indicatorConstLp 2 hs hμs.ne c : Y → ℂ) ρ
    apply Integrable.congr _ (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c)).symm
    exact (integrable_indicator_iff hs).mpr (integrableOn_const (C := c) hμs.ne)
  · intro f g hf hg hfg hF hG
    simp only [map_add,hF,hG]
  · exact isClosed_eq (operator hx hy).continuous
      (pull hz ∘L operator (hz.comp hx) hy).continuous
end
section

variable {Ω R X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} [SigmaFinite μ] {σ : Measure R} [SigmaFinite σ]
  {ν : Measure X} {ρ : Measure Y}
  {r : Ω → R} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel R X} {η : Kernel R Y} [IsMarkovKernel κ] [IsMarkovKernel η]

lemma product_operator_inner_integrable
    (hr : MeasurePreserving r μ σ) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (h : HasCondDistrib (fun ω => (x ω,y ω)) r (κ ×ₖ η) μ)
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 ρ)
    (hfi : Integrable (f : X → ℂ) ν) (hgi : Integrable (g : Y → ℂ) ρ) :
    inner ℂ f (operator hx hy g) =
      inner ℂ (operator hr hx f) (operator hr hy g) := by
  have hσ : SigmaFinite (μ.map r) := by rw [hr.map_eq]; infer_instance
  have hf : HasCondDistrib x r κ μ := by simpa using h.fst
  have hg : HasCondDistrib y r η μ := by simpa using h.snd
  have hfx : Integrable (fun ω => f (x ω)) μ :=
    (hx.integrable_comp f.1.stronglyMeasurable.aestronglyMeasurable).mpr hfi
  have hgy : Integrable (fun ω => g (y ω)) μ :=
    (hy.integrable_comp g.1.stronglyMeasurable.aestronglyMeasurable).mpr hgi
  have hef := (operator_ae_eq_condExp_integrable hr hx f hfi).trans
    (SigmaFiniteConditional.condExp_of_kernel hr.measurable hf f f.1.stronglyMeasurable hfx)
  have heg := (operator_ae_eq_condExp_integrable hr hy g hgi).trans
    (SigmaFiniteConditional.condExp_of_kernel hr.measurable hg g g.1.stronglyMeasurable hgy)
  let F : R × (X × Y) → ℂ := fun u => inner ℂ (f u.2.1) (g u.2.2)
  have hFm : StronglyMeasurable F :=
    (f.1.stronglyMeasurable.comp_measurable measurable_snd.fst).inner
      (g.1.stronglyMeasurable.comp_measurable measurable_snd.snd)
  have hi : Integrable (fun ω => inner ℂ (f (x ω)) (g (y ω))) μ := by
    apply (L2.integrable_inner (pull hx f) (pull hy g)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving f hx,Lp.coeFn_compMeasurePreserving g hy]
      with ω h1 h2
    change inner ℂ (Lp.compMeasurePreserving x hx f ω)
      (Lp.compMeasurePreserving y hy g ω) = _
    rw [h1,h2]
    rfl
  have hFi : Integrable F ((μ.map r) ⊗ₘ (κ ×ₖ η)) := by
    rw [←h.map_eq]
    exact (integrable_map_measure hFm.aestronglyMeasurable h.aemeasurable).mpr hi
  rw [inner_operator]
  calc
    (∫ ω, inner ℂ (f (x ω)) (g (y ω)) ∂μ) = ∫ u, F u ∂(μ.map r) ⊗ₘ (κ ×ₖ η) :=
      h.integral_comp hFm.aestronglyMeasurable
    _ = ∫ u, inner ℂ (∫ z, f z ∂κ u) (∫ z, g z ∂η u) ∂μ.map r := by
      rw [Measure.integral_compProd hFi]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F,Kernel.prod_apply,RCLike.inner_apply]
      simp_rw [mul_comm (g _) _]
      rw [integral_prod_mul (μ := κ u) (ν := η u)
        (fun z => starRingEnd ℂ (f z)) (fun z => g z),integral_conj]
      exact mul_comm _ _
    _ = ∫ ω, inner ℂ (∫ z, f z ∂κ (r ω)) (∫ z, g z ∂η (r ω)) ∂μ := by
      apply integral_map hr.aemeasurable
      exact ((f.1.stronglyMeasurable.integral_kernel).inner
        (g.1.stronglyMeasurable.integral_kernel)).aestronglyMeasurable
    _ = ∫ ω, inner ℂ (operator hr hx f (r ω)) (operator hr hy g (r ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hef,heg] with ω h1 h2
      rw [h1,h2]
    _ = inner ℂ (operator hr hx f) (operator hr hy g) := by
      rw [L2.inner_def]
      exact hr.hasLaw.integral_comp (f := fun u =>
        inner ℂ (operator hr hx f u) (operator hr hy g u))
        (((operator hr hx f).1.stronglyMeasurable).inner (𝕜 := ℂ)
          (operator hr hy g).1.stronglyMeasurable).aestronglyMeasurable

lemma indicator_integrable {A : Type*} [MeasurableSpace A] (ζ : Measure A)
    (s : Set A) (hs : MeasurableSet s) (hζ : ζ s < ∞) (c : ℂ) :
    Integrable (indicatorConstLp 2 hs hζ.ne c : A → ℂ) ζ := by
  apply Integrable.congr _ (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hζ.ne) (c := c)).symm
  exact (integrable_indicator_iff hs).mpr (integrableOn_const (C := c) hζ.ne)

theorem product_operator
    (hr : MeasurePreserving r μ σ) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (h : HasCondDistrib (fun ω => (x ω,y ω)) r (κ ×ₖ η) μ) :
    operator hx hy = (operator hr hx).adjoint ∘L operator hr hy := by
  have htest (g : Lp ℂ 2 ρ) (hgi : Integrable (g : Y → ℂ) ρ) (f : Lp ℂ 2 ν) :
      inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g) := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun f => inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g))
    · intro d t ht hν
      exact product_operator_inner_integrable hr hx hy h _ g (indicator_integrable ν t ht hν d) hgi
    · intro f₁ f₂ hf₁ hf₂ hfg h1 h2
      simp only [map_add,inner_add_left,h1,h2]
    · exact isClosed_eq (continuous_id.inner continuous_const)
        ((operator hr hx).continuous.inner continuous_const)
  have hi : ∀ (f : Lp ℂ 2 ν) (g : Lp ℂ 2 ρ),
      inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g) := by
    intro f
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun g => inner ℂ f (operator hx hy g) = inner ℂ (operator hr hx f) (operator hr hy g))
    · intro c s hs hρ
      exact htest _ (indicator_integrable ρ s hs hρ c) f
    · intro g₁ g₂ hg₁ hg₂ hfg h1 h2
      simp only [map_add,inner_add_right,h1,h2]
    · exact isClosed_eq (continuous_const.inner (operator hx hy).continuous)
        (continuous_const.inner (operator hr hy).continuous)
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.comp_apply,adjoint_inner_right]
  exact hi f g

end

variable {Ω P Z I : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace Z]
  {μ : Measure Ω} [SigmaFinite μ] {π : Measure P} [SigmaFinite π]
  {ξ : Measure Z} [SigmaFinite ξ]

lemma operator_congr {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ₁ : Measure A} {μ₂ : Measure B} {μ₃ : Measure C}
    {f f' : A → B} {g g' : A → C}
    (hf : MeasurePreserving f μ₁ μ₂) (hg : MeasurePreserving g μ₁ μ₃)
    (hf' : MeasurePreserving f' μ₁ μ₂) (hg' : MeasurePreserving g' μ₁ μ₃)
    (he : f = f') (he' : g = g') : operator hf hg = operator hf' hg' := by
  subst f'; subst g'; rfl

lemma square_operator (row col : I → Ω → P) (slot : I → P → Z)
    (hr : ∀ a, MeasurePreserving (row a) μ π)
    (hc : ∀ s, MeasurePreserving (col s) μ π)
    (hq : ∀ i, MeasurePreserving (slot i) π ξ)
    (hcomm : ∀ a s, slot s ∘ row a = slot a ∘ col s)
    (a b s t : I) (K : Kernel Z Z) [IsMarkovKernel K]
    (h : HasCondDistrib (fun ω => (slot s (row b ω),slot t (row b ω))) (row a)
      (K.comap (slot s) (hq s).measurable ×ₖ K.comap (slot t) (hq t).measurable) μ) :
    operator (hq s) (hq t) = (operator (hq a) (hq b)).adjoint ∘L
      operator (hq s) (hq t) ∘L operator (hq a) (hq b) := by
  have hscreen (j : I)
      (hj : HasCondDistrib (slot j ∘ row b) (row a) (K.comap (slot j) (hq j).measurable) μ) :
      operator (hr a) ((hq j).comp (hr b)) = pull (hq j) ∘L operator (hq a) (hq b) := by
    rw [screened_operator_sigmaFinite (hr a) ((hq j).comp (hr b)) (hq j) hj]
    have hcol := operator_congr ((hq j).comp (hr a)) ((hq j).comp (hr b))
      ((hq a).comp (hc j)) ((hq b).comp (hc j)) (hcomm a j) (hcomm b j)
    rw [hcol,operator_pullback (hc j) (hq a) (hq b)]
  have hfst : HasCondDistrib (slot s ∘ row b) (row a) (K.comap (slot s) (hq s).measurable) μ :=
    by simpa only [Kernel.fst_prod, Function.comp_def] using h.fst
  have hsnd : HasCondDistrib (slot t ∘ row b) (row a) (K.comap (slot t) (hq t).measurable) μ :=
    by simpa only [Kernel.snd_prod, Function.comp_def] using h.snd
  have hp := product_operator (hr a) ((hq s).comp (hr b)) ((hq t).comp (hr b)) h
  rw [operator_pullback (hr b) (hq s) (hq t),hscreen s hfst,hscreen t hsnd] at hp
  apply hp.trans
  simp only [adjoint_comp,comp_assoc]
  rfl

end JoiningOperator

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

section RawLabelCells
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma rawLabel_cell_commute (a s : I) :
    rawLabelSlot M s ∘ rawLabelRow M a = rawLabelSlot M a ∘ rawLabelColumn M s := by
  funext x
  exact Prod.ext (parameter_cell_commute M a s x.1) rfl

lemma rawCounting_square_operator (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (a b s t : I) (hst : s ≠ t) :
    let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
    JoiningOperator.operator (hq s) (hq t) =
      (JoiningOperator.operator (hq a) (hq b)).adjoint ∘L
        JoiningOperator.operator (hq s) (hq t) ∘L
          JoiningOperator.operator (hq a) (hq b) := by
  let := rawLabelTransition_markov M Λ hk hm hind a b
  exact JoiningOperator.square_operator (rawLabelRow M) (rawLabelColumn M) (rawLabelSlot M)
    (rawCounting_rows_preserving M Λ hM hk hL hm hind S hS Eπ Eσ)
    (rawCounting_columns_preserving M Λ hM hk hL hm hind S hS Eπ Eσ)
    (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ)
    (rawLabel_cell_commute M) a b s t (rawLabelTransition M Λ a b)
    (rawCounting_target_pair_given_row M Λ hM hk hL hm hind S hS Eπ Eσ a b s t hst)
end RawLabelCells


universe u
variable {I : Type u} [Fintype I] [retained13 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma ownKernel_tuple_time_preserving : ∀ᵐ p ∂M.parameterLaw 1, ∀ i,
    MeasurePreserving (amap M.timeY 0) (M.ownKernel 0 (tupleParameter M p i))
      (M.ownKernel 0 (amap M.timeU 0 (tupleParameter M p i))) := by
  apply ae_all_iff.mpr
  intro i
  exact (show MeasurePreserving (plane 0 0 i) (M.parameterLaw 1) (M.parameterLaw 0) from
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae
      (M.ownKernel_time_preserving 0)

def rawLabelTime (z : RawLabel M) : RawLabel M :=
  (amap M.timeU 0 z.1,HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) z.2)
def rawLabelTimeInv (z : RawLabel M) : RawLabel M :=
  (amap M.timeU.symm 0 z.1,HilbertCode.transport (amap M.timeU.symm 0) (amapEquiv M.timeY.symm 0) z.2)
def rawLabelTupleTime (z : RawLabelTuple M) : RawLabelTuple M :=
  (amap M.timeU 1 z.1,fun i => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) (z.2 i))

omit [DecidableEq I] in
lemma measurable_rawLabelTime : Measurable (rawLabelTime M) :=
  ((measurable_amap M.timeU.measurable 0).comp measurable_fst).prodMk
    ((HilbertCode.measurable_transport _ (measurable_amap M.timeU.measurable 0) _).comp measurable_snd)

omit [DecidableEq I] in
lemma measurable_rawLabelTimeInv : Measurable (rawLabelTimeInv M) :=
  ((measurable_amap M.timeU.symm.measurable 0).comp measurable_fst).prodMk
    ((HilbertCode.measurable_transport _ (measurable_amap M.timeU.symm.measurable 0) _).comp measurable_snd)

omit [DecidableEq I] in
lemma measurable_rawLabelTupleTime : Measurable (rawLabelTupleTime M) :=
  ((measurable_amap M.timeU.measurable 1).comp measurable_fst).prodMk
    (Measurable.of_eval fun i => (HilbertCode.measurable_transport _
      (measurable_amap M.timeU.measurable 0) _).comp ((measurable_pi_apply i).comp measurable_snd))

omit [DecidableEq I] in
lemma localGraph_time_equiv (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ u ∂M.parameterLaw 0,
      ∃ e : {q // (u,q) ∈ S} ≃ {q // (amap M.timeU 0 u,q) ∈ S},
        ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1,
      ∃ e : {q // (tupleParameter M p i,q) ∈ S} ≃
        {q // (amap M.timeU 0 (tupleParameter M p i),q) ∈ S},
        ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val := by
    filter_upwards [ownKernel_tuple_time_preserving M,goodTuple_time_preserving M Λ hL,hS,
      (M.parameterLaw_invariant 1).quasiMeasurePreserving.ae hS] with p hk hΛ h1 h2
    refine ⟨localGraphTimeEquiv (M.ownKernel 0) Λ (tupleParameter M) (amapEquiv M.timeU 0)
      (amapEquiv M.timeY 0) p (amap M.timeU 1 p) (tupleParameter_time M p) hk hΛ hm S i ?_ ?_,fun _ => rfl⟩
    · intro q
      exact (Set.ext_iff.mp (h1 i) q).symm
    · intro q
      exact (Set.ext_iff.mp (h2 i) q).symm
  have hd := ae_map_descent (P := fun u =>
    ∃ e : {q // (u,q) ∈ S} ≃ {q // (amap M.timeU 0 u,q) ∈ S},
      ∀ q, (e q).val = HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) q.val)
    (M.parameterLaw 1) (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

include retained13 in
lemma rawCounting_time_preserving (i : I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) (E : BorelFibreEnumeration S) :
    MeasurePreserving (rawLabelTime M) (E.measure (M.parameterLaw 0)) (E.measure (M.parameterLaw 0)) := by
  let _ := retained13
  apply E.measurePreserving_fibrewise E _ _ (amap M.timeU 0) (M.parameterLaw_invariant 0)
    (fun z => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) z.2)
    ((HilbertCode.measurable_transport _ (measurable_amap M.timeU.measurable 0) _).comp measurable_snd)
  exact localGraph_time_equiv M Λ i hL hm S hS

omit [DecidableEq I] in
lemma rawTupleCounting_time_preserving
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M))) :
    MeasurePreserving (rawLabelTupleTime M) (Eπ.measure (M.parameterLaw 1)) (Eπ.measure (M.parameterLaw 1)) := by
  apply Eπ.measurePreserving_fibrewise Eπ _ _ (amap M.timeU 1) (M.parameterLaw_invariant 1)
    (fun z i => HilbertCode.transport (amap M.timeU 0) (amapEquiv M.timeY 0) (z.2 i))
    (Measurable.of_eval fun i => (HilbertCode.measurable_transport _
      (measurable_amap M.timeU.measurable 0) _).comp ((measurable_pi_apply i).comp measurable_snd))
  filter_upwards [ownKernel_tuple_time_preserving M,goodTuple_time_preserving M Λ hL] with p hk hΛ
  exact ⟨exactCodeEquivTransport (M.ownKernel 0) Λ (tupleParameter M) (amapEquiv M.timeU 0)
    (amapEquiv M.timeY 0) p (amap M.timeU 1 p) (tupleParameter_time M p) hk hΛ (hm p)
    (hm (amap M.timeU 1 p)),fun _ => rfl⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory ContinuousLinearMap
variable {Z : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  (τ σ : Z → Z) (hτ : MeasurePreserving τ ξ ξ) (hσ : MeasurePreserving σ ξ ξ)

lemma lp_time_inverse (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) (v : Lp ℂ 2 ξ) :
    Lp.compMeasurePreservingₗᵢ ℂ τ hτ (Lp.compMeasurePreservingₗᵢ ℂ σ hσ v) = v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreservingₗᵢ ℂ σ hσ v) hτ,
    hτ.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving v hσ),hστ] with z h1 h2 h3
  exact h1.trans (h2.trans (congrArg (fun x => v x) h3))

def aeLpTime (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ τ hτ)
    (fun v => ⟨Lp.compMeasurePreservingₗᵢ ℂ σ hσ v,lp_time_inverse ξ τ σ hτ hσ hστ v⟩)

lemma aeLpTime_coe (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) (v : Lp ℂ 2 ξ) :
    (aeLpTime ξ τ σ hτ hσ hστ v : Z → ℂ) =ᵐ[ξ] (fun z => v (τ z)) :=
  Lp.coeFn_compMeasurePreserving v hτ

include hτ in
omit hσ in
lemma inverse_measurePreserving (hσm : Measurable σ) (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) :
    MeasurePreserving σ ξ ξ := by
  refine ⟨hσm,?_⟩
  calc
    ξ.map σ = (ξ.map τ).map σ := congrArg (Measure.map σ) hτ.map_eq.symm
    _ = ξ.map (σ ∘ τ) := Measure.map_map hσm hτ.measurable
    _ = ξ.map id := Measure.map_congr hστ
    _ = ξ := Measure.map_id
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma localGraph_code_properties (i : I) (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
      q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular := by
  have hp : ∀ᵐ p ∂M.parameterLaw 1, ∀ q, (tupleParameter M p i,q) ∈ S →
      q.base = tupleParameter M p i ∧ q.IsCanonical ∧ q.IsUnimodular := by
    filter_upwards [hS] with p hp
    intro q hq
    have he : (p,q) ∈ rawLineGraph M Λ i := (Set.ext_iff.mp (hp i) q).mpr hq
    obtain ⟨a,ha,hq⟩ := he
    change a i = q at hq
    rw [←hq]
    exact ⟨ha.1 i,ha.2.1 i⟩
  have hd := ae_map_descent (P := fun u => ∀ q, (u,q) ∈ S →
    q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) (M.parameterLaw 1)
    (measurable_plane 0 0 i) hp
  rwa [M.parameterLaw_consistent 0 0 i] at hd

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma rawLabelTime_left_inverse (i : I) (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}) (E : BorelFibreEnumeration S) :
    ∀ᵐ z ∂E.measure (M.parameterLaw 0), rawLabelTimeInv M (rawLabelTime M z) = z := by
  filter_upwards [E.ae_mem (M.parameterLaw 0),
    E.ae_base (M.parameterLaw 0) (localGraph_code_properties M Λ i S hS),
    E.ae_base (M.parameterLaw 0) (M.ownKernel_time_preserving 0)] with z hz hq htime
  obtain ⟨hb,hc,hu⟩ := hq z.2 hz
  apply Prod.ext
  · exact (amapEquiv M.timeU 0).symm_apply_apply z.1
  · exact HilbertCode.transport_inverse (amapEquiv M.timeU 0)
      (amapEquiv M.timeY 0) z.2 hu hc (by rw [hb]; exact htime)
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  (ρ : Measure W) (ξ : Measure Z) (x y : W → Z)
  (hx : MeasurePreserving x ρ ξ) (hy : MeasurePreserving y ρ ξ)
  (τ : Z → Z) (hτ : MeasurePreserving τ ξ ξ)
  (t : W → W) (ht : MeasurePreserving t ρ ρ)

include ht in
lemma operator_time_conjugate (hxt : x ∘ t = τ ∘ x) (hyt : y ∘ t = τ ∘ y) :
    (pull hτ).adjoint ∘L operator hx hy ∘L pull hτ = operator hx hy := by
  have he : operator (hτ.comp hx) (hτ.comp hy) = operator (hx.comp ht) (hy.comp ht) := by
    exact operator_congr _ _ _ _ hxt.symm hyt.symm
  rw [operator,pull_comp hx hτ,pull_comp hy hτ,adjoint_comp] at he
  simpa only [operator,comp_assoc] using he.trans (operator_pullback ht hx hy)

include ht in
lemma operator_commutes_time (hxt : x ∘ t = τ ∘ x) (hyt : y ∘ t = τ ∘ y)
    (V : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ) (hV : (V : Lp ℂ 2 ξ →L[ℂ] Lp ℂ 2 ξ) = pull hτ) :
    ∀ v, V (operator hx hy v) = operator hx hy (V v) := by
  have he := operator_time_conjugate ρ ξ x y hx hy τ hτ t ht hxt hyt
  rw [←hV,V.adjoint_eq_symm] at he
  intro v
  have hh := congrArg (fun A : Lp ℂ 2 ξ →L[ℂ] Lp ℂ 2 ξ => V (A v)) he
  change V (V.symm (operator hx hy (V v))) = V (operator hx hy v) at hh
  rw [V.apply_symm_apply] at hh
  exact hh.symm
end JoiningOperator

section

open ContinuousLinearMap
open scoped InnerProductSpace

section

theorem partial_unitary_algebra {A : Type*} [Monoid A] [StarMul A]
    (a : A) (h₁ : a = star a * a * a) (h₂ : a = a * a * star a) :
    star a * a = a * star a ∧ IsStarProjection (star a * a) := by
  have hn : star a * a = a * star a := calc
    star a * a = star a * (a * a * star a) := congrArg (star a * ·) h₂
    _ = (star a * a * a) * star a := by simp only [mul_assoc]
    _ = a * star a := congrArg (· * star a) h₁.symm
  refine ⟨hn, ?_⟩
  apply IsStarProjection.mk
  · change (star a * a) * (star a * a) = star a * a
    calc
      (star a * a) * (star a * a) = (star a * a) * (a * star a) := by rw [hn]
      _ = ((star a * a) * a) * star a := by simp only [mul_assoc]
      _ = a * star a := by rw [← h₁]
      _ = star a * a := hn.symm
  · simp only [IsSelfAdjoint, star_mul, star_star]

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partial_unitary_range (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    (M.adjoint * M).range = M.range := by
  have hn := (partial_unitary_algebra M h₁ h₂).1
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    refine ⟨M.adjoint w, ?_⟩
    have hh := congrArg (fun A : H →L[ℂ] H => A w) hn
    exact hh.symm
  · rintro v ⟨w, rfl⟩
    refine ⟨M w, ?_⟩
    exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm

theorem partial_unitary_range_adjoint (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    M.range = M.adjoint.range := by
  have ha₁ : M.adjoint = M * M.adjoint * M.adjoint := by
    change star M = M * star M * star M
    have hh := congrArg star h₂
    simpa only [← star_eq_adjoint, star_mul, star_star, mul_assoc] using hh
  have ha₂ : M.adjoint = M.adjoint * M.adjoint * M := by
    change star M = star M * star M * M
    have hh := congrArg star h₁
    simpa only [← star_eq_adjoint, star_mul, star_star, mul_assoc] using hh
  rw [← partial_unitary_range M h₁ h₂,
    ← partial_unitary_range M.adjoint (by simpa using ha₁) (by simpa using ha₂),
    adjoint_adjoint]
  exact congrArg (fun A : H →L[ℂ] H => A.range) (partial_unitary_algebra M h₁ h₂).1

theorem partial_unitary_norm_on_range (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (v : H) (hv : v ∈ M.range) :
    ‖M v‖ = ‖v‖ := by
  have hfix : (M.adjoint * M) v = v := by
    rcases hv with ⟨w, rfl⟩
    exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm
  apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [← adjoint_inner_right]
  exact congrArg (fun w => (inner ℂ v w).re) hfix
end

open MeasureTheory Filter

theorem countable_essential_image_of_countable_fibres
    {Z U C : Type*} [MeasurableSpace Z] [MeasurableSpace U]
    [MeasurableSpace C] [MeasurableEq C]
    (ξ : Measure Z) [SigmaFinite ξ] (ν : Measure U) [IsProbabilityMeasure ν]
    (ψ : Z → C) (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (q : U → ℕ → C) (hq : ∀ n, Measurable (fun u => q u n))
    (hocc : ∀ᵐ z ∂ξ, ∀ᵐ u ∂ν, ∃ n, D (ψ z) = q u n) :
    ∃ S : Set C, S.Countable ∧ ∀ᵐ z ∂ξ, ψ z ∈ S := by
  have hm : MeasurableSet {zu : Z × U | ∃ n, D (ψ zu.1) = q zu.2 n} := by
    simp_rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_eq_fun (D.measurable.comp (hψ.comp measurable_fst))
      ((hq n).comp measurable_snd)
  obtain ⟨u, hu⟩ := ((MeasureTheory.Measure.ae_ae_comm hm).mp hocc).exists
  refine ⟨D.symm '' Set.range (q u), (Set.countable_range (q u)).image D.symm, ?_⟩
  filter_upwards [hu] with z hz
  obtain ⟨n, hn⟩ := hz
  exact ⟨q u n, ⟨n, rfl⟩, by rw [← hn, D.symm_apply_apply]⟩

variable {H J K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem deterministic_transition_of_norm_eq
    (U : H →ₗᵢ[ℂ] K) (V : J →ₗᵢ[ℂ] K) (v : J)
    (hn : ‖(U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v‖ = ‖v‖) :
    U ((U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v) = V v := by
  let M := U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap
  have hi : inner ℂ (U (M v)) (V v) = inner ℂ (M v) (M v) := by
    change inner ℂ (U.toContinuousLinearMap (M v)) (V v) = _
    rw [← adjoint_inner_right]
    rfl
  have hz : ‖U (M v) - V v‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), U.norm_map, V.norm_map, hi, inner_self_eq_norm_sq, hn]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
end

section
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partial_unitary_fixed (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) {v : H} (hv : v ∈ M.range) :
    M.adjoint (M v) = v := by
  obtain ⟨w,rfl⟩ := hv
  exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm

lemma partial_unitary_fixed' (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint)
    {v : H} (hv : v ∈ M.range) : M (M.adjoint v) = v := by
  have hn := (partial_unitary_algebra M h₁ h₂).1
  have hh := congrArg (fun A : H →L[ℂ] H => A v) hn
  exact hh.symm.trans (partial_unitary_fixed M h₁ hv)

lemma partial_unitary_closed_range (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    IsClosed (M.range : Set H) := by
  have he : (M.range : Set H) = {v | M (M.adjoint v) = v} := by
    ext v
    exact ⟨fun hv => partial_unitary_fixed' M h₁ h₂ hv,fun hv => ⟨M.adjoint v,hv⟩⟩
  rw [he]
  exact isClosed_eq (M.continuous.comp M.adjoint.continuous) continuous_id

def partialUnitary (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    M.range ≃ₗᵢ[ℂ] M.range where
  toFun v := ⟨M v,⟨v,rfl⟩⟩
  invFun v := ⟨M.adjoint v,by exact (partial_unitary_range_adjoint M h₁ h₂).ge ⟨v,rfl⟩⟩
  map_add' v w := Subtype.ext (M.map_add _ _)
  map_smul' c v := Subtype.ext (M.map_smul _ _)
  left_inv v := Subtype.ext (partial_unitary_fixed M h₁ v.property)
  right_inv v := Subtype.ext (partial_unitary_fixed' M h₁ h₂ v.property)
  norm_map' v := partial_unitary_norm_on_range M h₁ v.val v.property

def commutingRangeUnitary (M : H →L[ℂ] H) (V : H ≃ₗᵢ[ℂ] H)
    (hV : ∀ v, V (M v) = M (V v)) : M.range ≃ₗᵢ[ℂ] M.range where
  toFun v := ⟨V v,by obtain ⟨w,hw⟩ := v.property; exact ⟨V w,by change M (V w) = V v; exact (hV w).symm.trans (congrArg V hw)⟩⟩
  invFun v := ⟨V.symm v,by
    obtain ⟨w,hw⟩ := v.property
    refine ⟨V.symm w,?_⟩
    apply V.injective
    change V (M (V.symm w)) = V (V.symm v)
    rw [hV,V.apply_symm_apply,V.apply_symm_apply]
    exact hw⟩
  map_add' v w := Subtype.ext (V.map_add _ _)
  map_smul' c v := Subtype.ext (V.map_smul _ _)
  left_inv v := Subtype.ext (V.symm_apply_apply v)
  right_inv v := Subtype.ext (V.apply_symm_apply v)
  norm_map' v := V.norm_map v

lemma partialUnitary_commutingRange (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint)
    (V : H ≃ₗᵢ[ℂ] H) (hV : ∀ v, V (M v) = M (V v)) :
    Commute (partialUnitary M h₁ h₂) (commutingRangeUnitary M V hV) := by
  apply LinearIsometryEquiv.ext
  intro v
  apply Subtype.ext
  exact (hV v).symm
end

section
open MeasureTheory
abbrev LabelOrbitVector := (ℤ × ℤ) → ℂ

def labelShiftFirst : LabelOrbitVector ≃ᵐ LabelOrbitVector where
  toFun c p := c (p.1+1,p.2)
  invFun c p := c (p.1-1,p.2)
  left_inv c := by funext p; simp
  right_inv c := by funext p; simp
  measurable_toFun := Measurable.of_eval fun p => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun p => measurable_pi_apply _

def labelShiftSecond : LabelOrbitVector ≃ᵐ LabelOrbitVector where
  toFun c p := c (p.1,p.2+1)
  invFun c p := c (p.1,p.2-1)
  left_inv c := by funext p; simp
  right_inv c := by funext p; simp
  measurable_toFun := Measurable.of_eval fun p => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun p => measurable_pi_apply _

variable {Z H : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : H →ₗᵢ[ℂ] Lp ℂ 2 ξ) (D S : H ≃ₗᵢ[ℂ] H) (v : H)

def labelOrbitLP (p : ℤ × ℤ) : Lp ℂ 2 ξ := U ((D ^ p.1) ((S ^ p.2) v))
def labelOrbit (z : Z) : LabelOrbitVector := fun p => labelOrbitLP ξ U D S v p z
lemma measurable_labelOrbit : Measurable (labelOrbit ξ U D S v) :=
  Measurable.of_eval fun p => (Lp.stronglyMeasurable (labelOrbitLP ξ U D S v p)).measurable

lemma labelOrbitLP_first (p : ℤ × ℤ) :
    labelOrbitLP ξ U D S v (p.1+1,p.2) = U (D ((D ^ p.1) ((S ^ p.2) v))) := by
  unfold labelOrbitLP
  rw [show p.1+1 = 1+p.1 by omega,zpow_add,zpow_one]
  rfl

lemma labelOrbitLP_second (hDS : Commute D S) (p : ℤ × ℤ) :
    labelOrbitLP ξ U D S v (p.1,p.2+1) = U (S ((D ^ p.1) ((S ^ p.2) v))) := by
  unfold labelOrbitLP
  rw [show p.2+1 = 1+p.2 by omega,zpow_add,zpow_one]
  have h := (hDS.zpow_left p.1).eq
  exact congrArg U (congrArg (fun e : H ≃ₗᵢ[ℂ] H => e ((S ^ p.2) v)) h)

variable {W : Type*} [MeasurableSpace W] (ρ : Measure W)
  (source target : W → Z)
lemma labelOrbit_transition
    (hdet : ∀ w : H, ∀ᵐ x ∂ρ, U w (target x) = U (D w) (source x)) :
    ∀ᵐ x ∂ρ, labelOrbit ξ U D S v (target x) =
      labelShiftFirst (labelOrbit ξ U D S v (source x)) := by
  have ha (p : ℤ × ℤ) := hdet ((D ^ p.1) ((S ^ p.2) v))
  filter_upwards [ae_all_iff.mpr ha] with x hx
  funext p
  change labelOrbitLP ξ U D S v p (target x) = labelOrbitLP ξ U D S v (p.1+1,p.2) (source x)
  rw [labelOrbitLP_first]
  exact hx p

lemma labelOrbit_time (hDS : Commute D S) (τ : Z → Z)
    (htime : ∀ w : H, ∀ᵐ z ∂ξ, U w (τ z) = U (S w) z) :
    ∀ᵐ z ∂ξ, labelOrbit ξ U D S v (τ z) =
      labelShiftSecond (labelOrbit ξ U D S v z) := by
  have ha (p : ℤ × ℤ) := htime ((D ^ p.1) ((S ^ p.2) v))
  filter_upwards [ae_all_iff.mpr ha] with z hz
  funext p
  change labelOrbitLP ξ U D S v p (τ z) = labelOrbitLP ξ U D S v (p.1,p.2+1) z
  rw [labelOrbitLP_second ξ U D S v hDS]
  exact hz p

lemma labelOrbit_zero : labelOrbitLP ξ U D S v (0,0) = U v := by
  simp [labelOrbitLP]
end

section
open MeasureTheory
open scoped ENNReal
variable {Z : Type*} [MeasurableSpace Z] (ξ : Measure Z) [SigmaFinite ξ]

lemma exists_positive_memLp_two : ∃ f : Z → ℝ,
    Measurable f ∧ (∀ z, 0 < f z ∧ f z ≤ 1) ∧ Integrable f ξ ∧ MemLp f 2 ξ := by
  obtain ⟨g,hg,hm,hi⟩ := exists_pos_lintegral_lt_of_sigmaFinite ξ (by simp : (1 : ℝ≥0∞) ≠ 0)
  let f : Z → ℝ := fun z => min (g z : ℝ) 1
  have hf : Measurable f := (measurable_coe_nnreal_real.comp hm).min measurable_const
  have hpos (z) : 0 < f z := lt_min (hg z) zero_lt_one
  have hle (z) : f z ≤ 1 := min_le_right _ _
  have hgint : Integrable (fun z => (g z : ℝ)) ξ := by
    have hh := integrable_toReal_of_lintegral_ne_top (hm.coe_nnreal_ennreal.aemeasurable) (ne_top_of_lt hi)
    simpa only [ENNReal.coe_toReal] using hh
  have hfi : Integrable f ξ := hgint.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs,abs_of_pos (hpos z)]; exact min_le_left _ _))
  refine ⟨f,hf,fun z => ⟨hpos z,hle z⟩,hfi,?_⟩
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply hfi.mono' (hf.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_pos (hpos z)]
  nlinarith [hpos z,hle z]
end

namespace JoiningOperator

open Set MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

section KernelRepresentatives
variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  {ρ : Measure W} [SigmaFinite ρ] {ξ : Measure Z} [SigmaFinite ξ]
  {source target : W → Z}
  (hs : MeasurePreserving source ρ ξ) (ht : MeasurePreserving target ρ ξ)
  (K : Kernel Z Z) [IsMarkovKernel K]
  (hK : HasCondDistrib target source K ρ)

include hK in
lemma operator_integral_representative (g : Lp ℂ 2 ξ) (f : Z → ℂ)
    (hf : StronglyMeasurable f) (hfi : Integrable f ξ) (hg : (g : Z → ℂ) =ᵐ[ξ] f) :
    (operator hs ht g : Z → ℂ) =ᵐ[ξ] (fun z => ∫ y, f y ∂K z) := by
  have hσ : SigmaFinite (ρ.map source) := by rw [hs.map_eq]; infer_instance
  have hgi := hfi.congr hg.symm
  have he := operator_ae_eq_condExp_integrable hs ht g hgi
  have hx : (fun w => g (target w)) =ᵐ[ρ] (fun w => f (target w)) := ht.quasiMeasurePreserving.ae hg
  have hc := SigmaFiniteConditional.condExp_of_kernel hs.measurable hK f hf
    ((ht.integrable_comp hf.aestronglyMeasurable).mpr hfi)
  have he' := he.trans ((condExp_congr_ae hx).trans hc)
  have hd := (ae_map_iff hs.measurable.aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable (operator hs ht g)).measurable
      hf.integral_kernel.measurable)).mpr he'
  rwa [hs.map_eq] at hd

include hs ht hK in
omit [SigmaFinite ρ] in
lemma kernel_integrable (f : Z → ℝ) (hf : Measurable f) (hfi : Integrable f ξ) :
    ∀ᵐ z ∂ξ, Integrable f (K z) := by
  have hj : Integrable (fun zy : Z × Z => f zy.2) (ξ ⊗ₘ K) := by
    rw [←hs.map_eq,←hK.map_eq]
    exact (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      hK.aemeasurable).mpr ((ht.integrable_comp hf.aestronglyMeasurable).mpr hfi)
  exact hj.ae_of_compProd

include K hK in

lemma exists_positive_range_vector : ∃ v : Lp ℂ 2 ξ,
    v ∈ (operator hs ht).range ∧ ∀ᵐ z ∂ξ, 0 < (v z).re := by
  obtain ⟨f,hf,hpos,hfi,hflp⟩ := Rokhlin.exists_positive_memLp_two ξ
  have hfc : MemLp (fun z => (f z : ℂ)) 2 ξ := hflp.ofReal
  let g : Lp ℂ 2 ξ := hfc.toLp _
  refine ⟨operator hs ht g,⟨g,rfl⟩,?_⟩
  have he := operator_integral_representative hs ht K hK g (fun z => (f z : ℂ))
    (Complex.measurable_ofReal.comp hf).stronglyMeasurable hfi.ofReal hfc.coeFn_toLp
  filter_upwards [he,kernel_integrable hs ht K hK f hf hfi] with z hz hi
  rw [hz,integral_complex_ofReal]
  change 0 < ∫ y, f y ∂K z
  apply (integral_pos_iff_support_of_nonneg (fun y => (hpos y).1.le) hi).mpr
  have he : Function.support f = univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (hpos y).1
  rw [he,measure_univ]
  exact zero_lt_one
end KernelRepresentatives


variable {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  {ρ : Measure W} [SigmaFinite ρ] {ξ : Measure Z} [SigmaFinite ξ]
  {source target : W → Z}
  (hs : MeasurePreserving source ρ ξ) (ht : MeasurePreserving target ρ ξ)

omit [SigmaFinite ρ] [SigmaFinite ξ] in
lemma deterministic_on_range
    (h₁ : operator hs ht = (operator hs ht).adjoint * operator hs ht * operator hs ht)
    (v : (operator hs ht).range) :
    ∀ᵐ x ∂ρ, v.val (target x) = operator hs ht v.val (source x) := by
  let U : Lp ℂ 2 ξ →ₗᵢ[ℂ] Lp ℂ 2 ρ := Lp.compMeasurePreservingₗᵢ ℂ source hs
  let V : Lp ℂ 2 ξ →ₗᵢ[ℂ] Lp ℂ 2 ρ := Lp.compMeasurePreservingₗᵢ ℂ target ht
  have hn : ‖(U.toContinuousLinearMap.adjoint ∘L V.toContinuousLinearMap) v.val‖ = ‖v.val‖ :=
    partial_unitary_norm_on_range (operator hs ht) h₁ v.val v.property
  have he : U (operator hs ht v.val) = V v.val :=
    deterministic_transition_of_norm_eq U V v.val hn
  have h : (U (operator hs ht v.val) : W → ℂ) =ᵐ[ρ] (V v.val : W → ℂ) := Lp.ext_iff.mp he
  filter_upwards [h,Lp.coeFn_compMeasurePreserving (operator hs ht v.val) hs,
    Lp.coeFn_compMeasurePreserving v.val ht] with w hw h1 h2
  exact h2.symm.trans (hw.symm.trans h1)

lemma exists_orbit_vector
    (h₁ : operator hs ht = (operator hs ht).adjoint * operator hs ht * operator hs ht)
    (h₂ : operator hs ht = operator hs ht * operator hs ht * (operator hs ht).adjoint)
    (V : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ)
    (hV : ∀ v, V (operator hs ht v) = operator hs ht (V v))
    (τ : Z → Z) (htime : ∀ v : Lp ℂ 2 ξ, (V v : Z → ℂ) =ᵐ[ξ] fun z => v (τ z))
    (K : Kernel Z Z) [IsMarkovKernel K] (hK : HasCondDistrib target source K ρ) :
    ∃ (ψ : Z → LabelOrbitVector) (v : Lp ℂ 2 ξ),
      Measurable ψ ∧ (∀ z, ψ z (0,0) = v z) ∧
      (∀ᵐ z ∂ξ, 0 < (v z).re) ∧
      (∀ᵐ w ∂ρ, ψ (target w) = labelShiftFirst (ψ (source w))) ∧
      (∀ᵐ z ∂ξ, ψ (τ z) = labelShiftSecond (ψ z)) := by
  obtain ⟨v,hvr,hvp⟩ := exists_positive_range_vector hs ht K hK
  let vr : (operator hs ht).range := ⟨v,hvr⟩
  let U := (operator hs ht).range.subtypeₗᵢ
  let D := partialUnitary (operator hs ht) h₁ h₂
  let S := commutingRangeUnitary (operator hs ht) V hV
  have hDS : Commute D S := partialUnitary_commutingRange _ h₁ h₂ V hV
  refine ⟨labelOrbit ξ U D S vr,v,measurable_labelOrbit _ _ _ _ _,?_,hvp,?_,?_⟩
  · intro z
    exact congrArg (fun g : Lp ℂ 2 ξ => g z) (labelOrbit_zero ξ U D S vr)
  · exact labelOrbit_transition ξ U D S vr ρ source target (deterministic_on_range hs ht h₁)
  · exact labelOrbit_time ξ U D S vr hDS τ (fun w => (htime w.val).symm)
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma parameterLaw_proper (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    (M.parameterLaw (n+1)).map (planes n J) = Measure.pi (fun _ : J => M.parameterLaw n) := by
  unfold Object.parameterLaw
  rw [Measure.map_map (measurable_planes _ _) (measurable_amap M.measurable_par _)]
  have he : planes n J ∘ amap M.par (n+1) =
      (fun z : J → Arr I M.Y n => fun j => amap M.par n (z j)) ∘ planes n J := rfl
  have hg : Measurable (fun z : J → Arr I M.Y n => fun j => amap M.par n (z j)) :=
    Measurable.of_eval fun j => (measurable_amap M.measurable_par n).comp (measurable_pi_apply j)
  rw [he,←Measure.map_map hg (measurable_planes n J),M.proper n J hJ,
    Measure.pi_map_pi (fun _ => (measurable_amap M.measurable_par n).aemeasurable)]

lemma parameter_pair_preserving (hk : 3 ≤ Fintype.card I) (s t : I) (hst : s ≠ t) :
    MeasurePreserving (fun p => (tupleParameter M p s,tupleParameter M p t))
      (M.parameterLaw 1) ((M.parameterLaw 0).prod (M.parameterLaw 0)) := by
  have hJ : ({s,t} : Finset I) ≠ Finset.univ := by
    intro h
    have hcard : ({s,t} : Finset I).card = 2 := by simp [hst]
    rw [h,Finset.card_univ] at hcard
    omega
  let s' : ({s,t} : Finset I) := ⟨s,by simp⟩
  let t' : ({s,t} : Finset I) := ⟨t,by simp⟩
  have hne : s' ≠ t' := fun h => hst (congrArg Subtype.val h)
  have hi : iIndepFun (fun i : ({s,t} : Finset I) => Function.eval i)
      (Measure.pi (fun _ : ({s,t} : Finset I) => M.parameterLaw 0)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hp : MeasurePreserving (fun z : ({s,t} : Finset I) → Arr I M.U 0 => (z s',z t'))
      (Measure.pi (fun _ => M.parameterLaw 0)) ((M.parameterLaw 0).prod (M.parameterLaw 0)) := by
    refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _),?_⟩
    rw [(hi.indepFun hne).map_prod_eq_prod_map_map (measurable_pi_apply s').aemeasurable
      (measurable_pi_apply t').aemeasurable,
      (measurePreserving_eval (fun _ : ({s,t} : Finset I) => M.parameterLaw 0) s').map_eq,
      (measurePreserving_eval (fun _ : ({s,t} : Finset I) => M.parameterLaw 0) t').map_eq]
  exact hp.comp ⟨measurable_planes 0 {s,t},parameterLaw_proper M 0 {s,t} hJ⟩

variable (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma rawCounting_target_parameter_independent (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (s t : I) (hst : s ≠ t) :
    MeasurePreserving (fun z : RawLabelTuple M => (rawLabelSlot M s z,(rawLabelSlot M t z).1))
      (Eπ.measure (M.parameterLaw 1)) ((E.measure (M.parameterLaw 0)).prod (M.parameterLaw 0)) := by
  have he : ∀ᵐ p ∂M.parameterLaw 1, ∃ e :
      {q : I → HilbertCode (M.ownKernel 0) //
        (p,q) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)} ≃
      {q : HilbertCode (M.ownKernel 0) // (tupleParameter M p s,q) ∈ S},
      ∀ z, (e z).val = z.val s := by
    filter_upwards [hS] with p hp
    exact ⟨exactFibreSlotEquiv (M.ownKernel 0) Λ (tupleParameter M) hk hm hind S p s
      (hp s),fun _ => rfl⟩
  have hη : HasCondDistrib (fun p => tupleParameter M p t) (fun p => tupleParameter M p s)
      (Kernel.const (Arr I M.U 0) (M.parameterLaw 0)) (M.parameterLaw 1) := by
    refine ⟨((measurable_plane _ _ _).prodMk (measurable_plane _ _ _)).aemeasurable,?_⟩
    change (M.parameterLaw 1).map (fun p => (tupleParameter M p s,tupleParameter M p t)) =
      (M.parameterLaw 1).map (plane 0 0 s) ⊗ₘ Kernel.const _ (M.parameterLaw 0)
    rw [M.parameterLaw_consistent,Measure.compProd_const]
    exact (parameter_pair_preserving M hk s t hst).map_eq
  have hc := Eπ.observation_conditional_of_fibrewise E (M.parameterLaw 1) (M.parameterLaw 0)
    (fun p => tupleParameter M p s) ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
    (fun z => z.2 s) ((measurable_pi_apply s).comp measurable_snd) he
    (fun p => tupleParameter M p t) (measurable_plane _ _ _)
    (Kernel.const _ (M.parameterLaw 0)) hη
  refine ⟨(measurable_rawLabelSlot M s).prodMk (measurable_rawLabelSlot M t).fst,?_⟩
  have hh := hc.map_eq
  rw [(rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ s).map_eq] at hh
  change (Eπ.measure (M.parameterLaw 1)).map (fun z => (rawLabelSlot M s z,(rawLabelSlot M t z).1)) =
    E.measure (M.parameterLaw 0) ⊗ₘ Kernel.const _ (M.parameterLaw 0) at hh
  rwa [Measure.compProd_const] at hh
end ArrayObjects.Object.Rolled

namespace BorelFibreEnumeration
open MeasureTheory Set
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma ae_fibre_all (ν : Measure U) [SigmaFinite ν] {P : U × Z → Prop}
    (h : ∀ᵐ x ∂E.measure ν, P x) :
    ∀ᵐ u ∂ν, ∀ z, (u,z) ∈ S → P (u,z) := by
  rw [measure,E.measurableEmbedding_point.ae_map_iff] at h
  have hh : ∀ᵐ x ∂(ν.prod Measure.count).restrict E.indexDomain,
      P (x.1,E.section_ x.2 x.1) := by
    rw [←map_comap_subtype_coe E.measurable_indexDomain]
    exact (MeasurableEmbedding.subtype_coe E.measurable_indexDomain).ae_map_iff.mpr h
  have hprod := (ae_restrict_iff' E.measurable_indexDomain).mp hh
  have ha := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [ha] with u hu
  have hon : ∀ n : ℕ, u ∈ E.domain n → P (u,E.section_ n u) := by
    simpa only [Measure.ae_count_iff,indexDomain,Set.mem_ofPred_eq] using hu
  intro z hz
  obtain ⟨n,hn,rfl⟩ := E.cover u z hz
  exact hon n hn
end BorelFibreEnumeration

section
open MeasureTheory Set
variable {U Z C W : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace C] [MeasurableEq C]
  [MeasurableSpace W] {S : Set (U × Z)} (E : BorelFibreEnumeration S)
  (ν : Measure U) [IsProbabilityMeasure ν] (ρ : Measure W) [SigmaFinite ρ]
  (source target : W → U × Z)

omit [SigmaFinite ρ] in

lemma countable_orbit_image (ht : MeasurePreserving target ρ (E.measure ν))
    (hpp : MeasurePreserving (fun w => (source w,(target w).1)) ρ ((E.measure ν).prod ν))
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (hD : ∀ᵐ w ∂ρ, ψ (target w) = D (ψ (source w))) :
    ∃ R : Set C, R.Countable ∧ ∀ᵐ z ∂E.measure ν, ψ z ∈ R := by
  let q : U → ℕ → C := fun u n => ψ (u,E.section_ n u)
  have hq (n : ℕ) : Measurable (fun u => q u n) :=
    hψ.comp (measurable_id.prodMk (E.measurable_section n))
  have hmeas : MeasurableSet {zu : (U × Z) × U | ∃ n, D (ψ zu.1) = q zu.2 n} := by
    simp_rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_eq_fun
      (D.measurable.comp (hψ.comp measurable_fst)) ((hq n).comp measurable_snd)
  have hw : ∀ᵐ w ∂ρ, ∃ n, D (ψ (source w)) = q (target w).1 n := by
    filter_upwards [hD,ht.quasiMeasurePreserving.ae (E.ae_mem ν)] with w hw hm
    obtain ⟨n,_,hn⟩ := E.cover (target w).1 (target w).2 hm
    exact ⟨n,hw.symm.trans (congrArg ψ (Prod.ext rfl hn.symm))⟩
  have hp : ∀ᵐ zu ∂(E.measure ν).prod ν, ∃ n, D (ψ zu.1) = q zu.2 n := by
    rw [←hpp.map_eq]
    exact (ae_map_iff hpp.measurable.aemeasurable hmeas).mpr hw
  exact countable_essential_image_of_countable_fibres (E.measure ν) ν ψ hψ D q hq
    (Measure.ae_ae_of_ae_prod hp)
end

section
open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
namespace JoiningOperator
lemma partial_unitary_of_squares_aux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A B : H →L[ℂ] H)
    (hb : B = A.adjoint) (hb' : B.adjoint = A)
    (h1 : A = A.adjoint ∘L A ∘L A) (h2 : A = B.adjoint ∘L A ∘L B) :
    A = A.adjoint * A * A ∧ A = A * A * A.adjoint := by
  constructor
  · simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using h1
  · rw [hb',hb] at h2
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using h2

lemma partial_unitary_of_squares {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {μ : Measure W} {ν : Measure Z} {f g : W → Z}
    (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g μ ν)
    (h1 : operator hf hg = (operator hf hg).adjoint ∘L operator hf hg ∘L operator hf hg)
    (h2 : operator hf hg = (operator hg hf).adjoint ∘L operator hf hg ∘L operator hg hf) :
    operator hf hg = (operator hf hg).adjoint * operator hf hg * operator hf hg ∧
      operator hf hg = operator hf hg * operator hf hg * (operator hf hg).adjoint :=
  partial_unitary_of_squares_aux _ _ (operator_adjoint hf hg).symm
    (operator_adjoint hg hf) h1 h2
end JoiningOperator
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hL Eσ hst in
lemma rawCounting_partial_unitary :
    let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
    let A := JoiningOperator.operator (hq s) (hq t)
    A = A.adjoint * A * A ∧ A = A * A * A.adjoint := by
  dsimp only
  exact JoiningOperator.partial_unitary_of_squares _ _
    (rawCounting_square_operator M Λ hM hk hL hm hind S hS E Eπ Eσ s t s t hst)
    (rawCounting_square_operator M Λ hM hk hL hm hind S hS E Eπ Eσ t s s t hst)

include hM hk hL hm hind hS Eσ hst in
lemma rawCounting_exists_orbit :
    ∃ (ψ : RawLabel M → LabelOrbitVector) (v : Lp ℂ 2 (E.measure (M.parameterLaw 0))),
      Measurable ψ ∧ (∀ z, ψ z (0,0) = v z) ∧
      (∀ᵐ z ∂E.measure (M.parameterLaw 0), 0 < (v z).re) ∧
      (∀ᵐ w ∂Eπ.measure (M.parameterLaw 1), ψ (rawLabelSlot M t w) = labelShiftFirst (ψ (rawLabelSlot M s w))) ∧
      (∀ᵐ z ∂E.measure (M.parameterLaw 0), ψ (rawLabelTime M z) = labelShiftSecond (ψ z)) ∧
      (∃ R : Set LabelOrbitVector, R.Countable ∧ ∀ᵐ z ∂E.measure (M.parameterLaw 0), ψ z ∈ R) := by
  let hq := rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ
  have hτ := rawCounting_time_preserving M Λ s hL hm S hS E
  have hi := rawLabelTime_left_inverse M Λ s S hS E
  have hσ := inverse_measurePreserving (E.measure (M.parameterLaw 0)) (rawLabelTime M)
    (rawLabelTimeInv M) hτ (measurable_rawLabelTimeInv M) hi
  let V := aeLpTime _ _ _ hτ hσ hi
  have hV : ∀ v, V (JoiningOperator.operator (hq s) (hq t) v) =
      JoiningOperator.operator (hq s) (hq t) (V v) :=
    JoiningOperator.operator_commutes_time _ _ _ _ (hq s) (hq t) _ hτ _
      (rawTupleCounting_time_preserving M Λ hL hm Eπ) rfl rfl V rfl
  have hA := rawCounting_partial_unitary M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  let := rawLabelTransition_markov M Λ hk hm hind s t
  obtain ⟨ψ,v,hψ,hzero,hpos,htr,htime⟩ := JoiningOperator.exists_orbit_vector (hq s) (hq t)
    hA.1 hA.2 V hV (rawLabelTime M) (aeLpTime_coe _ _ _ hτ hσ hi)
    (rawLabelTransition M Λ s t) (rawCounting_label_transition M Λ hk hm hind S hS E Eπ s t)
  refine ⟨ψ,v,hψ,hzero,hpos,htr,htime,?_⟩
  exact countable_orbit_image E (M.parameterLaw 0) (Eπ.measure (M.parameterLaw 1))
    (rawLabelSlot M s) (rawLabelSlot M t) (hq t)
    (rawCounting_target_parameter_independent M Λ hk hm hind S hS E Eπ s t hst)
    ψ hψ labelShiftFirst htr
end ArrayObjects.Object.Rolled
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped ENNReal
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def restrictGraph (Q : Set (U × Z)) (hQ : MeasurableSet Q) : BorelFibreEnumeration (S ∩ Q) where
  domain n := {u | u ∈ E.domain n ∧ (u,E.section_ n u) ∈ Q}
  section_ := E.section_
  measurable_domain n := (E.measurable_domain n).inter ((measurable_id.prodMk (E.measurable_section n)) hQ)
  measurable_section := E.measurable_section
  mem n u hu := ⟨E.mem n u hu.1,hu.2⟩
  cover u z hz := by
    obtain ⟨n,hn,he⟩ := E.cover u z hz.1
    exact ⟨n,⟨hn,by rw [he]; exact hz.2⟩,he⟩
  unique u n m hn hm he := E.unique u n m hn.1 hm.1 he

lemma restrictGraph_mass (ν : Measure U) [SigmaFinite ν]
    (Q : Set (U × Z)) (hQ : MeasurableSet Q) :
    (E.restrictGraph Q hQ).measure ν univ = E.measure ν Q := by
  rw [←lintegral_one,←lintegral_indicator_one hQ]
  change (∫⁻ u, (1 : ℝ≥0∞) ∂(E.restrictGraph Q hQ).measure ν) =
    ∫⁻ a, Q.indicator (fun _ => (1 : ℝ≥0∞)) a ∂E.measure ν
  rw [(E.restrictGraph Q hQ).lintegral_measure ν (fun _ => 1) measurable_const,
    E.lintegral_measure ν (Q.indicator (fun _ => 1)) (measurable_const.indicator hQ)]
  apply lintegral_congr
  intro u
  apply tsum_congr
  intro n
  classical
  simp only [restrictGraph,indicator_apply,mem_ofPred]
  split_ifs <;> simp_all

lemma ae_finite_fibres (ν : Measure U) [SigmaFinite ν]
    (hν : E.measure ν univ < ∞) : ∀ᵐ u ∂ν, {z | (u,z) ∈ S}.Finite := by
  let g : U → ℝ≥0∞ := fun u => ∑' n, (E.domain n).indicator (fun _ => 1) u
  have hg : Measurable g := Measurable.tsum fun n => measurable_const.indicator (E.measurable_domain n)
  have hi : ∫⁻ u, g u ∂ν ≠ ∞ := by
    rw [←E.lintegral_measure ν (fun _ => 1) measurable_const,lintegral_one]
    exact hν.ne
  filter_upwards [ae_lt_top hg hi] with u hu
  have he : g u = Measure.count {n : ℕ | u ∈ E.domain n} := by
    rw [←lintegral_indicator_one (Set.to_countable _).measurableSet,lintegral_count]
    rfl
  rw [he,Measure.count_apply_lt_top] at hu
  have hr : {z | (u,z) ∈ S} = (fun n => E.section_ n u) '' {n | u ∈ E.domain n} := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn,he⟩ := E.cover u z hz
      exact ⟨n,hn,he⟩
    · rintro ⟨n,hn,rfl⟩
      exact E.mem n u hn
  rw [hr]
  exact hu.image _

lemma ae_finite_level (ν : Measure U) [SigmaFinite ν]
    (Q : Set (U × Z)) (hQ : MeasurableSet Q) (hν : E.measure ν Q < ∞) :
    ∀ᵐ u ∂ν, {z | (u,z) ∈ S ∧ (u,z) ∈ Q}.Finite := by
  apply (E.restrictGraph Q hQ).ae_finite_fibres ν
  rw [E.restrictGraph_mass ν Q hQ]
  exact hν
end BorelFibreEnumeration

section
open MeasureTheory Set
open scoped ENNReal
variable {Z C W : Type*} [MeasurableSpace Z] [MeasurableSpace C]
  [MeasurableSingletonClass C] [MeasurableSpace W]
  (ξ : Measure Z) (ψ : Z → C)

def positiveLevels : Set C := {b | ξ {z | ψ z = b} ≠ 0}

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma positiveLevels_countable (S : Set C) (hSc : S.Countable)
    (hS : ∀ᵐ z ∂ξ, ψ z ∈ S) : (positiveLevels ξ ψ).Countable := by
  apply hSc.mono
  intro b hb
  by_contra hbS
  have he : ∀ᵐ z ∂ξ, ψ z ≠ b := hS.mono fun z hz he => hbS (he ▸ hz)
  have hz : ξ {z | ψ z = b} = 0 := by simpa only [ae_iff,not_not] using he
  exact hb hz

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma ae_mem_positiveLevels (S : Set C) (hSc : S.Countable)
    (hS : ∀ᵐ z ∂ξ, ψ z ∈ S) : ∀ᵐ z ∂ξ, ψ z ∈ positiveLevels ξ ψ := by
  let : Countable S := hSc.to_subtype
  have h (b : S) : ∀ᵐ z ∂ξ, ψ z = b.val → b.val ∈ positiveLevels ξ ψ := by
    by_cases hb : ξ {z | ψ z = b.val} = 0
    · have he : ∀ᵐ z ∂ξ, ψ z ≠ b.val := by simpa only [ae_iff,not_not] using hb
      exact he.mono fun _ hz he => False.elim (hz he)
    · exact Filter.Eventually.of_forall fun _ _ => hb
  filter_upwards [hS,ae_all_iff.mpr h] with z hz hb
  exact hb ⟨ψ z,hz⟩ rfl

omit [MeasurableSingletonClass C] in
lemma joining_transport_invariant (hψ : Measurable ψ) (ρ : Measure W)
    (source target : W → Z) (hs : MeasurePreserving source ρ ξ)
    (ht : MeasurePreserving target ρ ξ) (D : C ≃ᵐ C)
    (hD : (ψ ∘ target) =ᵐ[ρ] (D ∘ ψ ∘ source)) :
    MeasurePreserving D (ξ.map ψ) (ξ.map ψ) := by
  refine ⟨D.measurable,?_⟩
  rw [←hs.map_eq,Measure.map_map hψ hs.measurable,
    Measure.map_map D.measurable (hψ.comp hs.measurable),←Measure.map_congr hD,
    ←Measure.map_map hψ ht.measurable,ht.map_eq]
  rw [←Measure.map_map hψ hs.measurable,hs.map_eq]

lemma positiveLevel_mass_transport (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (hD : MeasurePreserving D (ξ.map ψ) (ξ.map ψ)) (b : C) :
    ξ {z | ψ z = D b} = ξ {z | ψ z = b} := by
  have h := hD.measure_preimage (measurableSet_singleton (D b)).nullMeasurableSet
  have he : D ⁻¹' ({D b} : Set C) = {b} := by ext c; simp
  rw [he,Measure.map_apply hψ (measurableSet_singleton b),
    Measure.map_apply hψ (measurableSet_singleton (D b))] at h
  exact h.symm

def positiveLevelsEquiv (hψ : Measurable ψ) (D : C ≃ᵐ C)
    (hD : MeasurePreserving D (ξ.map ψ) (ξ.map ψ)) :
    positiveLevels ξ ψ ≃ positiveLevels ξ ψ where
  toFun b := ⟨D b,by
    change ξ {z | ψ z = D b.val} ≠ 0
    rw [positiveLevel_mass_transport ξ ψ hψ D hD]
    exact b.property⟩
  invFun b := ⟨D.symm b,by
    have h := positiveLevel_mass_transport ξ ψ hψ D hD (D.symm b)
    rw [D.apply_symm_apply] at h
    change ξ {z | ψ z = D.symm b.val} ≠ 0
    rw [←h]
    exact b.property⟩
  left_inv b := Subtype.ext (D.symm_apply_apply b)
  right_inv b := Subtype.ext (D.apply_symm_apply b)

omit [MeasurableSpace C] [MeasurableSingletonClass C] in

lemma finite_positive_level_mass (v : Lp ℂ 2 ξ) (c : C → ℂ)
    (hcoord : ∀ᵐ z ∂ξ, c (ψ z) = v z) (hpos : ∀ᵐ z ∂ξ, v z ≠ 0)
    (b : positiveLevels ξ ψ) : ξ {z | ψ z = b.val} < ∞ := by
  have hb : c b.val ≠ 0 := by
    intro hb
    have he : ∀ᵐ z ∂ξ, ψ z ≠ b.val := by
      filter_upwards [hcoord,hpos] with z hz hp he
      exact hp (hz.symm.trans ((congrArg c he).trans hb))
    exact b.property (by simpa only [ae_iff,not_not] using he)
  have hi : Integrable (fun z => ‖v z‖ ^ 2) ξ := (Lp.memLp v).integrable_norm_pow (by decide : 2 ≠ 0)
  have hbound := hi.measure_ge_lt_top (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb))
  apply lt_of_le_of_lt _ hbound
  apply measure_mono_ae
  filter_upwards [hcoord] with z hz hzb
  change ‖c b.val‖ ^ 2 ≤ ‖v z‖ ^ 2
  rw [←hz,hzb]
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : Set (RawLabel M))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S})
    (E : BorelFibreEnumeration S)
    (Eπ : BorelFibreEnumeration (exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)))
    (Eσ : BorelFibreEnumeration (rawExactSquare M Λ)) (s t : I) (hst : s ≠ t)

include hM hk hL hm hind hS Eπ Eσ hst in
lemma exists_raw_finite_levels :
    ∃ ψ : RawLabel M → LabelOrbitVector,
      Measurable ψ ∧
      (positiveLevels (E.measure (M.parameterLaw 0)) ψ).Countable ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
        ψ (u,q) ∈ positiveLevels (E.measure (M.parameterLaw 0)) ψ) ∧
      (∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        E.measure (M.parameterLaw 0) {z | ψ z = b.val} < ∞) ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ b : positiveLevels (E.measure (M.parameterLaw 0)) ψ,
        {q | (u,q) ∈ S ∧ ψ (u,q) = b.val}.Finite) ∧
      MeasurePreserving labelShiftFirst ((E.measure (M.parameterLaw 0)).map ψ)
        ((E.measure (M.parameterLaw 0)).map ψ) ∧
      MeasurePreserving labelShiftSecond ((E.measure (M.parameterLaw 0)).map ψ)
        ((E.measure (M.parameterLaw 0)).map ψ) ∧
      (∀ᵐ p ∂M.parameterLaw 1, ∀ a, (p,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
        ψ (tupleParameter M p t,a t) = labelShiftFirst (ψ (tupleParameter M p s,a s))) ∧
      (∀ᵐ u ∂M.parameterLaw 0, ∀ q, (u,q) ∈ S →
        ψ (rawLabelTime M (u,q)) = labelShiftSecond (ψ (u,q))) := by
  obtain ⟨ψ,v,hψ,hzero,hpos,htr,htime,R,hRc,hR⟩ :=
    rawCounting_exists_orbit M Λ hM hk hL hm hind S hS E Eπ Eσ s t hst
  have hBc := positiveLevels_countable (E.measure (M.parameterLaw 0)) ψ R hRc hR
  let : Countable (positiveLevels (E.measure (M.parameterLaw 0)) ψ) := hBc.to_subtype
  have hb (b : positiveLevels (E.measure (M.parameterLaw 0)) ψ) :
      E.measure (M.parameterLaw 0) {z | ψ z = b.val} < ∞ := by
    apply finite_positive_level_mass _ ψ v (fun c => c (0,0))
      (Filter.Eventually.of_forall hzero) _ b
    filter_upwards [hpos] with z hz
    intro he
    rw [he,Complex.zero_re] at hz
    exact lt_irrefl _ hz
  refine ⟨ψ,hψ,hBc,E.ae_fibre_all _ (ae_mem_positiveLevels _ ψ R hRc hR),hb,?_,?_,?_,
    Eπ.ae_fibre_all _ htr,E.ae_fibre_all _ htime⟩
  · apply ae_all_iff.mpr
    intro b
    exact E.ae_finite_level _ {z | ψ z = b.val} (measurableSet_eq_fun hψ measurable_const) (hb b)
  · exact joining_transport_invariant _ ψ hψ _ (rawLabelSlot M s) (rawLabelSlot M t)
      (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ s)
      (rawCounting_coordinate_preserving M Λ hk hm hind S hS E Eπ t) labelShiftFirst htr
  · exact joining_transport_invariant _ ψ hψ _ id (rawLabelTime M) (MeasurePreserving.id _)
      (rawCounting_time_preserving M Λ s hL hm S hS E) labelShiftSecond htime
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
