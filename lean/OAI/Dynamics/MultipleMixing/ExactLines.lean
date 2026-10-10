import OAI.Dynamics.MultipleMixing.Tensors

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped ENNReal
variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma closure_image_dense_span (A : E →L[ℂ] F) (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => A (v j)))).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (fun j => A (v j)))).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨v j,rfl⟩
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x,rfl⟩
      have hc : IsClosed (S.comap A.toLinearMap : Set E) :=
        (Submodule.isClosed_topologicalClosure _).preimage A.continuous
      have hs : Submodule.span ℂ (Set.range v) ≤ S.comap A.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j,rfl⟩)
      have hh : ⊤ ≤ S.comap A.toLinearMap := by
        rw [←hv]
        exact Submodule.topologicalClosure_minimal _ hs hc
      exact hh (show x ∈ (⊤ : Submodule ℂ E) from trivial)
    · exact Submodule.isClosed_topologicalClosure _

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {ν : Measure X} {x : Ω → X}

lemma pullback_dense_span (hx : MeasurePreserving x μ ν) (v : J → Lp ℂ 2 ν)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => JoiningOperator.pull hx (v j)))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  rw [closure_image_dense_span _ _ hv, JoiningOperator.pull_range]
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  exact (isClosed_aestronglyMeasurable hx.measurable.comap_le).submodule_topologicalClosure_eq

local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

lemma torusWord_pullback_dense {I : Type*} [Countable I] [IsFiniteMeasure μ]
    (γ : Ω → I → Circle) (hγ : Measurable γ) :
    (Submodule.span ℂ (Set.range (fun w => JoiningOperator.pull (MeasurePreserving.mk hγ rfl)
      (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord (I := I) w))))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap γ inferInstance) 2 μ := by
  exact pullback_dense_span (MeasurePreserving.mk hγ rfl) _ (torusWord_L2_dense (μ.map γ))

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal

section
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω Z X Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [IsFiniteMeasure ν] [IsFiniteMeasure ρ] [IsFiniteMeasure η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma torusWord_contraction
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (a : X → I → Circle) (b : Y → I → Circle) (c : Z → I → Circle)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ᵐ ω ∂μ, c (z ω) = a (x ω) * (b (y ω))⁻¹)
    (w : FreeGroup I) :
    pull (MeasurePreserving.mk hc rfl) (ContinuousMap.toLp 2 (η.map c) ℂ (torusWord w)) =
      contraction hz hxy
        (pull (MeasurePreserving.mk ha rfl) (ContinuousMap.toLp 2 (ν.map a) ℂ (torusWord w)))
        (star (pull (MeasurePreserving.mk hb rfl) (ContinuousMap.toLp 2 (ρ.map b) ℂ (torusWord w)))) := by
  let f := ContinuousMap.toLp 2 (η.map c) ℂ (torusWord w)
  let g := ContinuousMap.toLp 2 (ν.map a) ℂ (torusWord w)
  let h := ContinuousMap.toLp 2 (ρ.map b) ℂ (torusWord w)
  let hc' : MeasurePreserving c η (η.map c) := ⟨hc,rfl⟩
  let ha' : MeasurePreserving a ν (ν.map a) := ⟨ha,rfl⟩
  let hb' : MeasurePreserving b ρ (ρ.map b) := ⟨hb,rfl⟩
  have he : pull hz (pull hc' f) = pull hxy (tensorLp (pull ha' g) (star (pull hb' h))) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (pull hc' f) hz,
      hz.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hc'),
      (hc'.comp hz).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (η.map c) (𝕜 := ℂ) (p := 2) (torusWord w)),
      Lp.coeFn_compMeasurePreserving (tensorLp (pull ha' g) (star (pull hb' h))) hxy,
      hxy.quasiMeasurePreserving.ae (coe_tensorLp (pull ha' g) (star (pull hb' h))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_compMeasurePreserving g ha')),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_star (pull hb' h))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_compMeasurePreserving h hb')),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae
        (ha'.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (ν.map a) (𝕜 := ℂ) (p := 2) (torusWord w)))),
      hxy.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae
        (hb'.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (ρ.map b) (𝕜 := ℂ) (p := 2) (torusWord w)))),
      hr] with ω hf1 hf2 hf3 ht1 ht2 hg1 hh1 hh2 hg2 hh3 hrω
    calc
      _ = torusWord w (c (z ω)) := hf1.trans (hf2.trans hf3)
      _ = torusWord w (a (x ω)) * star (torusWord w (b (y ω))) := by rw [hrω,torusWord_ratio]
      _ = (pull ha' g) (x ω) * star ((pull hb' h) (y ω)) := by
        rw [show (pull ha' g) (x ω) = torusWord w (a (x ω)) from hg1.trans hg2,
          show (pull hb' h) (y ω) = torusWord w (b (y ω)) from hh2.trans hh3]
      _ = _ := (ht1.trans (ht2.trans (congrArg (_ * ·) hh1))).symm
  have hh := congrArg (fun q => (pull hz).adjoint q) he
  have hid := congrArg (fun A : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 η => A (pull hc' f)) (pull_adjoint_pull hz)
  change (pull hz).adjoint (pull hz (pull hc' f)) = pull hc' f at hid
  rw [hid] at hh
  exact hh

end

local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω Z X Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [retained8 : IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] [IsFiniteMeasure η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

include retained8 in
lemma ratio_field_le_active
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (a : X → I → Circle) (b : Y → I → Circle) (c : Z → I → Circle)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ᵐ ω ∂μ, c (z ω) = a (x ω) * (b (y ω))⁻¹) :
    lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η ≤
      (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure := by
  let _ := retained8
  erw [←torusWord_pullback_dense (μ := η) c hc]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  exact ⟨_, (torusWord_contraction hz hxy a b c ha hb hc hr w).symm⟩

end JoiningOperator

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
lemma ae_kernel_joint {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace V] {μ : Measure Ω} [SFinite μ] {z : Ω → Z} {v : Ω → V}
    {κ : Kernel Z V} [IsSFiniteKernel κ] (h : HasCondDistrib v z κ μ) {p : Z × V → Prop}
    (hp : MeasurableSet {q | p q}) (hv : ∀ᵐ ω ∂μ, p (z ω,v ω)) :
    ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p (a,b) := by
  apply Measure.ae_ae_of_ae_compProd
  rw [←h.map_eq]
  exact (ae_map_iff h.aemeasurable hp).mpr hv
end ConditionalFibres

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_torus_completeness (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∃ (J : Type u) (_ : Countable J)
        (A : (cols.P → rows.A → Arr I M.Y n) → J → Circle)
        (B : (cols.P → rows.B → Arr I M.Y n) → J → Circle)
        (P : (cols.A → rows.P → Arr I M.Y n) → J → Circle)
        (Q : (cols.B → rows.P → Arr I M.Y n) → J → Circle)
        (H : (cols.P → rows.P → Arr I M.Y n) → J → Circle),
        Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
        commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e =
          lpMeas ℂ ℂ (MeasurableSpace.comap H inferInstance) 2 (cellLaw M rows.P cols.P n e) ∧
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          H (cells M rows.P cols.P n y) = A (cells M rows.A cols.P n y) *
            (B (cells M rows.B cols.P n y))⁻¹) ∧
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          H (cells M rows.P cols.P n y) = P (cells M rows.P cols.A n y) *
            (Q (cells M rows.P cols.B n y))⁻¹) := by
  filter_upwards [grouped_polar_data M hM rows cols n,
    grouped_haar_normalization M hM rows cols n,
    grouped_polar_a_field M hM rows cols n,grouped_polar_b_field M hM rows cols n,
    pairPair_fixed_conditional M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP n,
    rowPair_fixed_conditional M rows.P cols.P cols.A cols.B n,
    columnPair_fixed_marginals M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP
      rows.properA rows.properB rows.disjointPA rows.disjointPB rows.properPA rows.properPB n,
    rowPair_fixed_marginals M hM rows.P cols.P cols.A cols.B rows.properP
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.P cols.P rows.properP n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.A rows.B cols.P cols.P rows.disjointAB rows.properAB n,
    cells_indep_columns_fibre M rows.P rows.P cols.A cols.B cols.disjointAB cols.properAB n,
    columnActive_eq_range M hM rows cols.P cols.properP n,
    rowActive_eq_range M hM rows.P rows.properP cols n,
    grouped_column_contraction_projection M hM rows cols n]
      with e hRd hHaar haField hbField hpair hκ hξ hκm hξm hz hx hy hc hd hxy hcd hcol hrow hproj
  obtain ⟨R⟩ := hRd
  obtain ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,hfa,hfb,hra,hrb⟩ :=
    R.torus_coordinates (hHaar R)
      ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e)
      ((rowPairKernel M rows.P cols.P cols.A cols.B n).sectR e) hκ hξ hpair
      (hκm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩)
      (hξm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩)
  let : Countable J := hJ
  let : Group (J → Circle) := (inferInstance : CommGroup (J → Circle)).toGroup
  let : MeasurableMul₂ (J → Circle) := inferInstance
  have haF := haField R
  have hbF := hbField R
  rw [hfa] at haF
  rw [hfb] at hbF
  let hXY : MeasurePreserving (fun y => (cells M rows.A cols.P n y,cells M rows.B cols.P n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.P n e).prod (cellLaw M rows.B cols.P n e)) :=
    ⟨hx.measurable.prodMk hy.measurable, by
      rw [←hx.map_eq,←hy.map_eq]
      exact hxy.map_prod_eq_prod_map_map hx.measurable.aemeasurable hy.measurable.aemeasurable⟩
  let hPQ : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e)) :=
    ⟨hc.measurable.prodMk hd.measurable, by
      rw [←hc.map_eq,←hd.map_eq]
      exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable⟩
  let α := ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e).map (Prod.map A B)
  let : IsMarkovKernel α := Kernel.IsMarkovKernel.map _ (hA.prodMap hB)
  have hα : HasCondDistrib (fun y => (A (cells M rows.A cols.P n y),B (cells M rows.B cols.P n y)))
      (cells M rows.P cols.P n) α (M.ownKernel (n+2) e) := hκ.comp_left (hA.prodMap hB)
  let σ := (cellLaw M rows.B cols.P n e).map B
  let : IsProbabilityMeasure σ := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hB.aemeasurable
  have hm : ∀ᵐ v ∂cellLaw M rows.P cols.P n e, (α v).map Prod.snd = σ := by
    rw [hz.map_eq] at hκm
    filter_upwards [hκm] with v hv
    dsimp only [α,σ]
    exact (kernel_map_pair_snd ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e) v hA hB).trans
      (congrArg (fun m => m.map B) hv.2.map_eq)
  have hr : ∀ᵐ v ∂cellLaw M rows.P cols.P n e, ∀ᵐ w ∂α v, w.1*w.2⁻¹ = H v := by
    rw [←hz.map_eq]
    exact ConditionalFibres.ae_kernel_joint hα
      (measurableSet_eq_fun (Measurable.of_eval fun j =>
        ((measurable_pi_apply j).comp measurable_snd.fst).mul
          (((measurable_pi_apply j).comp measurable_snd.snd).inv))
        (hH.comp measurable_fst)) (hra.mono fun _ h => h.symm)
  refine ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,le_antisymm ?_ ?_,hra,hrb⟩
  · apply JoiningOperator.common_space_le_ratio (G := J → Circle) (gG := inferInstance) (mG := inferInstance) (hG := inferInstance) (a := A) (b := B) (c := H)
      hz hXY hA hB hH hα σ hm hr _
      (commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection
      (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection
    · rw [←hcol hz hXY]
      exact inf_le_right
    · exact hproj hz hXY
    · intro g
      exact haF (Submodule.starProjection_apply_mem _ g)
    · intro h
      exact hbF (Submodule.starProjection_apply_mem _ h)
  · apply le_inf
    · rw [hrow hz hPQ]
      exact JoiningOperator.ratio_field_le_active hz hPQ P Q H hP hQ hH hrb
    · rw [hcol hz hXY]
      exact JoiningOperator.ratio_field_le_active hz hXY A B H hA hB hH hra
end ArrayObjects.Object.Rolled

section
variable {I Ω Y : Type*} [MeasurableSpace Y]

lemma field_finset_observation (f : I → Ω → Y) (s : Finset I) :
    MeasurableSpace.comap (fun ω (i : s) => f i ω) inferInstance =
      ⨆ i ∈ s, MeasurableSpace.comap (f i) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  simp only [iSup_subtype]

lemma field_pair_finset_union [DecidableEq I] (f : I → Ω → Y) (s t : Finset I) :
    MeasurableSpace.comap (fun ω => ((fun (i : s) => f i ω),(fun (i : t) => f i ω))) inferInstance =
      MeasurableSpace.comap (fun ω (i : ↥(s ∪ t)) => f i ω) inferInstance := by
  change ((inferInstance : MeasurableSpace (s → Y)).prod (inferInstance : MeasurableSpace (t → Y))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,field_finset_observation,field_finset_observation,field_finset_observation]
  simp only [Finset.mem_union,iSup_or]
  rw [iSup_sup_eq]

lemma field_finset_grid {J : Type*} (f : I → J → Ω → Y) (s : Finset I) (t : Finset J) :
    MeasurableSpace.comap (fun ω (i : s) (j : t) => f i j ω) inferInstance =
      ⨆ i ∈ s, ⨆ j ∈ t, MeasurableSpace.comap (f i j) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  simp_rw [MeasurableSpace.comap_process_pi]
  simp only [iSup_subtype]

lemma field_grid_pair_inner_union {J : Type*} [DecidableEq J]
    (f : I → J → Ω → Y) (r : Finset I) (s t : Finset J) :
    MeasurableSpace.comap (fun ω => ((fun (i : r) (j : s) => f i j ω),
      (fun (i : r) (j : t) => f i j ω))) inferInstance =
      MeasurableSpace.comap (fun ω (i : r) (j : ↥(s ∪ t)) => f i j ω) inferInstance := by
  change ((inferInstance : MeasurableSpace (r → s → Y)).prod (inferInstance : MeasurableSpace (r → t → Y))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,field_finset_grid,field_finset_grid,field_finset_grid]
  simp only [Finset.mem_union,iSup_or]
  simp only [iSup_sup_eq]
end

section
variable {I : Type*} [Fintype I] [DecidableEq I]

@[ext] structure ComplementSplit (P : Finset I) where
  A : Finset I
  B : Finset I
  nonemptyP : P.Nonempty
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  disjointPA : Disjoint P A
  disjointPB : Disjoint P B
  disjointAB : Disjoint A B
  cover : P ∪ A ∪ B = Finset.univ

namespace ComplementSplit
variable {P : Finset I}
abbrev partition (s : ComplementSplit P) : TriplePartition I :=
  ⟨P,s.A,s.B,s.nonemptyP,s.nonemptyA,s.nonemptyB,s.disjointPA,s.disjointPB,s.disjointAB,s.cover⟩

instance : Finite (ComplementSplit P) :=
  Finite.of_injective (fun s : ComplementSplit P => (s.A,s.B)) (by
    intro s t h
    exact ComplementSplit.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma union_eq (s : ComplementSplit P) : s.A ∪ s.B = Pᶜ := by
  ext i
  constructor
  · intro hi
    refine Finset.mem_compl.mpr (fun hip => ?_)
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.disjoint_left.mp s.disjointPA hip h
    · exact Finset.disjoint_left.mp s.disjointPB hip h
  · intro hi
    have hp : i ∉ P := Finset.mem_compl.mp hi
    have hu : i ∈ P ∪ s.A ∪ s.B := s.cover ▸ Finset.mem_univ i
    simpa only [Finset.mem_union,hp,false_or] using hu

def singleton (P : Finset I) (hP : P.Nonempty) (s : I) (hs : s ∉ P)
    (hb : (P ∪ {s})ᶜ.Nonempty) : ComplementSplit P where
  A := {s}
  B := (P ∪ {s})ᶜ
  nonemptyP := hP
  nonemptyA := Finset.singleton_nonempty s
  nonemptyB := hb
  disjointPA := Finset.disjoint_singleton_right.mpr hs
  disjointPB := Finset.disjoint_left.mpr (by
    intro i hi hh
    exact Finset.mem_compl.mp hh (Finset.mem_union_left _ hi))
  disjointAB := Finset.disjoint_left.mpr (by
    intro i hi hh
    exact Finset.mem_compl.mp hh (Finset.mem_union_right _ hi))
  cover := Finset.union_compl _

end ComplementSplit
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma cells_pair_preserving {A B S D : Finset I} {n : ℕ} {e : Arr I M.U (n+2)}
    (ha : MeasurePreserving (cells M A S n) (M.ownKernel (n+2) e) (cellLaw M A S n e))
    (hb : MeasurePreserving (cells M B D n) (M.ownKernel (n+2) e) (cellLaw M B D n e))
    (hi : IndepFun (cells M A S n) (cells M B D n) (M.ownKernel (n+2) e)) :
    MeasurePreserving (fun y => (cells M A S n y,cells M B D n y))
      (M.ownKernel (n+2) e) ((cellLaw M A S n e).prod (cellLaw M B D n e)) := by
  refine ⟨ha.measurable.prodMk hb.measurable,?_⟩
  rw [←ha.map_eq,←hb.map_eq]
  exact hi.map_prod_eq_prod_map_map ha.measurable.aemeasurable hb.measurable.aemeasurable

lemma rowActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (hP : P ≠ Finset.univ) (s t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      rowActive M P R s.A s.B n e = rowActive M P R t.A t.B n e := by
  filter_upwards [rowActive_eq_range M hM P hP s.partition n,
    rowActive_eq_range M hM P hP t.partition n,
    cells_fibre_marginal M hM P R hP n,
    cells_fibre_marginal M hM P s.A hP n,cells_fibre_marginal M hM P s.B hP n,
    cells_fibre_marginal M hM P t.A hP n,cells_fibre_marginal M hM P t.B hP n,
    cells_indep_columns_fibre M P P s.A s.B s.disjointAB s.partition.properAB n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
      with e hs ht hz hsa hsb hta htb his hit
  let hS := cells_pair_preserving M hsa hsb his
  let hT := cells_pair_preserving M hta htb hit
  rw [hs hz hS,ht hz hT]
  apply JoiningOperator.active_observation_eq hz hS hT
  change MeasurableSpace.comap (fun y => ((fun (j : s.A) (a : P) => missingRow M n j a y),
    (fun (j : s.B) (a : P) => missingRow M n j a y))) inferInstance =
    MeasurableSpace.comap (fun y => ((fun (j : t.A) (a : P) => missingRow M n j a y),
    (fun (j : t.B) (a : P) => missingRow M n j a y))) inferInstance
  rw [field_pair_finset_union (fun j y (a : P) => missingRow M n j a y) s.A s.B,
    field_pair_finset_union (fun j y (a : P) => missingRow M n j a y) t.A t.B,s.union_eq,t.union_eq]

lemma columnActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (hR : R ≠ Finset.univ) (s t : ComplementSplit P) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      columnActive M P s.A s.B R n e = columnActive M P t.A t.B R n e := by
  filter_upwards [columnActive_eq_range M hM s.partition R hR n,
    columnActive_eq_range M hM t.partition R hR n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM s.A R s.partition.properA n,
    cells_fibre_marginal M hM s.B R s.partition.properB n,
    cells_fibre_marginal M hM t.A R t.partition.properA n,
    cells_fibre_marginal M hM t.B R t.partition.properB n,
    cells_indep_rows_fibre M hM s.A s.B R R s.disjointAB s.partition.properAB n,
    cells_indep_rows_fibre M hM t.A t.B R R t.disjointAB t.partition.properAB n]
      with e hs ht hz hsa hsb hta htb his hit
  let hS := cells_pair_preserving M hsa hsb his
  let hT := cells_pair_preserving M hta htb hit
  rw [hs hz hS,ht hz hT]
  apply JoiningOperator.active_observation_eq hz hS hT
  change MeasurableSpace.comap (fun y => ((fun (j : R) (a : s.A) => missingRow M n j a y),
    (fun (j : R) (a : s.B) => missingRow M n j a y))) inferInstance =
    MeasurableSpace.comap (fun y => ((fun (j : R) (a : t.A) => missingRow M n j a y),
    (fun (j : R) (a : t.B) => missingRow M n j a y))) inferInstance
  rw [field_grid_pair_inner_union,field_grid_pair_inner_union,s.union_eq,t.union_eq]

lemma commonActive_complement_invariant (hM : M.IsSaturated) (P R : Finset I)
    (s s' : ComplementSplit P) (t t' : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M P s.A s.B R t.A t.B n e = commonActive M P s'.A s'.B R t'.A t'.B n e := by
  filter_upwards [rowActive_complement_invariant M hM P R s.partition.properP t t' n,
    columnActive_complement_invariant M hM P R t.partition.properP s s' n] with e hr hc
  exact congrArg₂ (· ⊓ ·) hr hc
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma ternary_unit_const_of_nonzero_mean
    (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ) (hz : AEMeasurable z μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (hne : (∫ ω, (f (z ω) : ℂ) ∂μ) ≠ 0) :
    ∃ a : Circle, ∀ᵐ ω ∂μ, f (z ω) = a := by
  let F := fun ω => (f (z ω) : ℂ)
  let G := fun ω => (g (x ω) : ℂ)
  let H := fun ω => (h (y ω) : ℂ)
  have hf' : Measurable (fun q => (f q : ℂ)) := measurable_subtype_coe.comp hf
  have hg' : Measurable (fun q => (g q : ℂ)) := measurable_subtype_coe.comp hg
  have hh' : Measurable (fun q => (h q : ℂ)) := measurable_subtype_coe.comp hh
  have hfm : AEStronglyMeasurable F μ := (hf'.comp_aemeasurable hz).aestronglyMeasurable
  have hgm : AEStronglyMeasurable G μ := (hg'.comp_aemeasurable hx).aestronglyMeasurable
  have hhm : AEStronglyMeasurable H μ := (hh'.comp_aemeasurable hy).aestronglyMeasurable
  have heF : F =ᵐ[μ] fun ω => G ω * H ω := he.mono fun ω hω => congrArg ((↑) : Circle → ℂ) hω
  have heG : G =ᵐ[μ] fun ω => F ω * conj (H ω) := by
    filter_upwards [heF] with ω hω
    rw [hω, mul_assoc,←Complex.inv_eq_conj (Circle.norm_coe _),mul_inv_cancel₀ (Circle.coe_ne_zero _),mul_one]
  have heH : H =ᵐ[μ] fun ω => F ω * conj (G ω) := by
    filter_upwards [heF] with ω hω
    rw [hω,mul_comm (G ω),mul_assoc,←Complex.inv_eq_conj (Circle.norm_coe _),mul_inv_cancel₀ (Circle.coe_ne_zero _),mul_one]
  have ha : ‖∫ ω, F ω ∂μ‖ = ‖∫ ω, G ω ∂μ‖ * ‖∫ ω, H ω ∂μ‖ := by
    rw [integral_congr_ae heF,show (∫ ω, G ω * H ω ∂μ) = (∫ ω, G ω ∂μ) * (∫ ω, H ω ∂μ) from (hxy.comp hg' hh').integral_fun_mul_eq_mul_integral hgm hhm,norm_mul]
  have hb : ‖∫ ω, G ω ∂μ‖ = ‖∫ ω, F ω ∂μ‖ * ‖∫ ω, H ω ∂μ‖ := by
    rw [integral_congr_ae heG,show (∫ ω, F ω * conj (H ω) ∂μ) = (∫ ω, F ω ∂μ) * (∫ ω, conj (H ω) ∂μ) from (hyz.symm.comp hf' (Complex.continuous_conj.measurable.comp hh')).integral_fun_mul_eq_mul_integral hfm hhm.star,
      integral_conj,norm_mul,Complex.norm_conj]
  have hc : ‖∫ ω, H ω ∂μ‖ = ‖∫ ω, F ω ∂μ‖ * ‖∫ ω, G ω ∂μ‖ := by
    rw [integral_congr_ae heH,show (∫ ω, F ω * conj (G ω) ∂μ) = (∫ ω, F ω ∂μ) * (∫ ω, conj (G ω) ∂μ) from (hxz.symm.comp hf' (Complex.continuous_conj.measurable.comp hg')).integral_fun_mul_eq_mul_integral hfm hgm.star,
      integral_conj,norm_mul,Complex.norm_conj]
  have hA : 0 < ‖∫ ω, F ω ∂μ‖ := norm_pos_iff.mpr hne
  have hB : 0 ≤ ‖∫ ω, G ω ∂μ‖ := norm_nonneg _
  have hC : 0 ≤ ‖∫ ω, H ω ∂μ‖ := norm_nonneg _
  have hBpos : 0 < ‖∫ ω, G ω ∂μ‖ := by nlinarith [ha]
  have hCone : ‖∫ ω, H ω ∂μ‖ = 1 := by nlinarith [ha,hb]
  have hBone : ‖∫ ω, G ω ∂μ‖ = 1 := by nlinarith [ha,hc,hCone]
  have hAone : ‖∫ ω, F ω ∂μ‖ = 1 := by rw [ha,hBone,hCone,mul_one]
  let a : Circle := ⟨∫ ω, F ω ∂μ, by exact mem_sphere_zero_iff_norm.mpr hAone⟩
  have hconst := ae_eq_mean_of_norm_mean_eq_one F
    (Filter.Eventually.of_forall fun ω => Circle.norm_coe _) hAone
  exact ⟨a,hconst.mono fun _ ht => Circle.ext ht⟩

lemma ternary_line_dichotomy
    (f f' : Z → Circle) (g g' : X → Circle) (h h' : Y → Circle)
    (hf : Measurable f) (hf' : Measurable f')
    (hg : Measurable g) (hg' : Measurable g') (hh : Measurable h) (hh' : Measurable h')
    (hx : AEMeasurable x μ) (hy : AEMeasurable y μ) (hz : AEMeasurable z μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (he' : ∀ᵐ ω ∂μ, f' (z ω) = g' (x ω) * h' (y ω)) :
    (∫ ω, (f (z ω) : ℂ) * conj (f' (z ω) : ℂ) ∂μ) = 0 ∨
      ∃ a : Circle, ∀ᵐ ω ∂μ, f (z ω) = a * f' (z ω) := by
  by_cases hn : (∫ ω, (f (z ω) : ℂ) * conj (f' (z ω) : ℂ) ∂μ) = 0
  · exact Or.inl hn
  right
  have hp : ∀ᵐ ω ∂μ, f (z ω)*(f' (z ω))⁻¹ =
      (g (x ω)*(g' (x ω))⁻¹) * (h (y ω)*(h' (y ω))⁻¹) := by
    filter_upwards [he,he'] with ω hω hω'
    rw [hω,hω',mul_inv_rev]
    ac_rfl
  obtain ⟨a,ha⟩ := ternary_unit_const_of_nonzero_mean
    (fun q => f q*(f' q)⁻¹) (fun q => g q*(g' q)⁻¹) (fun q => h q*(h' q)⁻¹)
    (hf.mul hf'.inv) (hg.mul hg'.inv) (hh.mul hh'.inv) hx hy hz hxy hxz hyz hp
    (by simpa only [Circle.coe_mul,Circle.coe_inv_eq_conj] using hn)
  exact ⟨a,ha.mono fun _ he => mul_inv_eq_iff_eq_mul.mp he⟩
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
  (x : Ω → X) (y : Ω → Y) (z : Ω → Z)

def splitExact : Set (Lp ℂ 2 η) := {v | ∃ (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (_ : Measurable g) (_ : Measurable h) (c : ℂ),
    v = c • circleLp η f hf ∧ ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω)}

lemma zero_mem_splitExact : (0 : Lp ℂ 2 η) ∈ splitExact μ η x y z := by
  exact ⟨1,1,1,measurable_const,measurable_const,measurable_const,0,by simp,
    Filter.Eventually.of_forall fun _ => (one_mul (1 : Circle)).symm⟩

lemma smul_mem_splitExact (c : ℂ) {v : Lp ℂ 2 η} (hv : v ∈ splitExact μ η x y z) :
    c • v ∈ splitExact μ η x y z := by
  obtain ⟨f,g,h,hf,hg,hh,d,hv,he⟩ := hv
  exact ⟨f,g,h,hf,hg,hh,c*d,by rw [hv,mul_smul],he⟩

lemma circle_mem_splitExact (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω)) :
    circleLp η f hf ∈ splitExact μ η x y z :=
  ⟨f,g,h,hf,hg,hh,1,(one_smul _ _).symm,he⟩

variable {μ η x y z}

lemma circleLp_dichotomy [IsProbabilityMeasure μ]
    (hz : MeasurePreserving z μ η) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    (f f' : Z → Circle) (g g' : X → Circle) (h h' : Y → Circle)
    (hf : Measurable f) (hf' : Measurable f')
    (hg : Measurable g) (hg' : Measurable g') (hh : Measurable h) (hh' : Measurable h')
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω))
    (he' : ∀ᵐ ω ∂μ, f' (z ω) = g' (x ω) * h' (y ω)) :
    inner ℂ (circleLp η f hf) (circleLp η f' hf') = 0 ∨
      ∃ a : Circle, circleLp η f hf = (a : ℂ) • circleLp η f' hf' := by
  rcases ternary_line_dichotomy f f' g g' h h' hf hf' hg hg' hh hh' hx hy hz.measurable.aemeasurable
    hxy hxz hyz he he' with ho | ⟨a,ha⟩
  · left
    apply inner_eq_zero_symm.mp
    rw [circleLp_inner]
    have hi : (∫ v, conj (f' v : ℂ) * (f v : ℂ) ∂η) =
        ∫ ω, conj (f' (z ω) : ℂ) * (f (z ω) : ℂ) ∂μ :=
      by
        rw [←hz.map_eq]
        exact integral_map hz.measurable.aemeasurable (by fun_prop)
    rw [hi]
    simpa only [mul_comm] using ho
  · right
    have ha' : f =ᵐ[η] fun v => a*f' v := by
      rw [←hz.map_eq]
      exact (ae_map_iff hz.measurable.aemeasurable
        (measurableSet_eq_fun hf (measurable_const.mul hf'))).mpr ha
    exact ⟨a,(circleLp_congr η hf (measurable_const.mul hf') ha').trans (circleLp_phase η a f' hf')⟩

lemma splitExact_dichotomy [IsProbabilityMeasure μ]
    (hz : MeasurePreserving z μ η) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxy : IndepFun x y μ) (hxz : IndepFun x z μ) (hyz : IndepFun y z μ)
    {v w : Lp ℂ 2 η} (hv : v ∈ splitExact μ η x y z) (hw : w ∈ splitExact μ η x y z) :
    inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w := by
  obtain ⟨f,g,h,hf,hg,hh,c,rfl,he⟩ := hv
  obtain ⟨f',g',h',hf',hg',hh',d,rfl,he'⟩ := hw
  rcases circleLp_dichotomy hz hx hy hxy hxz hyz f f' g g' h h' hf hf' hg hg' hh hh' he he'
    with ho | ⟨a,ha⟩
  · left
    simp only [inner_smul_left,inner_smul_right,ho,mul_zero]
  · by_cases hd : d = 0
    · left
      simp only [hd,zero_smul,inner_zero_right]
    · right
      refine ⟨c*(a : ℂ)*d⁻¹,?_⟩
      rw [ha,smul_smul,smul_smul,mul_assoc,mul_assoc,inv_mul_cancel₀ hd,mul_one]

lemma circleLp_contraction {ν : Measure X} {ρ : Measure Y}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (f : Z → Circle) (g : X → Circle) (h : Y → Circle)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (he : ∀ᵐ ω ∂μ, f (z ω) = g (x ω)*h (y ω)) :
    circleLp η f hf = contraction hz hxy (circleLp ν g hg) (circleLp ρ h hh) := by
  have hx := (measurePreserving_fst (μ := ν) (ν := ρ)).comp hxy
  have hy := (measurePreserving_snd (μ := ν) (ν := ρ)).comp hxy
  have hp : pull hz (circleLp η f hf) = pull hxy (tensorLp (circleLp ν g hg) (circleLp ρ h hh)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp η f hf) hz,
      hz.quasiMeasurePreserving.ae (circleLp_coe η f hf),
      Lp.coeFn_compMeasurePreserving (tensorLp (circleLp ν g hg) (circleLp ρ h hh)) hxy,
      hxy.quasiMeasurePreserving.ae (coe_tensorLp (circleLp ν g hg) (circleLp ρ h hh)),
      hx.quasiMeasurePreserving.ae (circleLp_coe ν g hg),
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ h hh),he] with ω h1 h2 h3 h4 h5 h6 h7
    calc
      _ = (f (z ω) : ℂ) := h1.trans h2
      _ = (g (x ω) : ℂ)*(h (y ω) : ℂ) := congrArg ((↑) : Circle → ℂ) h7
      _ = _ := (h3.trans (h4.trans (congrArg₂ (·*·) h5 h6))).symm
  have hid := congrArg (fun A : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 η => A (circleLp η f hf)) (pull_adjoint_pull hz)
  exact hid.symm.trans (congrArg (fun q => (pull hz).adjoint q) hp)

lemma splitExact_le_active {ν : Measure X} {ρ : Measure Y}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ)) :
    splitExact μ η x y z ⊆ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure := by
  rintro v ⟨f,g,h,hf,hg,hh,c,rfl,he⟩
  exact (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure.smul_mem c
    (Submodule.le_topologicalClosure _ ⟨_,(circleLp_contraction hz hxy f g h hf hg hh he).symm⟩)
end JoiningOperator

section
open MeasureTheory
open scoped ENNReal
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (γ : Ω → J → Circle) (hγ : Measurable γ)

lemma torus_circle_pull (w : FreeGroup J) :
    circleLp μ (fun x => torusWordCircle w (γ x)) ((torusWordCircle w).continuous.measurable.comp hγ) =
      JoiningOperator.pull (MeasurePreserving.mk hγ rfl)
        (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord w)) := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => torusWordCircle w (γ x)) ((torusWordCircle w).continuous.measurable.comp hγ),
    Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 (μ.map γ) ℂ (torusWord w)) (MeasurePreserving.mk hγ rfl),
    (MeasurePreserving.mk hγ rfl).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (μ.map γ) (𝕜 := ℂ) (p := 2) (torusWord w))]
      with x h1 h2 h3
  exact h1.trans (h2.trans h3).symm

lemma torus_circle_dense :
    (Submodule.span ℂ (Set.range (fun w => circleLp μ (fun x => torusWordCircle w (γ x))
      ((torusWordCircle w).continuous.measurable.comp hγ)))).topologicalClosure =
      lpMeas ℂ ℂ (MeasurableSpace.comap γ inferInstance) 2 μ := by
  simp_rw [torus_circle_pull μ γ hγ]
  exact torusWord_pullback_dense γ hγ
end

namespace JoiningOperator
open MeasureTheory
open scoped ENNReal
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y P Q J : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Q]
    [Countable J] (μ : Measure Ω) (η : Measure Z) [IsFiniteMeasure η]
    (x : Ω → X) (y : Ω → Y) (p : Ω → P) (q : Ω → Q) (z : Ω → Z)

lemma torus_exact_split (A : X → J → Circle) (B : Y → J → Circle) (H : Z → J → Circle)
    (hA : Measurable A) (hB : Measurable B) (hH : Measurable H)
    (he : ∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) (w : FreeGroup J) :
    circleLp η (fun v => torusWordCircle w (H v)) ((torusWordCircle w).continuous.measurable.comp hH) ∈
      splitExact μ η x y z := by
  apply circle_mem_splitExact μ η x y z _ (fun v => torusWordCircle w (A v))
    (fun v => (torusWordCircle w (B v))⁻¹) _
    ((torusWordCircle w).continuous.measurable.comp hA)
    (((torusWordCircle w).continuous.measurable.comp hB).inv)
  filter_upwards [he] with ω hω
  rw [hω,torusWordCircle_mul,torusWordCircle_inv]

lemma torus_split_inter_span
    (A : X → J → Circle) (B : Y → J → Circle)
    (C : P → J → Circle) (D : Q → J → Circle) (H : Z → J → Circle)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) (hH : Measurable H)
    (he : ∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹)
    (hf : ∀ᵐ ω ∂μ, H (z ω) = C (p ω) * (D (q ω))⁻¹)
    (V : Submodule ℂ (Lp ℂ 2 η)) (hV : IsClosed (V : Set (Lp ℂ 2 η)))
    (hsub : splitExact μ η x y z ∩ splitExact μ η p q z ⊆ V)
    (hfield : V = lpMeas ℂ ℂ (MeasurableSpace.comap H inferInstance) 2 η) :
    (Submodule.span ℂ (splitExact μ η x y z ∩ splitExact μ η p q z)).topologicalClosure = V := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hsub) hV
  · rw [hfield,←torus_circle_dense η H hH]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_mono
    rintro v ⟨w,rfl⟩
    exact ⟨torus_exact_split μ η x y z A B H hA hB hH he w,
      torus_exact_split μ η p q z C D H hC hD hH hf w⟩
end JoiningOperator

section
open scoped InnerProductSpace
variable {H A B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma nonzero_inner_in_closedSpan (S : Set H) (v : H) (hv : v ≠ 0)
    (hmem : v ∈ (Submodule.span ℂ S).topologicalClosure) :
    ∃ w ∈ S, inner ℂ v w ≠ 0 := by
  by_contra! h
  have ho : v ∈ (Submodule.span ℂ S)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
    | smul c x hx ih => simp only [inner_smul_right,ih,mul_zero]
  have ht : v ∈ ((Submodule.span ℂ S).topologicalClosure)ᗮ := by
    simpa only [Submodule.orthogonal_closure] using ho
  exact hv (inner_self_eq_zero.mp (((Submodule.mem_orthogonal' _ v).mp ht) v hmem))

theorem common_exact_all_splits
    (P : A → Set H) (Q : B → Set H) (D : Submodule ℂ H)
    (hP0 : ∀ a, (0 : H) ∈ P a) (hQ0 : ∀ b, (0 : H) ∈ Q b)
    (hPs : ∀ a (c : ℂ) v, v ∈ P a → c • v ∈ P a)
    (hQs : ∀ b (c : ℂ) v, v ∈ Q b → c • v ∈ Q b)
    (hPo : ∀ a v, v ∈ P a → ∀ w, w ∈ P a → inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w)
    (hQo : ∀ b v, v ∈ Q b → ∀ w, w ∈ Q b → inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w)
    (hspan : ∀ a b, (Submodule.span ℂ (P a ∩ Q b)).topologicalClosure = D)
    (a₀ : A) (b₀ : B) :
    (Submodule.span ℂ {v | (∀ a, v ∈ P a) ∧ (∀ b, v ∈ Q b)}).topologicalClosure = D := by
  apply le_antisymm
  · rw [←hspan a₀ b₀]
    exact Submodule.topologicalClosure_mono (Submodule.span_mono (fun v hv => ⟨hv.1 a₀,hv.2 b₀⟩))
  · rw [←hspan a₀ b₀]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_mono
    rintro v ⟨hp,hq⟩
    by_cases hz : v = 0
    · subst v
      exact ⟨hP0,hQ0⟩
    have hv : v ∈ D := by
      rw [←hspan a₀ b₀]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨hp,hq⟩)
    constructor
    · intro a
      obtain ⟨w,hw,hn⟩ := nonzero_inner_in_closedSpan (P a ∩ Q b₀) v hz (by rwa [hspan])
      obtain ⟨c,hc⟩ := (hQo b₀ v hq w hw.2).resolve_left hn
      rw [hc]
      exact hPs a c w hw.1
    · intro b
      obtain ⟨w,hw,hn⟩ := nonzero_inner_in_closedSpan (P a₀ ∩ Q b) v hz (by rwa [hspan])
      obtain ⟨c,hc⟩ := (hPo a₀ v hp w hw.1).resolve_left hn
      rw [hc]
      exact hQs b c w hw.2
end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowSplitExact (P R : Finset I) (s : ComplementSplit R) (n : ℕ) (e : Arr I M.U (n+2)) :=
  JoiningOperator.splitExact (M.ownKernel (n+2) e) (cellLaw M P R n e)
    (cells M P s.A n) (cells M P s.B n) (cells M P R n)
def columnSplitExact (P R : Finset I) (s : ComplementSplit P) (n : ℕ) (e : Arr I M.U (n+2)) :=
  JoiningOperator.splitExact (M.ownKernel (n+2) e) (cellLaw M P R n e)
    (cells M s.A R n) (cells M s.B R n) (cells M P R n)

lemma grouped_exact_split_span (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (Submodule.span ℂ (rowSplitExact M P R t n e ∩ columnSplitExact M P R s n e)).topologicalClosure =
        commonActive M P s.A s.B R t.A t.B n e := by
  filter_upwards [grouped_torus_completeness M hM s.partition t.partition n,
    rowActive_eq_range M hM P s.partition.properP t.partition n,
    columnActive_eq_range M hM s.partition R t.partition.properP n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM P t.A s.partition.properP n,
    cells_fibre_marginal M hM P t.B s.partition.properP n,
    cells_fibre_marginal M hM s.A R s.partition.properA n,
    cells_fibre_marginal M hM s.B R s.partition.properB n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n,
    cells_indep_rows_fibre M hM s.A s.B R R s.disjointAB s.partition.properAB n]
      with e he hr hc hz hpa hpb hap hbp hri hci
  obtain ⟨J,hJ,A,B,C,D,H,hA,hB,hC,hD,hH,hF,hAB,hCD⟩ := he
  let : Countable J := hJ
  let hrow := cells_pair_preserving M hpa hpb hri
  let hcol := cells_pair_preserving M hap hbp hci
  apply JoiningOperator.torus_split_inter_span _ _ _ _ _ _ _ C D A B H hC hD hA hB hH hCD hAB _ _ _ hF
  · exact IsClosed.inter (essentialRange.isClosed (cellLaw M P t.A n e) (fibreRowEdge M P t.A R t.B n e))
      (essentialRange.isClosed (cellLaw M s.A R n e) (fibreColumnEdge M s.A P s.B R n e))
  · rintro v ⟨hv,hw⟩
    constructor
    · rw [hr hz hrow]
      exact JoiningOperator.splitExact_le_active hz hrow hv
    · rw [hc hz hcol]
      exact JoiningOperator.splitExact_le_active hz hcol hw

lemma rowSplitExact_dichotomy (hM : M.IsSaturated) (P R : Finset I) (hP : P ≠ Finset.univ)
    (s : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ v ∈ rowSplitExact M P R s n e, ∀ w ∈ rowSplitExact M P R s n e,
        inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w := by
  filter_upwards [cells_fibre_marginal M hM P R hP n,
    cells_indep_columns_fibre M P P s.A s.B s.disjointAB s.partition.properAB n,
    cells_indep_columns_fibre M P P s.A R s.disjointPA.symm
      (by simpa only [Finset.union_comm] using s.partition.properPA) n,
    cells_indep_columns_fibre M P P s.B R s.disjointPB.symm
      (by simpa only [Finset.union_comm] using s.partition.properPB) n] with e hz hxy hxz hyz
  exact fun v hv w hw => JoiningOperator.splitExact_dichotomy hz
    (measurable_cells M P s.A n).aemeasurable (measurable_cells M P s.B n).aemeasurable hxy hxz hyz hv hw

lemma columnSplitExact_dichotomy (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ v ∈ columnSplitExact M P R s n e, ∀ w ∈ columnSplitExact M P R s n e,
        inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w := by
  filter_upwards [cells_fibre_marginal M hM P R s.partition.properP n,
    cells_indep_rows_fibre M hM s.A s.B R R s.disjointAB s.partition.properAB n,
    cells_indep_rows_fibre M hM s.A P R R s.disjointPA.symm
      (by simpa only [Finset.union_comm] using s.partition.properPA) n,
    cells_indep_rows_fibre M hM s.B P R R s.disjointPB.symm
      (by simpa only [Finset.union_comm] using s.partition.properPB) n] with e hz hxy hxz hyz
  exact fun v hv w hw => JoiningOperator.splitExact_dichotomy hz
    (measurable_cells M s.A R n).aemeasurable (measurable_cells M s.B R n).aemeasurable hxy hxz hyz hv hw

def allSplitExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  {v | (∀ s : ComplementSplit R, v ∈ rowSplitExact M P R s n e) ∧
    (∀ t : ComplementSplit P, v ∈ columnSplitExact M P R t n e)}

lemma allSplitExact_span (hM : M.IsSaturated) (P R : Finset I)
    (s₀ : ComplementSplit P) (t₀ : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (Submodule.span ℂ (allSplitExact M P R n e)).topologicalClosure =
        commonActive M P s₀.A s₀.B R t₀.A t₀.B n e := by
  have hspan := (ae_all_iff.mpr fun s : ComplementSplit P =>
    ae_all_iff.mpr fun t : ComplementSplit R => grouped_exact_split_span M hM P R s t n)
  have hinv := (ae_all_iff.mpr fun s : ComplementSplit P =>
    ae_all_iff.mpr fun t : ComplementSplit R => commonActive_complement_invariant M hM P R s s₀ t t₀ n)
  have hrow := ae_all_iff.mpr fun t : ComplementSplit R => rowSplitExact_dichotomy M hM P R s₀.partition.properP t n
  have hcol := ae_all_iff.mpr fun s : ComplementSplit P => columnSplitExact_dichotomy M hM P R s n
  filter_upwards [hspan,hinv,hrow,hcol] with e hs hi hr hc
  apply common_exact_all_splits (rowSplitExact M P R · n e) (columnSplitExact M P R · n e) _
    (fun _ => JoiningOperator.zero_mem_splitExact _ _ _ _ _)
    (fun _ => JoiningOperator.zero_mem_splitExact _ _ _ _ _)
    (fun _ c v hv => JoiningOperator.smul_mem_splitExact _ _ _ _ _ c hv)
    (fun _ c v hv => JoiningOperator.smul_mem_splitExact _ _ _ _ _ c hv)
    hr hc (fun t s => (hs s t).trans (hi s t)) t₀ s₀

def oneColumn (P : Finset I) (n : ℕ) (j : I) (y : Arr I M.Y (n+2)) : P → Arr I M.Y n :=
  fun i => missingRow M n j i y

def oneRow (R : Finset I) (n : ℕ) (i : I) (y : Arr I M.Y (n+2)) : R → Arr I M.Y n :=
  fun j => missingRow M n j i y

omit [DecidableEq I] in
@[fun_prop] lemma measurable_oneColumn (P : Finset I) (n : ℕ) (j : I) : Measurable (oneColumn M P n j) := by
  exact Measurable.of_eval fun _ => measurable_missingRow M _ _ _
omit [DecidableEq I] in
@[fun_prop] lemma measurable_oneRow (R : Finset I) (n : ℕ) (i : I) : Measurable (oneRow M R n i) := by
  exact Measurable.of_eval fun _ => measurable_missingRow M _ _ _

def columnCellLaw (P : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (j : I) : Measure (P → Arr I M.Y n) :=
  (M.ownKernel (n+1) (plane (n+1) (Fin.last (n+1)) j e)).map (fun y (i : P) => plane n 0 i y)
def rowCellLaw (R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (i : I) : Measure (R → Arr I M.Y n) :=
  (M.ownKernel (n+1) (plane (n+1) 0 i e)).map (fun y (j : R) => plane n (Fin.last n) j y)

instance (P : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (j : I) : IsProbabilityMeasure (columnCellLaw M P n e j) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (by fun_prop)
instance (R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) (i : I) : IsProbabilityMeasure (rowCellLaw M R n e i) :=
  (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (by fun_prop)

omit [DecidableEq I] in
lemma proper_columns_product (P S : Finset I) (hS : S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (fun y (j : S) => oneColumn M P n j y) (M.ownKernel (n+2) e)
        (Measure.pi (fun j : S => columnCellLaw M P n e j)) := by
  have hp := ConditionalFibres.marginal (measurable_planes (n+1) S)
    (M.ownKernel_conditional (n+2)) (M.planes_conditional (n+1) S hS)
  filter_upwards [hp] with e he
  have hg := measurePreserving_pi
    (fun j : S => M.ownKernel (n+1) (plane (n+1) (Fin.last (n+1)) j e))
    (fun j : S => columnCellLaw M P n e j)
    (f := fun _ y (i : P) => plane n 0 i y)
    (fun _ => MeasurePreserving.mk (by fun_prop) rfl)
  have hm := hg.comp he
  convert hm using 1
  funext y j i
  exact (congrFun (plane_first_last M n i j) y).symm

lemma proper_rows_product (hM : M.IsSaturated) (R A : Finset I) (hA : A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (fun y (i : A) => oneRow M R n i y) (M.ownKernel (n+2) e)
        (Measure.pi (fun i : A => rowCellLaw M R n e i)) := by
  have hp := ConditionalFibres.marginal (measurable_parents M A (n+1))
    (M.ownKernel_conditional (n+2)) (rows_conditional M hM A hA n)
  filter_upwards [hp] with e he
  have hg := measurePreserving_pi
    (fun i : A => M.ownKernel (n+1) (plane (n+1) 0 i e))
    (fun i : A => rowCellLaw M R n e i)
    (f := fun _ y (j : R) => plane n (Fin.last n) j y)
    (fun _ => MeasurePreserving.mk (by fun_prop) rfl)
  exact hg.comp he
end ArrayObjects.Object.Rolled

namespace ComplementSplit
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Finset I}

lemma two_le_card_compl (s : ComplementSplit R) : 2 ≤ Rᶜ.card := by
  have h := s.partition.cardP
  change R.card + 2 ≤ Fintype.card I at h
  have hc := Finset.card_compl R
  omega

lemma rest_nonempty (s : ComplementSplit R) (i : ↥(Rᶜ)) : (R ∪ {(i : I)})ᶜ.Nonempty := by
  obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne (by have := two_le_card_compl s; omega : 1 < Rᶜ.card) (i : I)
  refine ⟨j,?_⟩
  simp only [Finset.mem_compl,Finset.mem_union,Finset.mem_singleton,not_or] at *
  exact ⟨hj,hji⟩

abbrev singletonFor (s : ComplementSplit R) (i : ↥(Rᶜ)) : ComplementSplit R :=
  ComplementSplit.singleton R s.nonemptyP i (Finset.mem_compl.mp i.property) (rest_nonempty s i)

def restIndex (i : ↥(Rᶜ)) (j : ↥((R ∪ {(i : I)})ᶜ)) : {j : ↥(Rᶜ) // j ≠ i} :=
  ⟨⟨j,Finset.mem_compl.mpr (fun hj => Finset.mem_compl.mp j.property (Finset.mem_union_left _ hj))⟩,
    by
      intro h
      have he : (j : I) = i := congrArg Subtype.val h
      exact Finset.mem_compl.mp j.property (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))⟩

end ComplementSplit

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I A B : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
  (μ : I → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

def hybrid (s : Finset I) (x : I → A × A) : I → A :=
  fun i => if i ∈ s then (x i).1 else (x i).2

lemma measurePreserving_hybrid (s : Finset I) :
    MeasurePreserving (hybrid s) (Measure.pi (fun i => (μ i).prod (μ i))) (Measure.pi μ) := by
  exact measurePreserving_pi (fun i => (μ i).prod (μ i)) μ (f := fun i p => if i ∈ s then p.1 else p.2) (by
  intro i
  by_cases hi : i ∈ s
  · simpa only [hybrid,hi,ite_true] using
      (measurePreserving_fst (μ := μ i) (ν := μ i))
  · simpa only [hybrid,hi,ite_false] using
      (measurePreserving_snd (μ := μ i) (ν := μ i)))

lemma ae_eq_const_of_omit (f : (I → A) → B)
    (g : ∀ i, (({j : I // j ≠ i}) → A) → B)
    (h : ∀ i, ∀ᵐ x ∂Measure.pi μ, f x = g i (fun j => x j)) :
    ∃ b, ∀ᵐ x ∂Measure.pi μ, f x = b := by
  have hh (s : Finset I) : ∀ᵐ x ∂Measure.pi (fun i => (μ i).prod (μ i)),
      f (hybrid s x) = f (hybrid ∅ x) := by
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall fun _ => rfl
    | @insert i s hi hs =>
      filter_upwards [(measurePreserving_hybrid μ (insert i s)).quasiMeasurePreserving.ae (h i),
        (measurePreserving_hybrid μ s).quasiMeasurePreserving.ae (h i),hs] with x h1 h2 h3
      rw [h1,←h3,h2]
      congr 1
      funext j
      simp only [hybrid,Finset.mem_insert, j.property, false_or]
  have he : ∀ᵐ x ∂(Measure.pi μ).prod (Measure.pi μ), f x.1 = f x.2 := by
    have hp := (measurePreserving_arrowProdEquivProdArrow A A I μ μ).symm
        (MeasurableEquiv.arrowProdEquivProdArrow A A I)
    filter_upwards [hp.quasiMeasurePreserving.ae (hh Finset.univ)] with x hx
    change f (fun i => if i ∈ Finset.univ then x.1 i else x.2 i) =
      f (fun i => if i ∈ (∅ : Finset I) then x.1 i else x.2 i) at hx
    simpa only [Finset.mem_univ,ite_true,Finset.notMem_empty,ite_false] using hx
  obtain ⟨x,hx⟩ := (Measure.ae_ae_of_ae_prod he).exists
  exact ⟨f x,hx.mono fun _ he => he.symm⟩

lemma pure_product_of_singleton_splits {G : Type*} [CommGroup G]
    (f : (I → A) → G) (a : I → A → G)
    (b : ∀ i, (({j : I // j ≠ i}) → A) → G)
    (h : ∀ i, ∀ᵐ x ∂Measure.pi μ, f x = a i (x i) * b i (fun j => x j)) :
    ∃ c, ∀ᵐ x ∂Measure.pi μ, f x = c * ∏ i, a i (x i) := by
  let F (x : I → A) := f x * (∏ i, a i (x i))⁻¹
  let B (i : I) (x : ({j : I // j ≠ i}) → A) :=
    b i x * (∏ j : ({j : I // j ≠ i}), a j (x j))⁻¹
  have hi : ∀ i, ∀ᵐ x ∂Measure.pi μ, F x = B i (fun j => x j) := by
    intro i
    filter_upwards [h i] with x hx
    dsimp only [F,B]
    rw [hx,←Finset.prod_erase_mul Finset.univ (fun j => a j (x j)) (Finset.mem_univ i)]
    have hp : (∏ j : ({j : I // j ≠ i}), a j (x j)) =
        ∏ j ∈ Finset.univ.erase i, a j (x j) := by
      classical
      exact (Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i)
        (fun j => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
        (fun j => a j (x j))).symm
    rw [hp]
    simp only [mul_inv_rev]
    simp only [mul_assoc, mul_left_comm, mul_inv_cancel_left]
  obtain ⟨c,hc⟩ := ae_eq_const_of_omit μ F B hi
  refine ⟨c,hc.mono fun x hx => ?_⟩
  exact (mul_inv_eq_iff_eq_mul.mp hx)
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω Z X Y : Type*} [MeasurableSpace Ω] [retained9 : MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {η : Measure Z} [IsProbabilityMeasure η]
    {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma circle_split_witness (hz : MeasurePreserving z μ η) (f : Z → Circle) (hf : Measurable f)
    (hv : circleLp η f hf ∈ JoiningOperator.splitExact μ η x y z) :
    ∃ (g : X → Circle) (h : Y → Circle), Measurable g ∧ Measurable h ∧
      ∀ᵐ ω ∂μ, f (z ω) = g (x ω) * h (y ω) := by
  obtain ⟨f',g,h,hf',hg,hh,c,hv,he⟩ := hv
  have hn : ‖c‖ = 1 := by
    have hh := congrArg norm hv
    simpa only [circleLp_norm,norm_smul,mul_one] using hh.symm
  let a : Circle := ⟨c,mem_sphere_zero_iff_norm.mpr hn⟩
  have hfg : ∀ᵐ v ∂η, f v = a*f' v := by
    filter_upwards [circleLp_coe η f hf,circleLp_coe η f' hf',Lp.coeFn_smul c (circleLp η f' hf')] with v h1 h2 h3
    apply Subtype.ext
    change (f v : ℂ) = c * (f' v : ℂ)
    rw [←h1,hv,h3]
    change c * circleLp η f' hf' v = c * (f' v : ℂ)
    rw [h2]
  refine ⟨fun u => a*g u,h,measurable_const.mul hg,hh,?_⟩
  filter_upwards [hz.quasiMeasurePreserving.ae hfg,he] with ω h1 h2
  rw [h1,h2,mul_assoc]

variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace A]
    (ν : I → Measure A) [∀ i, IsProbabilityMeasure (ν i)]

include retained9 in
lemma full_product_of_exact_splits (u : Ω → I → A)
    (hu : MeasurePreserving u μ (Measure.pi ν)) (f : Z → Circle)
    (a : I → A → Circle) (b : ∀ i, ({j : I // j ≠ i} → A) → Circle)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (he : ∀ i, ∀ᵐ ω ∂μ, f (z ω) = a i (u ω i) * b i (fun j => u ω j)) :
    ∃ c : Circle, ∀ᵐ ω ∂μ, f (z ω) = c * ∏ i, a i (u ω i) := by
  let _ := retained9
  let i₀ : I := Classical.choice inferInstance
  let F (v : I → A) := a i₀ (v i₀) * b i₀ (fun j => v j)
  have hF : Measurable F := (ha i₀ |>.comp (measurable_pi_apply i₀)).mul
    (hb i₀ |>.comp (Measurable.of_eval (fun _ => measurable_pi_apply _)))
  have hs : ∀ i, ∀ᵐ v ∂Measure.pi ν, F v = a i (v i) * b i (fun j => v j) := by
    intro i
    rw [←hu.map_eq]
    apply (ae_map_iff hu.measurable.aemeasurable (measurableSet_eq_fun hF
      ((ha i |>.comp (measurable_pi_apply i)).mul
        (hb i |>.comp (Measurable.of_eval (fun _ => measurable_pi_apply _)))))).mpr
    filter_upwards [he i₀,he i] with ω h0 hi
    exact h0.symm.trans hi
  obtain ⟨c,hc⟩ := pure_product_of_singleton_splits ν F a b hs
  refine ⟨c,?_⟩
  filter_upwards [he i₀,hu.quasiMeasurePreserving.ae hc] with ω h0 hc
  exact h0.trans hc
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma complement_proper {P : Finset I} (hP : P.Nonempty) : Pᶜ ≠ Finset.univ := by
  obtain ⟨i,hi⟩ := hP
  intro h
  have := Finset.mem_compl.mp (h.symm ▸ Finset.mem_univ i)
  exact this hi

lemma row_all_splits_product (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f),
        (∀ t' : ComplementSplit R, circleLp (cellLaw M P R n e) f hf ∈ rowSplitExact M P R t' n e) →
        ∃ (a : ↥(Rᶜ) → (P → Arr I M.Y n) → Circle) (c : Circle),
          (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
            f (cells M P R n y) = c * ∏ i : ↥(Rᶜ), a i (oneColumn M P n i y) := by
  let : Nonempty ↥(Rᶜ) := Finset.Nonempty.to_subtype (by
    have := t.two_le_card_compl
    exact Finset.card_pos.mp (by omega))
  filter_upwards [cells_fibre_marginal M hM P R s.partition.properP n,
    proper_columns_product M P Rᶜ (complement_proper t.nonemptyP) n] with e hz hp
  intro f hf h
  have hw (i : ↥(Rᶜ)) := circle_split_witness hz f hf (h (t.singletonFor i))
  choose g b hg hb he using hw
  let a (i : ↥(Rᶜ)) (v : P → Arr I M.Y n) : Circle := g i (fun _ p => v p)
  let d (i : ↥(Rᶜ)) (v : {j : ↥(Rᶜ) // j ≠ i} → (P → Arr I M.Y n)) : Circle :=
    b i (fun j p => v (ComplementSplit.restIndex i j) p)
  have ha : ∀ i, Measurable (a i) := by intro i; exact (hg i).comp (by fun_prop)
  have hd : ∀ i, Measurable (d i) := by intro i; exact (hb i).comp (by fun_prop)
  have he' (i : ↥(Rᶜ)) : ∀ᵐ y ∂M.ownKernel (n+2) e,
      f (cells M P R n y) = a i (oneColumn M P n i y) * d i (fun j => oneColumn M P n j.val y) := by
    filter_upwards [he i] with y hy
    convert hy using 2
    · dsimp only [a]
      apply congrArg (g i)
      funext j p
      have hj : (j : I) = i := Finset.mem_singleton.mp j.property
      simp only [cells,oneColumn,hj]
    · rfl
  obtain ⟨c,hc⟩ := full_product_of_exact_splits (fun i : ↥(Rᶜ) => columnCellLaw M P n e i)
    (fun y (j : ↥(Rᶜ)) => oneColumn M P n j y) hp f a d ha hd he'
  exact ⟨a,c,ha,hc⟩

lemma column_all_splits_product (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (_t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f),
        (∀ s' : ComplementSplit P, circleLp (cellLaw M P R n e) f hf ∈ columnSplitExact M P R s' n e) →
        ∃ (a : ↥(Pᶜ) → (R → Arr I M.Y n) → Circle) (c : Circle),
          (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
            f (cells M P R n y) = c * ∏ i : ↥(Pᶜ), a i (oneRow M R n i y) := by
  let : Nonempty ↥(Pᶜ) := Finset.Nonempty.to_subtype (by
    have := s.two_le_card_compl
    exact Finset.card_pos.mp (by omega))
  filter_upwards [cells_fibre_marginal M hM P R s.partition.properP n,
    proper_rows_product M hM R Pᶜ (complement_proper s.nonemptyP) n] with e hz hp
  intro f hf h
  have hw (i : ↥(Pᶜ)) := circle_split_witness hz f hf (h (s.singletonFor i))
  choose g b hg hb he using hw
  let a (i : ↥(Pᶜ)) (v : R → Arr I M.Y n) : Circle := g i (fun j _ => v j)
  let d (i : ↥(Pᶜ)) (v : {j : ↥(Pᶜ) // j ≠ i} → (R → Arr I M.Y n)) : Circle :=
    b i (fun p j => v (ComplementSplit.restIndex i j) p)
  have ha : ∀ i, Measurable (a i) := by intro i; exact (hg i).comp (by fun_prop)
  have hd : ∀ i, Measurable (d i) := by intro i; exact (hb i).comp (by fun_prop)
  have he' (i : ↥(Pᶜ)) : ∀ᵐ y ∂M.ownKernel (n+2) e,
      f (cells M P R n y) = a i (oneRow M R n i y) * d i (fun j => oneRow M R n j.val y) := by
    filter_upwards [he i] with y hy
    convert hy using 2
    · dsimp only [a]
      apply congrArg (g i)
      funext p j
      have hj : (j : I) = i := Finset.mem_singleton.mp j.property
      simp only [cells,oneRow,hj]
    · rfl
  obtain ⟨c,hc⟩ := full_product_of_exact_splits (fun i : ↥(Pᶜ) => rowCellLaw M R n e i)
    (fun y (j : ↥(Pᶜ)) => oneRow M R n j y) hp f a d ha hd he'
  exact ⟨a,c,ha,hc⟩
end

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def fullExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) : Set (Lp ℂ 2 (cellLaw M P R n e)) :=
  {v | ∃ (f : (R → P → Arr I M.Y n) → Circle) (hf : Measurable f) (d : ℂ),
    v = d • circleLp (cellLaw M P R n e) f hf ∧
    (∃ (a : ↥(Rᶜ) → (P → Arr I M.Y n) → Circle) (c : Circle),
      (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
        f (cells M P R n y) = c * ∏ i : ↥(Rᶜ), a i (oneColumn M P n i y)) ∧
    (∃ (a : ↥(Pᶜ) → (R → Arr I M.Y n) → Circle) (c : Circle),
      (∀ i, Measurable (a i)) ∧ ∀ᵐ y ∂M.ownKernel (n+2) e,
        f (cells M P R n y) = c * ∏ i : ↥(Pᶜ), a i (oneRow M R n i y))}

lemma zero_mem_fullExact (P R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    (0 : Lp ℂ 2 (cellLaw M P R n e)) ∈ fullExact M P R n e := by
  refine ⟨1,measurable_const,0,by simp,?_,?_⟩ <;>
    exact ⟨1,1,fun _ => measurable_const,Filter.Eventually.of_forall (by intro y; simp)⟩

lemma allSplitExact_subset_fullExact (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      allSplitExact M P R n e ⊆ fullExact M P R n e := by
  filter_upwards [row_all_splits_product M hM P R s t n,column_all_splits_product M hM P R s t n]
    with e hr hc
  intro v hv
  obtain ⟨f,g,h,hf,hg,hh,c,hv',he⟩ := hv.1 t
  by_cases hz : c = 0
  · rw [hz,zero_smul] at hv'
    rw [hv']
    exact zero_mem_fullExact M P R n e
  have hrow : ∀ t' : ComplementSplit R, circleLp (cellLaw M P R n e) f hf ∈ rowSplitExact M P R t' n e := by
    intro t'
    have h := JoiningOperator.smul_mem_splitExact _ _ _ _ _ c⁻¹ (hv.1 t')
    rwa [hv',smul_smul,inv_mul_cancel₀ hz,one_smul] at h
  have hcol : ∀ s' : ComplementSplit P, circleLp (cellLaw M P R n e) f hf ∈ columnSplitExact M P R s' n e := by
    intro s'
    have h := JoiningOperator.smul_mem_splitExact _ _ _ _ _ c⁻¹ (hv.2 s')
    rwa [hv',smul_smul,inv_mul_cancel₀ hz,one_smul] at h
  exact ⟨f,hf,c,hv',hr f hf hrow,hc f hf hcol⟩

lemma commonActive_le_fullExact_span (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M P s.A s.B R t.A t.B n e ≤
        (Submodule.span ℂ (fullExact M P R n e)).topologicalClosure := by
  filter_upwards [allSplitExact_span M hM P R s t n,
    allSplitExact_subset_fullExact M hM P R s t n] with e he hs
  rw [←he]
  exact Submodule.topologicalClosure_mono (Submodule.span_mono hs)

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set

theorem ae_map_descent {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → S} (hf : Measurable f)
    {P : S → Prop} (hP : ∀ᵐ ω ∂μ, P (f ω)) : ∀ᵐ s ∂μ.map f, P s := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let κ := condDistrib id f μ
  have hnull : NullMeasurableSet {ω | P (f ω)} μ := by
    exact NullMeasurableSet.congr (nullMeasurableSet_univ (μ := μ))
      (by filter_upwards [hP] with ω hω; exact propext (iff_of_true trivial hω))
  obtain ⟨t,ht,htm,hte⟩ := hnull.exists_measurable_subset_ae_eq
  have hta : ∀ᵐ ω ∂μ, ω ∈ t := by
    filter_upwards [hP,hte] with ω hω he
    exact he.mpr hω
  have hgood : ∀ᵐ s ∂μ.map f, ∀ᵐ ω ∂κ s, ω ∈ t ∧ f ω = s := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Ω => p.2 ∈ t ∧ f p.2 = p.1)
    change ∀ᵐ p ∂μ.map f ⊗ₘ condDistrib id f μ, p.2 ∈ t ∧ f p.2 = p.1
    rw [compProd_map_condDistrib hf.aemeasurable aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      ((htm.preimage measurable_snd).inter (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst))).mpr
    filter_upwards [hta] with ω hω
    exact ⟨hω,rfl⟩
  filter_upwards [hgood] with s hs
  obtain ⟨ω,hω,he⟩ := hs.exists
  rw [←he]
  exact ht hω
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {P H : Type*} [MeasurableSpace P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopology H]

lemma random_projection_exactness (μ : Measure P) [SFinite μ]
    (V C : P → Submodule ℂ H) [∀ p, (V p).HasOrthogonalProjection]
    (hC : ∀ p, IsClosed (C p : Set H)) (hCV : ∀ p, C p ≤ V p)
    (hm : ∀ᵐ pair ∂μ.prod μ,
      (V pair.1).starProjection ∘L (V pair.2).starProjection =
        (V pair.2).starProjection ∘L (V pair.1).starProjection ∧
      V pair.1 ⊓ V pair.2 ≤ C pair.1) :
    ∀ᵐ p ∂μ, V p = C p := by
  let F := fun p => (V p).starProjection
  filter_upwards [essentialRange.ae_range_le μ F, Measure.ae_ae_of_ae_prod hm] with p hp hpm
  apply le_antisymm _ (hCV p)
  have hc : essentialRange μ F ≤ (C p).comap (F p).toLinearMap := by
    apply essentialRange.le_comap_of_ae_comp μ F (F p) (C p) (hC p)
    filter_upwards [hpm] with q hq
    rintro _ ⟨v,rfl⟩
    apply hq.2
    constructor
    · exact (V p).starProjection_apply_mem _
    · change F p (F q v) ∈ V q
      rw [show F p (F q v) = F q (F p v) from congrArg (fun A : H →L[ℂ] H => A v) hq.1]
      exact (V q).starProjection_apply_mem _
  intro v hv
  have hv' : v ∈ essentialRange μ F := hp ⟨v,(V p).starProjection_eq_self_iff.mpr hv⟩
  have hh := hc hv'
  change (V p).starProjection v ∈ C p at hh
  rwa [(V p).starProjection_eq_self_iff.mpr hv] at hh

omit [SecondCountableTopology H] in

lemma essential_projection_not_ae_zero (μ : Measure P)
    (V : P → Submodule ℂ H) [∀ p, (V p).HasOrthogonalProjection]
    (v : H) (hv : v ∈ essentialRange μ (fun p => (V p).starProjection)) (hne : v ≠ 0) :
    ¬ ∀ᵐ p ∂μ, (V p).starProjection v = 0 := by
  intro hz
  have hk : v ∈ essentialKernel μ (fun p => (V p).starProjection.adjoint) := by
    change ∀ᵐ p ∂μ, (V p).starProjection.adjoint v = 0
    simpa only [(isSelfAdjoint_starProjection _).adjoint_eq] using hz
  exact hne ((inner_self_eq_zero (𝕜 := ℂ)).mp ((Submodule.mem_orthogonal _ _).mp hv v hk))

lemma active_projection_not_ae_zero (μ : Measure P)
    (V : P → Submodule ℂ H) [∀ p, (V p).HasOrthogonalProjection] :
    ∀ᵐ p ∂μ, ∀ v ∈ V p, v ≠ 0 → ¬ ∀ᵐ q ∂μ, (V q).starProjection v = 0 := by
  filter_upwards [essentialRange.ae_range_le μ (fun p => (V p).starProjection)] with p hp
  intro v hv hne
  exact essential_projection_not_ae_zero μ V v
    (hp ⟨v,(V p).starProjection_eq_self_iff.mpr hv⟩) hne
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [retained10 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev Cell (i : I) := ({i} : Finset I) → ({i} : Finset I) → Arr I M.Y 0

def padCell (i : I) (y : Arr I M.Y 0) : Cell M i := fun _ _ => y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_padCell (i : I) : Measurable (padCell M i) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_id

def slotCell (i : I) : Arr I M.Y 1 → Cell M i := padCell M i ∘ plane 0 0 i
include retained10 in
@[fun_prop] lemma measurable_slotCell (i : I) : Measurable (slotCell M i) := by
  let _ := retained10
  exact (measurable_padCell M i).comp (measurable_plane _ _ _)

def slotRest (i : I) (y : Arr I M.Y 1) : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 :=
  fun j => plane 0 0 j y
@[fun_prop] lemma measurable_slotRest (i : I) : Measurable (slotRest M i) := by
  exact Measurable.of_eval fun _ => measurable_plane _ _ _

def slotLocal (i : I) : Kernel (Arr I M.U 0) (Cell M i) := (M.ownKernel 0).map (padCell M i)
instance (i : I) : IsMarkovKernel (slotLocal M i) := Kernel.IsMarkovKernel.map _ (measurable_padCell M i)

def slotActive (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 ν) := by
  classical
  exact if h : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν then
    (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure
  else ⊥

lemma slotActive_eq (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1)
    (h : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν) :
    slotActive M i ν p = (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure := by
  rw [slotActive,dite_eq_left h]

lemma slotActive_closed (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) :
    IsClosed (slotActive M i ν p : Set (Lp ℂ 2 ν)) := by
  unfold slotActive
  split
  · exact Submodule.isClosed_topologicalClosure _
  · exact isClosed_singleton

instance (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1) :
    CompleteSpace (slotActive M i ν p) := (slotActive_closed M i ν p).completeSpace_coe

omit [DecidableEq I] in
lemma cells_single_row (i : I) :
    cells M {i} {i} 0 = slotCell M i ∘ plane 1 0 i := by
  funext y j a
  have hj : (j : I) = i := Finset.mem_singleton.mp j.property
  have ha : (a : I) = i := Finset.mem_singleton.mp a.property
  simp only [cells,slotCell,padCell,Function.comp_apply,hj,ha]
  rfl

include retained10 in
lemma cells_single_column (i : I) :
    cells M {i} {i} 0 = slotCell M i ∘ plane 1 (Fin.last 1) i := by
  let _ := retained10
  funext y j a
  have hj : (j : I) = i := Finset.mem_singleton.mp j.property
  have ha : (a : I) = i := Finset.mem_singleton.mp a.property
  simp only [cells,slotCell,padCell,Function.comp_apply,hj,ha]
  exact (congrFun (plane_first_last M 0 i i) y).symm

include retained10 in
lemma slotCell_marginal (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ p ∂M.parameterLaw 1, MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
      (slotLocal M i (plane 0 0 i p)) := by
  let _ := retained10
  have h := ConditionalFibres.marginal (measurable_plane 0 0 i)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i)
  filter_upwards [h] with p hp
  exact (MeasurePreserving.mk (measurable_padCell M i) (Kernel.map_apply _ (measurable_padCell M i) _).symm).comp hp

lemma row_marginal_fibre (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (plane 1 0 i) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 0 i e)) := by
  have hproper : ({i} : Finset I) ≠ Finset.univ := by
    intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ] at this
    omega
  have h := (rows_conditional M hM {i} hproper 0).comp_left
    (measurable_pi_apply (⟨i,Finset.mem_singleton_self i⟩ : ({i} : Finset I)))
  rw [FiniteKernel.map_eval] at h
  exact ConditionalFibres.marginal (measurable_plane _ _ _)
    (M.ownKernel_conditional 2) h

omit [DecidableEq I] in
lemma column_marginal_fibre (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (plane 1 (Fin.last 1) i) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 (Fin.last 1) i e)) := by
  exact ConditionalFibres.marginal (measurable_plane _ _ _) (M.ownKernel_conditional 2)
    (M.plane_conditional hI 1 i)

lemma singleton_cellLaw (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ e ∂M.parameterLaw 2, cellLaw M {i} {i} 0 e =
      slotLocal M i (plane 0 0 i (plane 1 0 i e)) := by
  have hproper : ({i} : Finset I) ≠ Finset.univ := by
    intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ] at this
    omega
  let hparam : MeasurePreserving (plane 1 0 i) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent 1 0 i⟩
  filter_upwards [cells_fibre_marginal M hM {i} {i} hproper 0,
    row_marginal_fibre M hM hI i,
    hparam.quasiMeasurePreserving.ae (slotCell_marginal M hI i)] with e hc hr hs
  have hh := hs.comp hr
  rw [←cells_single_row] at hh
  exact hc.map_eq.symm.trans hh.map_eq
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
section
lemma iIndepFun_map_iff_measurable {A B J C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype J] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : B → J → C) (g : A → B) (hf : ∀ j, Measurable (fun b => f b j)) (hg : Measurable g) :
    iIndepFun (fun j b => f b j) (μ.map g) ↔ iIndepFun (fun j a => f (g a) j) μ := by
  let : IsProbabilityMeasure (μ.map g) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hg.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hf j).aemeasurable),
    iIndepFun_iff_map_fun_eq_pi_map (f := fun j a => f (g a) j) (fun j => ((hf j).comp hg).aemeasurable)]
  simp only [Measure.map_map (Measurable.of_eval hf) hg,
    Measure.map_map (hf _) hg]
  rfl
end
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def slotTuple (r : I) (y : Arr I M.Y 1) : I → Cell M r :=
  fun j => padCell M r (plane 0 0 j y)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_slotTuple (r : I) : Measurable (slotTuple M r) :=
  Measurable.of_eval fun _ => (measurable_padCell M r).comp (measurable_plane _ _ _)

def slotTupleKernel (r : I) : Kernel (Arr I M.U 1) (I → Cell M r) :=
  (M.ownKernel 1).map (slotTuple M r)
instance (r : I) : IsMarkovKernel (slotTupleKernel M r) :=
  Kernel.IsMarkovKernel.map _ (measurable_slotTuple M r)

def tupleParameter (p : Arr I M.U 1) : I → Arr I M.U 0 := fun j => plane 0 0 j p
omit [DecidableEq I] in
@[fun_prop] lemma measurable_tupleParameter : Measurable (tupleParameter M) :=
  Measurable.of_eval fun _ => measurable_plane _ _ _

omit [DecidableEq I] in
lemma slotTuple_marginal (hI : 2 ≤ Fintype.card I) (r : I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      MeasurePreserving (fun z : I → Cell M r => z j) (slotTupleKernel M r p)
        (slotLocal M r (tupleParameter M p j)) := by
  have h (j : I) := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [ae_all_iff.mpr h] with p hp j
  refine ⟨measurable_pi_apply j,?_⟩
  rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M r),
    Measure.map_map (measurable_pi_apply j) (measurable_slotTuple M r)]
  change (M.ownKernel 1 p).map (padCell M r ∘ plane 0 0 j) = _
  rw [←Measure.map_map (measurable_padCell M r) (measurable_plane 0 0 j),(hp j).map_eq]
  change ((M.ownKernel 0) (plane 0 0 j p)).map (padCell M r) =
    (slotLocal M r) (tupleParameter M p j)
  exact (Kernel.map_apply (M.ownKernel 0) (measurable_padCell M r) _).symm

lemma tuple_planes_product (j : I) :
    ∀ᵐ p ∂M.parameterLaw 1, MeasurePreserving (planes 0 (Finset.univ.erase j))
      (M.ownKernel 1 p)
      (Measure.pi (fun t : (Finset.univ.erase j : Finset I) =>
        M.ownKernel 0 (plane 0 0 t p))) := by
  have hproper : Finset.univ.erase j ≠ (Finset.univ : Finset I) := by
    intro he
    have := congrArg (fun s : Finset I => j ∈ s) he
    simp at this
  exact ConditionalFibres.marginal (measurable_planes _ _)
    (M.ownKernel_conditional 1) (M.planes_conditional 0 _ hproper)

lemma slotTuple_proper (r : I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun z : I → Cell M r => z t) (slotTupleKernel M r p) := by
  filter_upwards [ae_all_iff.mpr (tuple_planes_product M)] with p hp j
  rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M r)]
  apply (iIndepFun_map_iff_measurable (J := ↥(Finset.univ.erase j)) _ _ _ (fun t => measurable_pi_apply (t : I))
    (measurable_slotTuple M r)).mpr
  have h := iIndepFun_pi (μ := fun t : (Finset.univ.erase j : Finset I) =>
    M.ownKernel 0 (plane 0 0 t p)) (fun _ : (Finset.univ.erase j : Finset I) =>
    (measurable_padCell M r).aemeasurable)
  rw [←(hp j).map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 1 p)
    (fun (b : ↥(Finset.univ.erase j : Finset I) → Arr I M.Y 0) t => padCell M r (b t))
    (planes 0 (Finset.univ.erase j))
    (fun t => (measurable_padCell M r).comp (measurable_pi_apply t))
    (measurable_planes 0 _)).mp h

lemma exists_good_tuple_set (hI : 2 ≤ Fintype.card I) (r : I) :
    ∃ D : Set (Arr I M.U 1), MeasurableSet D ∧ (∀ᵐ p ∂M.parameterLaw 1, p ∈ D) ∧
      (∀ p ∈ D, ∀ j, MeasurePreserving (fun z : I → Cell M r => z j)
        (slotTupleKernel M r p) (slotLocal M r (tupleParameter M p j))) ∧
      (∀ p ∈ D, ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun z : I → Cell M r => z t) (slotTupleKernel M r p)) := by
  let P := fun p => (∀ j, MeasurePreserving (fun z : I → Cell M r => z j)
    (slotTupleKernel M r p) (slotLocal M r (tupleParameter M p j))) ∧
    (∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun z : I → Cell M r => z t) (slotTupleKernel M r p))
  have hp : ∀ᵐ p ∂M.parameterLaw 1, P p := (slotTuple_marginal M hI r).and (slotTuple_proper M r)
  have hn : NullMeasurableSet {p | P p} (M.parameterLaw 1) := by
    exact NullMeasurableSet.congr (nullMeasurableSet_univ (μ := M.parameterLaw 1))
      (by filter_upwards [hp] with p h; exact propext (iff_of_true trivial h))
  obtain ⟨D,hD,hDm,he⟩ := hn.exists_measurable_subset_ae_eq
  refine ⟨D,hDm,?_,fun p h => (hD h).1,fun p h => (hD h).2⟩
  filter_upwards [hp,he] with p hp he
  exact he.mpr hp
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (hu : Measurable u)

def productTupleKernel : Kernel P (I → Y) :=
  FiniteKernel.pi (fun i => κ.comap (fun p => u p i) ((measurable_pi_apply i).comp hu))
instance : IsMarkovKernel (productTupleKernel κ u hu) := inferInstanceAs (IsMarkovKernel (FiniteKernel.pi _))

include hu in
lemma exists_good_tuple_kernel (μ : Measure P)
    (hm : ∀ᵐ p ∂μ, ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ᵐ p ∂μ, ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ Λ' : Kernel P (I → Y), IsMarkovKernel Λ' ∧ Λ' =ᵐ[μ] Λ ∧
      (∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ' p) (κ (u p i))) ∧
      (∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
        fun y : I → Y => y j) (Λ' p)) := by
  classical
  let Q := fun p => (∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) ∧
    (∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) => fun y : I → Y => y j) (Λ p))
  have hq : ∀ᵐ p ∂μ, Q p := hm.and hind
  have hn : NullMeasurableSet {p | Q p} μ :=
    NullMeasurableSet.congr (nullMeasurableSet_univ (μ := μ))
      (by filter_upwards [hq] with p h; exact propext (iff_of_true trivial h))
  obtain ⟨D,hD,hDm,he⟩ := hn.exists_measurable_subset_ae_eq
  let L := Kernel.piecewise hDm Λ (productTupleKernel κ u hu)
  have hlm (p) (i) : MeasurePreserving (fun y : I → Y => y i) (L p) (κ (u p i)) := by
    by_cases hp : p ∈ D
    · simpa only [L,Kernel.piecewise_apply,ite_eq_left hp] using (hD hp).1 i
    · simpa only [L,Kernel.piecewise_apply,ite_eq_right hp,productTupleKernel,FiniteKernel.pi_apply,
        Kernel.comap_apply] using (measurePreserving_eval (fun i => κ (u p i)) i)
  have hli (p) (i) : iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (L p) := by
    by_cases hp : p ∈ D
    · simpa only [L,Kernel.piecewise_apply,ite_eq_left hp] using (hD hp).2 i
    · simp only [L,Kernel.piecewise_apply,ite_eq_right hp,productTupleKernel,FiniteKernel.pi_apply,Kernel.comap_apply]
      exact (iIndepFun_pi (μ := fun i => κ (u p i)) (fun _ => measurable_id.aemeasurable)).precomp
        Subtype.val_injective
  refine ⟨L,inferInstance,?_,hlm,hli⟩
  filter_upwards [hq,he] with p hp he
  exact (Kernel.piecewise_apply p).trans (ite_eq_left (he.mpr hp))
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawTuple (y : Arr I M.Y 1) : I → Arr I M.Y 0 := fun j => plane 0 0 j y
omit [DecidableEq I] in
@[fun_prop] lemma measurable_rawTuple : Measurable (rawTuple M) :=
  Measurable.of_eval fun _ => measurable_plane _ _ _

def rawTupleKernel : Kernel (Arr I M.U 1) (I → Arr I M.Y 0) := (M.ownKernel 1).map (rawTuple M)
instance : IsMarkovKernel (rawTupleKernel M) := Kernel.IsMarkovKernel.map _ (measurable_rawTuple M)

omit [DecidableEq I] in
lemma rawTuple_marginal (hI : 2 ≤ Fintype.card I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      MeasurePreserving (fun z : I → Arr I M.Y 0 => z j) (rawTupleKernel M p)
        (M.ownKernel 0 (tupleParameter M p j)) := by
  have h (j : I) := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [ae_all_iff.mpr h] with p hp j
  refine ⟨measurable_pi_apply j,?_⟩
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M),
    Measure.map_map (measurable_pi_apply j) (measurable_rawTuple M)]
  exact (hp j).map_eq

lemma rawTuple_proper :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun z : I → Arr I M.Y 0 => z t) (rawTupleKernel M p) := by
  filter_upwards [ae_all_iff.mpr (tuple_planes_product M)] with p hp j
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
  apply (iIndepFun_map_iff_measurable (J := ↥(Finset.univ.erase j)) _ _ _
    (fun t => measurable_pi_apply (t : I)) (measurable_rawTuple M)).mpr
  have h := iIndepFun_pi (μ := fun t : (Finset.univ.erase j : Finset I) =>
    M.ownKernel 0 (plane 0 0 t p)) (fun _ : (Finset.univ.erase j : Finset I) =>
    measurable_id.aemeasurable)
  rw [←(hp j).map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 1 p)
    (fun (b : ↥(Finset.univ.erase j : Finset I) → Arr I M.Y 0) t => b t)
    (planes 0 (Finset.univ.erase j)) (fun t => measurable_pi_apply t)
    (measurable_planes 0 _)).mp h

lemma raw_good_tuple_kernel (hI : 2 ≤ Fintype.card I) :
    ∃ Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0), IsMarkovKernel Λ ∧
      Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M ∧
      (∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
        (M.ownKernel 0 (tupleParameter M p j))) ∧
      (∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun y : I → Arr I M.Y 0 => y t) (Λ p)) :=
  exists_good_tuple_kernel (M.ownKernel 0) (rawTupleKernel M) (tupleParameter M)
    (measurable_tupleParameter M) (M.parameterLaw 1) (rawTuple_marginal M hI) (rawTuple_proper M)
end

universe u
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawTuple_time_commute : rawTuple M ∘ amap M.timeY 1 =
    (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i)) ∘ rawTuple M := rfl

lemma rawTuple_time_preserving :
    ∀ᵐ p ∂M.parameterLaw 1,
      MeasurePreserving (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i))
        (rawTupleKernel M p) (rawTupleKernel M (amap M.timeU 1 p)) := by
  filter_upwards [M.ownKernel_time_preserving 1] with p hp
  have htime : Measurable (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i)) :=
    Measurable.of_eval fun i => (measurable_amap M.timeY.measurable 0).comp (measurable_pi_apply i)
  refine ⟨htime,?_⟩
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M),
    Kernel.map_apply _ (measurable_rawTuple M),Measure.map_map htime (measurable_rawTuple M),
    ←rawTuple_time_commute M,←Measure.map_map (measurable_rawTuple M) (measurable_amap M.timeY.measurable 1),hp.map_eq]

lemma tupleParameter_time (p : Arr I M.U 1) (i : I) :
    tupleParameter M (amap M.timeU 1 p) i = amap M.timeU 0 (tupleParameter M p i) := rfl

lemma goodTuple_time_preserving
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M) :
    ∀ᵐ p ∂M.parameterLaw 1,
      MeasurePreserving (fun y : I → Arr I M.Y 0 => fun i => amap M.timeY 0 (y i))
        (Λ p) (Λ (amap M.timeU 1 p)) := by
  filter_upwards [rawTuple_time_preserving M,hL,
    (M.parameterLaw_invariant 1).quasiMeasurePreserving.ae hL] with p hp h1 h2
  rw [h1,h2]; exact hp

lemma exactCode_time
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j))) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ q : I → HilbertCode (M.ownKernel 0),
      (p,q) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      (amap M.timeU 1 p,fun i => HilbertCode.transport (amap M.timeU 0)
        (amapEquiv M.timeY 0) (q i)) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) := by
  have hk (i : I) : ∀ᵐ p ∂M.parameterLaw 1, MeasurePreserving (amap M.timeY 0)
      (M.ownKernel 0 (tupleParameter M p i))
      (M.ownKernel 0 (amap M.timeU 0 (tupleParameter M p i))) :=
    (show MeasurePreserving (plane 0 0 i) (M.parameterLaw 1) (M.parameterLaw 0) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae
        (M.ownKernel_time_preserving 0)
  filter_upwards [ae_all_iff.mpr hk,goodTuple_time_preserving M Λ hL] with p hp hΛ q hq
  exact exactCode_transport (M.ownKernel 0) Λ (tupleParameter M) (amap M.timeU 0)
    (amapEquiv M.timeY 0) p (amap M.timeU 1 p) (tupleParameter_time M p) hp hΛ (hm p) q hq

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y))
  (u : P → I → U)

def exactCodeEquivTransport (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hm' : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p') (κ (u p' i))) :
    {q : I → HilbertCode κ // (p,q) ∈ exactCodeSet κ Λ u} ≃
      {q : I → HilbertCode κ // (p',q) ∈ exactCodeSet κ Λ u} := by
  have hu' (i) : u p i = F.symm (u p' i) := by rw [hu i,F.symm_apply_apply]
  have hκ' (i) : MeasurePreserving E.symm (κ (u p' i)) (κ (F.symm (u p' i))) := by
    rw [hu i,F.symm_apply_apply]
    exact MeasurePreserving.symm E (hκ i)
  have hΛ' : MeasurePreserving (fun y : I → Y => fun i => E.symm (y i)) (Λ p') (Λ p) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrRight (fun _ : I => E)) hΛ
  refine {
    toFun := fun q => ⟨fun i => HilbertCode.transport F E (q.val i),
      exactCode_transport κ Λ u F E p p' hu hκ hΛ hm q.val q.property⟩
    invFun := fun q => ⟨fun i => HilbertCode.transport F.symm E.symm (q.val i),
      exactCode_transport κ Λ u F.symm E.symm p' p hu' hκ' hΛ' hm' q.val q.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro q
    apply Subtype.ext
    funext i
    apply HilbertCode.transport_inverse F E (q.val i) (q.property.2.1 i).2 (q.property.2.1 i).1
    rw [q.property.1 i]
    exact hκ i
  · intro q
    apply Subtype.ext
    funext i
    have h := HilbertCode.transport_inverse F.symm E.symm (q.val i)
      (q.property.2.1 i).2 (q.property.2.1 i).1
    apply h
    rw [q.property.1 i]
    exact hκ' i
end

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable (Y : Type*) [MeasurableSpace Y]

def measurableCircleSubgroup : Subgroup (Y → Circle) where
  carrier := {f | Measurable f}
  one_mem' := measurable_const
  mul_mem' := fun hf hg => hf.mul hg
  inv_mem' := fun hf => hf.inv
abbrev MeasurableCircle := measurableCircleSubgroup Y
instance measurableCircleCoeFun : CoeFun (MeasurableCircle Y) (fun _ => Y → Circle) := ⟨fun f => f.val⟩
lemma measurableCircle_measurable (f : MeasurableCircle Y) : Measurable (f : Y → Circle) := f.property
variable {Y} (μ : Measure Y)

def phaseSubgroup : Subgroup (MeasurableCircle Y) where
  carrier := {f | ∃ c : Circle, (f : Y → Circle) =ᵐ[μ] fun _ => c}
  one_mem' := ⟨1,Filter.Eventually.of_forall fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a*b,?_⟩
    filter_upwards [ha,hb] with y hfy hgy
    exact congrArg₂ (·*·) hfy hgy
  inv_mem' := by
    rintro f ⟨a,ha⟩
    refine ⟨a⁻¹,?_⟩
    filter_upwards [ha] with y hy
    exact congrArg Inv.inv hy
abbrev ProjectiveCircle := MeasurableCircle Y ⧸ phaseSubgroup μ

def projectiveCircle (f : Y → Circle) (hf : Measurable f) : ProjectiveCircle μ :=
  QuotientGroup.mk (⟨f,hf⟩ : MeasurableCircle Y)

lemma projectiveCircle_eq_iff (f g : Y → Circle) (hf : Measurable f) (hg : Measurable g) :
    projectiveCircle μ f hf = projectiveCircle μ g hg ↔
      ∃ c : Circle, f =ᵐ[μ] fun y => c*g y := by
  change (QuotientGroup.mk (⟨f,hf⟩ : MeasurableCircle Y) =
    QuotientGroup.mk (⟨g,hg⟩ : MeasurableCircle Y)) ↔ _
  rw [QuotientGroup.eq]
  change (∃ c : Circle, (fun y => (f y)⁻¹ * g y) =ᵐ[μ] fun _ => c) ↔ _
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    apply eq_inv_mul_iff_mul_eq.mpr
    exact (mul_comm c (f y)).trans (inv_mul_eq_iff_eq_mul.mp hy).symm
  · rintro ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    rw [hy,mul_inv_rev]
    simp [mul_comm]

lemma projectiveCircle_mul (f g : Y → Circle) (hf : Measurable f) (hg : Measurable g) :
    projectiveCircle μ (fun y => f y * g y) (hf.mul hg) =
      projectiveCircle μ f hf * projectiveCircle μ g hg := rfl

lemma projectiveCircle_one : projectiveCircle μ (fun _ : Y => 1) measurable_const = 1 := rfl
lemma projectiveCircle_inv (f : Y → Circle) (hf : Measurable f) :
    projectiveCircle μ (fun y => (f y)⁻¹) hf.inv = (projectiveCircle μ f hf)⁻¹ := rfl
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y I : Type*} [MeasurableSpace Y] [Fintype I]

def exactCircleTuples (μ : Measure (I → Y)) : Subgroup (I → MeasurableCircle Y) where
  carrier := {f | ∃ c : Circle, ∀ᵐ y ∂μ, ∏ i, f i (y i) = c}
  one_mem' := ⟨1,Filter.Eventually.of_forall fun _ => by simp⟩
  mul_mem' := by
    rintro f g ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c*d,?_⟩
    filter_upwards [hc,hd] with y hy hz
    change (∏ i, f i (y i) * g i (y i)) = c*d
    rw [Finset.prod_mul_distrib,hy,hz]
  inv_mem' := by
    rintro f ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    change (∏ i, (f i (y i))⁻¹) = c⁻¹
    rw [Finset.prod_inv_distrib,hy]

def tupleProjectivize (ν : I → Measure Y) : (I → MeasurableCircle Y) →*
    (∀ i, ProjectiveCircle (ν i)) where
  toFun := fun f i => QuotientGroup.mk (f i)
  map_one' := rfl
  map_mul' := fun _ _ => rfl

def exactProjectiveTuples (μ : Measure (I → Y)) (ν : I → Measure Y) :
    Subgroup (∀ i, ProjectiveCircle (ν i)) :=
  (exactCircleTuples μ).map (tupleProjectivize ν)

def exactProjectiveSlot (μ : Measure (I → Y)) (ν : I → Measure Y) (i : I) :
    exactProjectiveTuples μ ν →* ProjectiveCircle (ν i) where
  toFun := fun a => a.val i
  map_one' := rfl
  map_mul' := fun _ _ => rfl

variable [DecidableEq I]
lemma exactCircleTuples_constant_of_slot (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (f : I → MeasurableCircle Y) (hf : f ∈ exactCircleTuples μ)
    (i : I) (hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = 1) :
    ∀ j, projectiveCircle (ν j) (f j) (measurableCircle_measurable Y (f j)) = 1 := by
  have hpm (j : I) : Measurable (fun y : I → Y => (f j (y j) : ℂ)) :=
    measurable_subtype_coe.comp ((measurableCircle_measurable Y (f j)).comp (measurable_pi_apply j))
  have hpn (j : I) : ∀ᵐ y ∂μ, ‖(f j (y j) : ℂ)‖ = 1 :=
    Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  have hpi (j : I) : iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => (f t (y t) : ℂ)) μ :=
    (hind j).comp (fun t y => (f t y : ℂ))
      (fun t => measurable_subtype_coe.comp (measurableCircle_measurable Y (f t)))
  obtain ⟨c,hc⟩ := hf
  have hc' : ∀ᵐ y ∂μ, ∏ j, (f j (y j) : ℂ) = (c : ℂ) := by
    filter_upwards [hc] with y hy
    exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun a : Circle => (a : ℂ)) hy)
  have hx := exact_tuple_dichotomy hk (fun j (y : I → Y) => (f j (y j) : ℂ))
    (fun j => (hpm j).aestronglyMeasurable) hpn hpi (c : ℂ) (Circle.norm_coe c) hc'
  have hi' : ∃ d : Circle, (f i : Y → Circle) =ᵐ[ν i] fun _ => d := by
    rw [←projectiveCircle_one (ν i),projectiveCircle_eq_iff] at hi
    simpa only [mul_one] using hi
  obtain ⟨d,hd⟩ := hi'
  have hdi : (fun y : I → Y => (f i (y i) : ℂ)) =ᵐ[μ] fun _ => (d : ℂ) :=
    ((hm i).quasiMeasurePreserving.ae_eq_comp hd).mono fun _ h => congrArg (fun a : Circle => (a : ℂ)) h
  rcases hx with hz | he
  · have hh := hz i
    rw [integral_congr_ae hdi,integral_const,probReal_univ,one_smul] at hh
    have hn := Circle.norm_coe d
    rw [hh,norm_zero] at hn
    norm_num at hn
  · intro j
    let a : Circle := ⟨∫ y, (f j (y j) : ℂ) ∂μ,mem_sphere_zero_iff_norm.mpr (he j).2⟩
    have hj : ∀ᵐ y ∂μ, f j (y j) = a :=
      (he j).1.mono fun _ h => Circle.coe_injective h
    have hj' : (f j : Y → Circle) =ᵐ[ν j] fun _ => a := by
      rw [←(hm j).map_eq]
      apply (ae_map_iff (hm j).measurable.aemeasurable
        (measurableSet_eq_fun (measurableCircle_measurable Y (f j)) measurable_const)).mpr
      exact hj
    rw [←projectiveCircle_one (ν j),projectiveCircle_eq_iff]
    exact ⟨a,by simpa only [mul_one] using hj'⟩
lemma exactProjectiveSlot_injective (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i : I) :
    Function.Injective (exactProjectiveSlot μ ν i) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨f,hf,hfa⟩ := a.property
  have hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = 1 := by
    change tupleProjectivize ν f i = 1
    rw [hfa]
    exact ha
  apply Subtype.ext
  funext j
  have hj := exactCircleTuples_constant_of_slot hk μ ν hm hind f hf i hi j
  change (a : ∀ j, ProjectiveCircle (ν j)) j = 1
  rw [←hfa]
  exact hj

def exactProjectiveMatching (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i j : I) :
    (exactProjectiveSlot μ ν i).range ≃* (exactProjectiveSlot μ ν j).range :=
  (MonoidHom.ofInjective (exactProjectiveSlot_injective hk μ ν hm hind i)).symm.trans
    (MonoidHom.ofInjective (exactProjectiveSlot_injective hk μ ν hm hind j))
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)
namespace HilbertCode
variable {κ}
def projective (u : U) (q : HilbertCode κ) : ProjectiveCircle (κ u) :=
  projectiveCircle (κ u) (circleRep q) (measurable_circleRep_fixed q)

lemma projective_injective {u : U} {q r : HilbertCode κ}
    (hbq : q.base = u) (hbr : r.base = u)
    (hcq : q.IsCanonical) (hcr : r.IsCanonical)
    (huq : q.IsUnimodular) (hur : r.IsUnimodular)
    (he : projective u q = projective u r) : q = r := by
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff (κ u) _ _ _ _).mp he
  have hq := circleRep_ae q huq
  have hr := circleRep_ae r hur
  rw [hbq] at hq
  rw [hbr] at hr
  apply eq_of_decode_smul (hbq.trans hbr.symm) hcq hcr (Circle.norm_coe c)
  rw [hbq]
  filter_upwards [hc,hq,hr] with y hy hqy hry
  rw [←hqy,hy]
  change (c : ℂ) * (circleRep r y : ℂ) = (c : ℂ) * representative (r,y)
  rw [hry]

lemma projective_encode_phase {u : U} (f : Y → Circle) (hf : Measurable f)
    (d : ℂ) (hd : ‖d‖ = 1) (q : HilbertCode κ)
    (he : q = encode u (d • circleLp (κ u) f hf)) (hu : q.IsUnimodular) :
    projective u q = projectiveCircle (κ u) f hf := by
  let c : Circle := ⟨d,mem_sphere_zero_iff_norm.mpr hd⟩
  apply (projectiveCircle_eq_iff (κ u) _ _ _ _).mpr
  refine ⟨c,?_⟩
  have hb : q.base = u := by rw [he]; rfl
  have hr := representative_eq_decode (encode u (d • circleLp (κ u) f hf))
  change (fun y => representative (encode u (d • circleLp (κ u) f hf),y)) =ᵐ[κ u]
    fun y => (decode (encode u (d • circleLp (κ u) f hf)) : Lp ℂ 2 (κ u)) y at hr
  rw [decode_encode] at hr
  have hcircle := circleRep_ae q hu
  rw [hb] at hcircle
  filter_upwards [hcircle,hr,Lp.coeFn_smul d (circleLp (κ u) f hf),circleLp_coe (κ u) f hf]
    with y h1 h2 h3 h4
  apply Circle.coe_injective
  change (circleRep q y : ℂ) = d * (f y : ℂ)
  exact h1.trans ((congrArg (fun z : HilbertCode κ => representative (z,y)) he).trans
    (h2.trans (h3.trans (congrArg (d * ·) h4))))
end HilbertCode

omit [DecidableEq I] in
lemma exact_code_projective_mem {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    (fun i => HilbertCode.projective (u p i) (a i)) ∈
      exactProjectiveTuples (Λ p) (fun i => κ (u p i)) := by
  obtain ⟨c,hc⟩ := exactCode_circle_tuple κ Λ u hm ha
  refine ⟨(fun i => ⟨HilbertCode.circleRep (a i),HilbertCode.measurable_circleRep_fixed (a i)⟩),?_,rfl⟩
  exact ⟨c,hc⟩

omit [DecidableEq I] in
lemma exact_projective_has_codes (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (v : exactProjectiveTuples (Λ p) (fun i => κ (u p i))) :
    ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧
      ∀ i, HilbertCode.projective (u p i) (a i) = v.val i := by
  obtain ⟨f,hf,hfv⟩ := v.property
  obtain ⟨c,hc⟩ := hf
  obtain ⟨a,d,ha,hd⟩ := normalized_exact_codes κ Λ u p hm
    (fun i => f i) (fun i => (measurableCircle_measurable Y (f i))) c hc
  refine ⟨a,ha,?_⟩
  intro i
  have he := HilbertCode.projective_encode_phase (κ := κ) (f i) (measurableCircle_measurable Y (f i))
    (d i) (hd i).1 (a i) (hd i).2 (ha.2.1 i).2
  exact he.trans (congrFun hfv i)
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [StandardBorelSpace U] in
lemma HilbertCode.distance_self (q : HilbertCode κ) : HilbertCode.distance q q = 0 := by
  rw [←HilbertCode.encode_decode q,HilbertCode.distance_encode,dist_self]

omit [StandardBorelSpace P] [StandardBorelSpace U] in
lemma exactCode_unique_slot (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {p : P} {a b : I → HilbertCode κ}
    (ha : (p,a) ∈ exactCodeSet κ Λ u) (hb : (p,b) ∈ exactCodeSet κ Λ u)
    (i : I) (hi : a i = b i) : a = b := by
  rcases HilbertCode.exact_codes_dichotomy hk (Λ p) a b
    (fun j => (ha.1 j).trans (hb.1 j).symm) ha.2.1 hb.2.1
    (fun j => by simpa only [ha.1 j] using hm p j) (hind p) ha.2.2 hb.2.2 with h | h
  · exact h
  · have h := h i
    rw [hi,HilbertCode.distance_self] at h
    norm_num at h

lemma exactCode_slot_embedding (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableEmbedding (fun t : ExactCodeTuple κ Λ u => (t.1.1,t.1.2 i)) := by
  let : StandardBorelSpace (ExactCodeTuple κ Λ u) :=
    (measurableSet_exactCodeSet κ Λ u hu).standardBorel
  apply Measurable.measurableEmbedding
    (measurable_subtype_coe.fst.prodMk ((measurable_pi_apply i).comp measurable_subtype_coe.snd))
  intro a b hab
  have hp : a.1.1 = b.1.1 := congrArg (fun x : P × HilbertCode κ => x.1) hab
  have hi : a.1.2 i = b.1.2 i := congrArg (fun x : P × HilbertCode κ => x.2) hab
  have hb : (a.1.1,b.1.2) ∈ exactCodeSet κ Λ u := by rw [hp]; exact b.property
  exact Subtype.ext (Prod.ext hp (exactCode_unique_slot κ Λ u hk hm hind a.property hb i hi))

def exactMatching (i : I) : P × HilbertCode κ → I → HilbertCode κ :=
  Function.extend (fun t : ExactCodeTuple κ Λ u => (t.1.1,t.1.2 i))
    (fun t => t.1.2) (fun pq j => HilbertCode.encode (u pq.1 j) 0)

lemma measurable_exactMatching (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    Measurable (exactMatching κ Λ u i) := by
  apply (exactCode_slot_embedding κ Λ u hu hk hm hind i).measurable_extend
    measurable_subtype_coe.snd
  apply Measurable.of_eval
  intro j
  exact MeasurableSection.zero (((measurable_pi_apply j).comp hu).comp measurable_fst)

lemma exactMatching_exact (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I)
    {p : P} {a : I → HilbertCode κ} (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    exactMatching κ Λ u i (p,a i) = a :=
  (exactCode_slot_embedding κ Λ u hu hk hm hind i).injective.extend_apply _ _ ⟨(p,a),ha⟩
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

abbrev ExactCodeSlot (p : P) (i : I) := {q : HilbertCode κ //
  ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q}

omit [DecidableEq I] in
lemma codeSlot_projective_range (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) (i : I) :
    {g : ProjectiveCircle (κ (u p i)) | ∃ q : ExactCodeSlot κ Λ u p i,
      HilbertCode.projective (u p i) q.val = g} =
      (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  ext g
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨a,ha,hai⟩ := q.property
    let v : exactProjectiveTuples (Λ p) (fun j => κ (u p j)) :=
      ⟨fun j => HilbertCode.projective (u p j) (a j),exact_code_projective_mem κ Λ u hm ha⟩
    exact ⟨v,by change HilbertCode.projective (u p i) (a i) = g; rw [hai,hq]⟩
  · rintro ⟨v,hv⟩
    obtain ⟨a,ha,he⟩ := exact_projective_has_codes κ Λ u p hm v
    exact ⟨⟨a i,a,ha,rfl⟩,(he i).trans hv⟩

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma codeSlot_projective_injective (p : P) (i : I) :
    Function.Injective (fun q : ExactCodeSlot κ Λ u p i => HilbertCode.projective (u p i) q.val) := by
  intro q r he
  obtain ⟨a,ha,hai⟩ := q.property
  obtain ⟨b,hb,hbi⟩ := r.property
  apply Subtype.ext
  change HilbertCode.projective (u p i) q.val = HilbertCode.projective (u p i) r.val at he
  rw [←hai,←hbi] at he ⊢
  exact HilbertCode.projective_injective (ha.1 i) (hb.1 i)
    (ha.2.1 i).1 (hb.2.1 i).1 (ha.2.1 i).2 (hb.2.1 i).2 he

def codeSlotEquivProjective (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) (i : I) :
    ExactCodeSlot κ Λ u p i ≃ (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  let f : ExactCodeSlot κ Λ u p i →
      (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := fun q =>
    ⟨HilbertCode.projective (u p i) q.val,by
      exact (Set.ext_iff.mp (codeSlot_projective_range κ Λ u p hm i) _).mp ⟨q,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r he
    exact codeSlot_projective_injective κ Λ u p i (congrArg Subtype.val he)
  · intro v
    have hv := v.property
    have hv := (Set.ext_iff.mp (codeSlot_projective_range κ Λ u p hm i) v.val).mpr hv
    obtain ⟨q,hq⟩ := hv
    exact ⟨q,Subtype.ext hq⟩

def codeSlotMatching (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I) :
    ExactCodeSlot κ Λ u p i ≃ ExactCodeSlot κ Λ u p j :=
  (codeSlotEquivProjective κ Λ u p hm i).trans
    ((exactProjectiveMatching hk (Λ p) (fun j => κ (u p j)) hm hind i j).toEquiv.trans
      (codeSlotEquivProjective κ Λ u p hm j).symm)
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y))
  (u : P → I → U)

lemma exactSlot_transport (F : U → U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (i : I) (q : HilbertCode κ)
    (hq : ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q) :
    ∃ a : I → HilbertCode κ, (p',a) ∈ exactCodeSet κ Λ u ∧ a i = HilbertCode.transport F E q := by
  obtain ⟨a,ha,hai⟩ := hq
  exact ⟨fun j => HilbertCode.transport F E (a j),
    exactCode_transport κ Λ u F E p p' hu hκ hΛ hm a ha,congrArg _ hai⟩

def localGraphTimeEquiv (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (S : Set (U × HilbertCode κ)) (i : I)
    (hS : ∀ q, (u p i,q) ∈ S ↔ ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q)
    (hS' : ∀ q, (F (u p i),q) ∈ S ↔ ∃ a : I → HilbertCode κ, (p',a) ∈ exactCodeSet κ Λ u ∧ a i = q) :
    {q : HilbertCode κ // (u p i,q) ∈ S} ≃ {q : HilbertCode κ // (F (u p i),q) ∈ S} := by
  have hu' (i) : u p i = F.symm (u p' i) := by rw [hu i,F.symm_apply_apply]
  have hκ' (i) : MeasurePreserving E.symm (κ (u p' i)) (κ (F.symm (u p' i))) := by
    rw [hu i,F.symm_apply_apply]; exact MeasurePreserving.symm E (hκ i)
  have hΛ' : MeasurePreserving (fun y : I → Y => fun i => E.symm (y i)) (Λ p') (Λ p) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrRight (fun _ : I => E)) hΛ
  refine {
    toFun := fun q => ⟨HilbertCode.transport F E q.val,
      (hS' _).mpr (exactSlot_transport κ Λ u F E p p' hu hκ hΛ (hm p) i q.val ((hS _).mp q.property))⟩
    invFun := fun q => ⟨HilbertCode.transport F.symm E.symm q.val,
      (hS _).mpr (exactSlot_transport κ Λ u F.symm E.symm p' p hu' hκ' hΛ' (hm p') i q.val ((hS' _).mp q.property))⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro q
    obtain ⟨a,ha,hai⟩ := (hS _).mp q.property
    apply Subtype.ext
    apply HilbertCode.transport_inverse F E q.val
    · rw [←hai]; exact (ha.2.1 i).2
    · rw [←hai]; exact (ha.2.1 i).1
    · rw [←hai,ha.1 i]; exact hκ i
  · intro q
    obtain ⟨a,ha,hai⟩ := (hS' _).mp q.property
    apply Subtype.ext
    apply HilbertCode.transport_inverse F.symm E.symm q.val
    · rw [←hai]; exact (ha.2.1 i).2
    · rw [←hai]; exact (ha.2.1 i).1
    · rw [←hai,ha.1 i]; exact hκ' i
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma rectangle_first_commutes
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω, y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω, x ω)) μ (μD.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    (essentialRange μX F).starProjection ∘L (essentialRange μC K).starProjection =
      (essentialRange μC K).starProjection ∘L (essentialRange μX F).starProjection := by
  have h := rectangle_all_intertwines hx hy hc hd hcy hcx hdy hdx hF hG hK hN h1 h2
  exact essentialRange.projection_commutes μX F (essentialRange μD N) (essentialRange μC K) h.2.2.1
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_active_commutes_corner (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (rowActive M rows.A cols.A cols.P cols.B n e).starProjection ∘L
        (columnActive M rows.A rows.P rows.B cols.A n e).starProjection =
      (columnActive M rows.A rows.P rows.B cols.A n e).starProjection ∘L
        (rowActive M rows.A cols.A cols.P cols.B n e).starProjection := by
  filter_upwards [grouped_fibre_rectangle M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP rows.disjointPA rows.disjointPB rows.cardPA rows.cardPB rows.properPA rows.properPB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.cover cols.nonemptyA cols.nonemptyB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.A cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.A cols.P rows.disjointPB rows.properPB n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.B cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.B cols.P rows.disjointPB rows.properPB n]
      with e hr hx hy hc hd hcx hcy hdx hdy
  have h := rectangle_first_commutes
    (F := fibreRowEdge M rows.A cols.P cols.A cols.B n e)
    (G := fibreRowEdge M rows.B cols.P cols.A cols.B n e)
    (K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e)
    (N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e) hx hy hc hd
    ⟨hc.measurable.prodMk hy.measurable, by
      rw [←hc.map_eq,←hy.map_eq]
      exact hcy.map_prod_eq_prod_map_map hc.measurable.aemeasurable hy.measurable.aemeasurable⟩
    ⟨hc.measurable.prodMk hx.measurable, by
      rw [←hc.map_eq,←hx.map_eq]
      exact hcx.map_prod_eq_prod_map_map hc.measurable.aemeasurable hx.measurable.aemeasurable⟩
    ⟨hd.measurable.prodMk hy.measurable, by
      rw [←hd.map_eq,←hy.map_eq]
      exact hdy.map_prod_eq_prod_map_map hd.measurable.aemeasurable hy.measurable.aemeasurable⟩
    ⟨hd.measurable.prodMk hx.measurable, by
      rw [←hd.map_eq,←hx.map_eq]
      exact hdx.map_prod_eq_prod_map_map hd.measurable.aemeasurable hx.measurable.aemeasurable⟩
    (fibreRowEdge_measurable M rows.A cols.P cols.A cols.B n e) (fibreRowEdge_measurable M rows.B cols.P cols.A cols.B n e)
    (fibreColumnEdge_measurable M rows.P rows.A rows.B cols.A n e) (fibreColumnEdge_measurable M rows.P rows.A rows.B cols.B n e)
    (hr.mono fun _ h => h.1) (hr.mono fun _ h => h.2)
  exact h

lemma grouped_active_commutes (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (rowActive M rows.P cols.P cols.A cols.B n e).starProjection ∘L
        (columnActive M rows.P rows.A rows.B cols.P n e).starProjection =
      (columnActive M rows.P rows.A rows.B cols.P n e).starProjection ∘L
        (rowActive M rows.P cols.P cols.A cols.B n e).starProjection := by
  exact grouped_active_commutes_corner M hM rows.swapPA cols.swapPA n
end ArrayObjects.Object.Rolled

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orthogonal_line_projection (S C : Set H) (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (hCV : (Submodule.span ℂ C).topologicalClosure = V)
    (hCS : C ⊆ S)
    (horth : ∀ v ∈ S, ∀ w ∈ S, inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w)
    {v : H} (hv : v ∈ S) : V.starProjection v = 0 ∨ V.starProjection v = v := by
  by_cases hm : v ∈ V
  · exact Or.inr (V.starProjection_eq_self_iff.mpr hm)
  · left
    apply V.starProjection_apply_eq_zero_iff.mpr
    rw [←hCV,Submodule.orthogonal_closure,Submodule.mem_orthogonal']
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rcases horth v hv w (hCS hw) with ho | ⟨c,hc⟩
      · exact ho
      · exact (hm (hc.symm ▸ V.smul_mem c (hCV ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span hw)))).elim
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
    | smul c x hx ih => simp only [inner_smul_right,ih,mul_zero]

lemma inf_projection_on_left (A B : Submodule ℂ H)
    [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A ⊓ B).HasOrthogonalProjection]
    (hc : A.starProjection ∘L B.starProjection = B.starProjection ∘L A.starProjection)
    {v : H} (hv : v ∈ A) : (A ⊓ B).starProjection v = B.starProjection v := by
  have hin : B.starProjection v ∈ A ⊓ B := by
    refine ⟨A.starProjection_eq_self_iff.mp ?_,B.starProjection_apply_mem _⟩
    have h := congrArg (fun T : H →L[ℂ] H => T v) hc
    simpa only [ContinuousLinearMap.comp_apply,A.starProjection_eq_self_iff.mpr hv] using h
  apply (A ⊓ B).eq_starProjection_of_mem_of_inner_eq_zero hin
  intro w hw
  exact B.starProjection_inner_eq_zero _ _ hw.2

lemma common_lines_projection (S C : Set H) (A B : Submodule ℂ H)
    [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A ⊓ B).HasOrthogonalProjection]
    (hspan : (Submodule.span ℂ C).topologicalClosure = A ⊓ B)
    (hCS : C ⊆ S)
    (horth : ∀ v ∈ S, ∀ w ∈ S, inner ℂ v w = 0 ∨ ∃ c : ℂ, v = c • w)
    (hc : A.starProjection ∘L B.starProjection = B.starProjection ∘L A.starProjection)
    {v : H} (hv : v ∈ S) (hva : v ∈ A) : B.starProjection v = 0 ∨ B.starProjection v = v := by
  have hin : B.starProjection v ∈ A ⊓ B := by
    refine ⟨A.starProjection_eq_self_iff.mp ?_,B.starProjection_apply_mem _⟩
    have h := congrArg (fun T : H →L[ℂ] H => T v) hc
    simpa only [ContinuousLinearMap.comp_apply,A.starProjection_eq_self_iff.mpr hva] using h
  have he : (A ⊓ B).starProjection v = B.starProjection v := by
    apply (A ⊓ B).eq_starProjection_of_mem_of_inner_eq_zero hin
    intro w hw
    exact B.starProjection_inner_eq_zero _ _ hw.2
  rw [←he]
  exact orthogonal_line_projection S C _ hspan hCS horth hv
end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma grouped_row_line_projection (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2), ∀ v ∈ rowSplitExact M P R t n e,
      (columnActive M P s.A s.B R n e).starProjection v = 0 ∨
      (columnActive M P s.A s.B R n e).starProjection v = v := by
  filter_upwards [grouped_exact_split_span M hM P R s t n,
    rowSplitExact_dichotomy M hM P R s.partition.properP t n,
    grouped_active_commutes M hM s.partition t.partition n,
    rowActive_eq_range M hM P s.partition.properP t.partition n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM P t.A s.partition.properP n,
    cells_fibre_marginal M hM P t.B s.partition.properP n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
    with e hspan horth hc hr hz ha hb hab
  intro v hv
  apply common_lines_projection (rowSplitExact M P R t n e)
    (rowSplitExact M P R t n e ∩ columnSplitExact M P R s n e)
    (rowActive M P R t.A t.B n e) (columnActive M P s.A s.B R n e)
    hspan Set.inter_subset_left horth hc hv
  let hpair := cells_pair_preserving M ha hb hab
  rw [hr hz hpair]
  exact JoiningOperator.splitExact_le_active hz hpair hv

lemma grouped_full_row_column_exact (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2), ∀ v,
      (∀ t' : ComplementSplit R, v ∈ rowSplitExact M P R t' n e) →
      v ∈ columnActive M P s.A s.B R n e → v ∈ fullExact M P R n e := by
  have hspans := ae_all_iff.mpr fun s' : ComplementSplit P => grouped_exact_split_span M hM P R s' t n
  have hinvs := ae_all_iff.mpr fun s' : ComplementSplit P =>
    commonActive_complement_invariant M hM P R s' s t t n
  filter_upwards [hspans,hinvs,rowSplitExact_dichotomy M hM P R s.partition.properP t n,
    allSplitExact_subset_fullExact M hM P R s t n,
    rowActive_eq_range M hM P s.partition.properP t.partition n,
    cells_fibre_marginal M hM P R s.partition.properP n,
    cells_fibre_marginal M hM P t.A s.partition.properP n,
    cells_fibre_marginal M hM P t.B s.partition.properP n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
    with e hspan hinv horth hfull hr hz ha hb hab
  intro v hrow hcol
  by_cases hv0 : v = 0
  · subst v
    exact zero_mem_fullExact M P R n e
  have hactive : v ∈ rowActive M P R t.A t.B n e := by
    let hpair := cells_pair_preserving M ha hb hab
    rw [hr hz hpair]
    exact JoiningOperator.splitExact_le_active hz hpair (hrow t)
  apply hfull
  refine ⟨hrow,?_⟩
  intro s'
  have hv : v ∈ (Submodule.span ℂ (rowSplitExact M P R t n e ∩
      columnSplitExact M P R s' n e)).topologicalClosure := by
    rw [hspan s',hinv s']
    exact ⟨hactive,hcol⟩
  obtain ⟨w,hw,hn⟩ := nonzero_inner_in_closedSpan _ v hv0 hv
  obtain ⟨c,hc⟩ := (horth v (hrow t) w hw.1).resolve_left hn
  rw [hc]
  exact JoiningOperator.smul_mem_splitExact _ _ _ _ _ c hw.2
end ArrayObjects.Object.Rolled

section
open MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma lp_star_zero : star (0 : Lp ℂ 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : Lp ℂ 2 μ),Lp.coeFn_zero ℂ 2 μ] with x hs hz
  simp only [Pi.zero_apply,Pi.star_apply] at hs hz ⊢
  rw [hs,hz,star_zero]

lemma lp_star_sub (f g : Lp ℂ 2 μ) : star (f-g) = star f-star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f-g),Lp.coeFn_star f,Lp.coeFn_star g,
    Lp.coeFn_sub f g,Lp.coeFn_sub (star f) (star g)] with x hs hf hg hd hd'
  simp only [Pi.star_apply,Pi.sub_apply] at hs hf hg hd hd'
  rw [hs,hd,star_sub,hd',hf,hg]

lemma lp_star_smul (c : ℂ) (f : Lp ℂ 2 μ) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f),Lp.coeFn_star f,Lp.coeFn_smul c f,
    Lp.coeFn_smul (star c) (star f)] with x hs hf hc hc'
  simpa only [Pi.star_apply,hc,hc',Pi.smul_apply,star_smul,hf] using hs

lemma lp_inner_star_star (f g : Lp ℂ 2 μ) :
    inner ℂ (star f) (star g) = star (inner ℂ f g) := by
  rw [L2.inner_def,L2.inner_def]
  change _ = conj (∫ x, inner ℂ (f x) (g x) ∂μ)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f,Lp.coeFn_star g] with x hf hg
  simp only [Pi.star_apply] at hf hg
  rw [hf,hg]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_mul,star_star,mul_comm]

lemma lp_inner_star_right (f g : Lp ℂ 2 μ) :
    inner ℂ f (star g) = star (inner ℂ (star f) g) := by
  simpa only [star_star] using lp_inner_star_star (star f) g

lemma lp_star_projection (V : Submodule ℂ (Lp ℂ 2 μ)) [V.HasOrthogonalProjection]
    (hV : ∀ v ∈ V, star v ∈ V) (f : Lp ℂ 2 μ) :
    V.starProjection (star f) = star (V.starProjection f) := by
  apply V.eq_starProjection_of_mem_of_inner_eq_zero
    (hV _ (V.starProjection_apply_mem f))
  intro w hw
  rw [←lp_star_sub]
  have h := V.starProjection_inner_eq_zero f (star w) (hV w hw)
  have hs := lp_inner_star_star (f - V.starProjection f) (star w)
  simpa only [star_star,h,star_zero] using hs
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {Ω X Y U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace U]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma operator_star (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (h : Lp ℂ 2 ρ) : operator hx hy (star h) = star (operator hx hy h) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_operator,lp_inner_star_right,inner_operator]
  change _ = conj (∫ ω, inner ℂ (star g (x ω)) (h (y ω)) ∂μ)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [hx.quasiMeasurePreserving.ae (Lp.coeFn_star g),
    hy.quasiMeasurePreserving.ae (Lp.coeFn_star h)] with ω hg hh
  simp only [Pi.star_apply] at hg hh
  rw [hg,hh]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_mul,star_star,mul_comm]

lemma family_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (u : U) (h : Lp ℂ 2 ρ) : family κ ν ρ u (star h) = star (family κ ν ρ u h) := by
  classical
  unfold family
  split_ifs with hp
  · exact operator_star hp.1 hp.2 h
  · simpa only [zero_apply] using lp_star_zero.symm

lemma family_adjoint_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (u : U) (h : Lp ℂ 2 ν) :
    (family κ ν ρ u).adjoint (star h) = star ((family κ ν ρ u).adjoint h) := by
  classical
  unfold family
  split_ifs with hp
  · rw [operator_adjoint]
    exact operator_star hp.2 hp.1 h
  · simpa only [map_zero,zero_apply] using lp_star_zero.symm

lemma family_active_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (m : Measure U) {v : Lp ℂ 2 ν} (hv : v ∈ essentialRange m (family κ ν ρ)) :
    star v ∈ essentialRange m (family κ ν ρ) := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro k hk
  have hs : star k ∈ essentialKernel m (fun u => (family κ ν ρ u).adjoint) := by
    change ∀ᵐ u ∂m, (family κ ν ρ u).adjoint (star k) = 0
    change ∀ᵐ u ∂m, (family κ ν ρ u).adjoint k = 0 at hk
    filter_upwards [hk] with u hu
    rw [family_adjoint_star,hu,lp_star_zero]
  rw [lp_inner_star_right,(Submodule.mem_orthogonal _ _).mp hv (star k) hs,star_zero]

lemma family_active_projection_star (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)
    (m : Measure U) (v : Lp ℂ 2 ν) :
    (essentialRange m (family κ ν ρ)).starProjection (star v) =
      star ((essentialRange m (family κ ν ρ)).starProjection v) :=
  lp_star_projection _ (fun _ hv => family_active_star κ ν ρ m hv) v

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma operator_circle_exact [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (f : X → Circle) (g : Y → Circle) (hf : Measurable f) (hg : Measurable g)
    (c : Circle) (he : ∀ᵐ ω ∂μ, g (y ω) = c * f (x ω)) :
    operator hx hy (circleLp ρ g hg) = (c : ℂ) • circleLp ν f hf := by
  have hp : pull hy (circleLp ρ g hg) = (c : ℂ) • pull hx (circleLp ν f hf) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ρ g hg) hy,
      Lp.coeFn_compMeasurePreserving (circleLp ν f hf) hx,
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ g hg),
      hx.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
      Lp.coeFn_smul (c : ℂ) (pull hx (circleLp ν f hf)),he]
      with ω h1 h2 h3 h4 h5 he
    calc
      _ = (g (y ω) : ℂ) := h1.trans h3
      _ = (c : ℂ) * (f (x ω) : ℂ) := congrArg ((↑) : Circle → ℂ) he
      _ = _ := (h5.trans (congrArg (fun z : ℂ => (c : ℂ)*z) (h2.trans h4))).symm
  change (pull hx).adjoint (pull hy (circleLp ρ g hg)) = _
  rw [hp,map_smul]
  congr 1
  exact congrArg (fun A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => A (circleLp ν f hf)) (pull_adjoint_pull hx)
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma rowActive_star (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M A R n e)} (hv : v ∈ rowActive M A R S D n e) :
    star v ∈ rowActive M A R S D n e := by
  unfold rowActive at *
  rw [fibreRowEdge_eq] at *
  exact JoiningOperator.family_active_star _ _ _ _ hv
omit [DecidableEq I] in
lemma columnActive_star (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M P R n e)} (hv : v ∈ columnActive M P A B R n e) :
    star v ∈ columnActive M P A B R n e := by
  unfold columnActive at *
  rw [fibreColumnEdge_eq] at *
  exact JoiningOperator.family_active_star _ _ _ _ hv
omit [DecidableEq I] in
lemma commonActive_star (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    {v : Lp ℂ 2 (cellLaw M P R n e)} (hv : v ∈ commonActive M P A B R S D n e) :
    star v ∈ commonActive M P A B R S D n e :=
  ⟨rowActive_star M _ _ _ _ _ _ hv.1,columnActive_star M _ _ _ _ _ _ hv.2⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
  [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} {z : Ω → Z}
  {κ : Kernel S Z} [IsSFiniteKernel κ]
lemma conditional_ae_descent (hs : Measurable s) (hz : Measurable z)
    (hκ : HasCondDistrib z s κ μ) {P : S → Z → Prop} (hP : ∀ᵐ ω ∂μ, P (s ω) (z ω)) :
    ∀ᵐ a ∂μ.map s, ∀ᵐ b ∂κ a, P a b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Z => P p.1 p.2)
  rw [←hκ.map_eq]
  exact ae_map_descent μ (hs.prodMk hz) hP
end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω X Y R : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace R]
  [StandardBorelSpace Ω] [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace R]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {x : Ω → X} {y : Ω → Y} {r : Ω → R}
  {κ : Kernel R (X × Y)} [IsSFiniteKernel κ]

lemma family_circle_exact (hx : Measurable x) (hy : Measurable y) (hr : Measurable r)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) r κ μ)
    (hm : ∀ᵐ a ∂μ.map r, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (f : X → Circle) (g : Y → Circle) (c : R → Circle)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ ω ∂μ, g (y ω) = c (r ω) * f (x ω)) :
    ∀ᵐ a ∂μ.map r, family κ ν ρ a (circleLp ρ g hg) = (c a : ℂ) • circleLp ν f hf := by
  have h := conditional_ae_descent (κ := κ)
    (P := fun a p => g p.2 = c a * f p.1) hr (hx.prodMk hy) hκ he
  filter_upwards [h,hm] with a ha hm
  rw [family_eq κ ν ρ a hm.1 hm.2]
  exact operator_circle_exact hm.1 hm.2 f g hf hg (c a) ha
end JoiningOperator

section
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure X} {ρ : Measure Y}
lemma binary_projection_transfer (D : Submodule ℂ (Lp ℂ 2 ν)) (E : Submodule ℂ (Lp ℂ 2 ρ))
    [D.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hE : ∀ w ∈ E, star w ∈ E)
    (F : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν)
    (hF : D.starProjection ∘L F = F ∘L E.starProjection)
    (v : Lp ℂ 2 ν) (w : Lp ℂ 2 ρ) (c : ℂ) (hc : c ≠ 0) (hv : v ≠ 0)
    (he : F (star w) = c • v)
    (hw : E.starProjection w = 0 ∨ E.starProjection w = w) :
    D.starProjection v = v ↔ E.starProjection w = w := by
  have hi := congrArg (fun A : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => A (star w)) hF
  simp only [ContinuousLinearMap.comp_apply,he,map_smul,lp_star_projection E hE] at hi
  constructor
  · intro hd
    rcases hw with hz | hid
    · rw [hz,lp_star_zero,map_zero,hd] at hi
      exact (hv ((smul_eq_zero.mp hi).resolve_left hc)).elim
    · exact hid
  · intro hid
    rw [hid,he] at hi
    exact (smul_right_injective _ hc) hi
end

section
open MeasureTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma circleLp_inv (f : X → Circle) (hf : Measurable f) :
    circleLp μ (fun x => (f x)⁻¹) hf.inv = star (circleLp μ f hf) := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => (f x)⁻¹) hf.inv,circleLp_coe μ f hf,
    Lp.coeFn_star (circleLp μ f hf)] with x h1 h2 h3
  rw [h1,h3]
  change (↑((f x)⁻¹) : ℂ) = star (circleLp μ f hf x)
  rw [h2,Circle.coe_inv_eq_conj]
  rfl
end

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev split (s : TriplePartition I) : ComplementSplit s.P :=
  ⟨s.A,s.B,s.nonemptyP,s.nonemptyA,s.nonemptyB,s.disjointPA,s.disjointPB,s.disjointAB,s.cover⟩
end TriplePartition

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma rowSplitExact_le_rowActive (hM : M.IsSaturated) (P R : Finset I)
    (hP : P ≠ Finset.univ) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2), rowSplitExact M P R t n e ⊆ rowActive M P R t.A t.B n e := by
  filter_upwards [rowActive_eq_range M hM P hP t.partition n,
    cells_fibre_marginal M hM P R hP n,
    cells_fibre_marginal M hM P t.A hP n,
    cells_fibre_marginal M hM P t.B hP n,
    cells_indep_columns_fibre M P P t.A t.B t.disjointAB t.partition.properAB n]
    with e hr hz ha hb hab
  rw [hr hz (cells_pair_preserving M ha hb hab)]
  exact JoiningOperator.splitExact_le_active hz (cells_pair_preserving M ha hb hab)

lemma grouped_row_membership_transfer (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂M.parameterLaw (n+2),
      ∀ (f : (cols.A → rows.A → Arr I M.Y n) → Circle)
        (g : (cols.B → rows.A → Arr I M.Y n) → Circle)
        (c : (cols.P → rows.A → Arr I M.Y n) → Circle)
        (hf : Measurable f) (hg : Measurable g) (_hc : Measurable c),
        (∀ᵐ y ∂M.ownKernel (n+2) e,
          (g (cells M rows.A cols.B n y))⁻¹ =
            c (cells M rows.A cols.P n y) * f (cells M rows.A cols.A n y)) →
        (circleLp (cellLaw M rows.A cols.A n e) f hf ∈ columnActive M rows.A rows.P rows.B cols.A n e ↔
         circleLp (cellLaw M rows.A cols.B n e) g hg ∈ columnActive M rows.A rows.P rows.B cols.B n e) := by
  filter_upwards [grouped_active_intersections M hM rows cols n,
    grouped_exact_split_span M hM rows.A cols.B rows.swapPA.split cols.swapPB.swapAB.split n,
    rowSplitExact_dichotomy M hM rows.A cols.B rows.properA cols.swapPB.swapAB.split n,
    rowSplitExact_le_rowActive M hM rows.A cols.A rows.properA cols.swapPA.split n,
    rowSplitExact_le_rowActive M hM rows.A cols.B rows.properA cols.swapPB.swapAB.split n,
    rowPair_fixed_conditional M rows.A cols.P cols.A cols.B n,
    rowPair_fixed_marginals M hM rows.A cols.P cols.A cols.B rows.properA
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n]
      with e hi hs ho hra hrb hk hm hp
  intro f g c hf hg hc he
  have hfex : circleLp (cellLaw M rows.A cols.A n e) f hf ∈
      rowSplitExact M rows.A cols.A cols.swapPA.split n e := by
    apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ f (fun z => (c z)⁻¹) (fun z => (g z)⁻¹) hf hc.inv hg.inv
    filter_upwards [he] with y hy
    rw [hy]
    simp only [inv_mul_cancel_left]
  have hgex : circleLp (cellLaw M rows.A cols.B n e) g hg ∈
      rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e := by
    apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ g (fun z => (c z)⁻¹) (fun z => (f z)⁻¹) hg hc.inv hf.inv
    filter_upwards [he] with y hy
    have h := congrArg Inv.inv hy
    simpa only [inv_inv,mul_inv_rev,mul_comm] using h
  have hw := orthogonal_line_projection
    (rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e)
    (rowSplitExact M rows.A cols.B cols.swapPB.swapAB.split n e ∩
      columnSplitExact M rows.A cols.B rows.swapPA.split n e)
    (commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e)
    hs Set.inter_subset_left ho hgex
  have heq := JoiningOperator.family_circle_exact
    (measurable_cells M rows.A cols.A n) (measurable_cells M rows.A cols.B n)
    (measurable_cells M rows.A cols.P n) hk hm f (fun z => (g z)⁻¹) c hf hg.inv he
  rw [←hp.map_eq] at hi
  have ht : ∀ᵐ r ∂(M.ownKernel (n+2) e).map (cells M rows.A cols.P n),
      (commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e).starProjection
          (circleLp (cellLaw M rows.A cols.A n e) f hf) = circleLp (cellLaw M rows.A cols.A n e) f hf ↔
      (commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e).starProjection
          (circleLp (cellLaw M rows.A cols.B n e) g hg) = circleLp (cellLaw M rows.A cols.B n e) g hg := by
    filter_upwards [hi.1,heq] with r hir her
    apply binary_projection_transfer _ _ (fun _ hv => commonActive_star M _ _ _ _ _ _ _ _ hv)
      (fibreRowEdge M rows.A cols.P cols.A cols.B n e r) hir
      _ _ (c r : ℂ) (Circle.coe_ne_zero _) (circleLp_ne_zero _ f hf) _ hw
    rw [fibreRowEdge_eq]
    rwa [circleLp_inv] at her
  rw [hp.map_eq] at ht
  obtain ⟨r,hr⟩ := ht.exists
  have hfa : circleLp (cellLaw M rows.A cols.A n e) f hf ∈ rowActive M rows.A cols.A cols.P cols.B n e := hra hfex
  have hgb : circleLp (cellLaw M rows.A cols.B n e) g hg ∈ rowActive M rows.A cols.B cols.P cols.A n e := hrb hgex
  simpa only [Submodule.starProjection_eq_self_iff,commonActive,Submodule.mem_inf,
    hfa,hgb,true_and] using hr
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory
variable {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} {μ' : Measure Ω'} {ν : Measure X}
  {f : Ω' → Ω} {x : Ω → X} {y : Ω → Y}

lemma measurePreserving_of_comp (hf : MeasurePreserving f μ' μ) (hx : Measurable x)
    (hxf : MeasurePreserving (x ∘ f) μ' ν) : MeasurePreserving x μ ν := by
  refine ⟨hx,?_⟩
  rw [←hf.map_eq,Measure.map_map hx hf.measurable]
  exact hxf.map_eq

lemma active_pullback (hf : MeasurePreserving f μ' μ) (hx : MeasurePreserving x μ ν)
    (hy : Measurable y) :
    (LinearMap.range (operator (hx.comp hf)
      ((MeasurePreserving.mk hy rfl).comp hf)).toLinearMap).topologicalClosure =
      (LinearMap.range (operator hx (MeasurePreserving.mk hy rfl)).toLinearMap).topologicalClosure := by
  rw [operator_pullback hf hx (MeasurePreserving.mk hy rfl)]
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma cells_field (A J : Finset I) (n : ℕ) :
    MeasurableSpace.comap (cells M A J n) inferInstance =
      ⨆ j ∈ J, ⨆ a ∈ A, MeasurableSpace.comap (missingRow M n j a) inferInstance := by
  exact field_finset_grid (fun j a y => missingRow M n j a y) J A

lemma row_rest_field (i : I) (s : ComplementSplit ({i} : Finset I)) :
    MeasurableSpace.comap (fun y => (cells M {i} s.A 0 y,cells M {i} s.B 0 y)) inferInstance =
      MeasurableSpace.comap (slotRest M i ∘ plane 1 0 i) inferInstance := by
  change ((inferInstance : MeasurableSpace (s.A → ({i} : Finset I) → Arr I M.Y 0)).prod
    (inferInstance : MeasurableSpace (s.B → ({i} : Finset I) → Arr I M.Y 0))).comap _ = _
  rw [MeasurableSpace.comap_prodMk]
  rw [cells_field, cells_field]
  simp only [Finset.mem_singleton,iSup_iSup_eq_left]
  change (⨆ j ∈ s.A, MeasurableSpace.comap (fun y => plane 0 0 j (plane 1 0 i y)) inferInstance) ⊔
    (⨆ j ∈ s.B, MeasurableSpace.comap (fun y => plane 0 0 j (plane 1 0 i y)) inferInstance) = _
  have h := field_finset_observation (fun j (y : Arr I M.Y 2) => plane 0 0 j (plane 1 0 i y)) (s.A ∪ s.B)
  simp only [Finset.mem_union,iSup_or,iSup_sup_eq] at h
  rw [s.union_eq] at h
  exact h.symm

lemma column_rest_field (i : I) (s : ComplementSplit ({i} : Finset I)) :
    MeasurableSpace.comap (fun y => (cells M s.A {i} 0 y,cells M s.B {i} 0 y)) inferInstance =
      MeasurableSpace.comap (slotRest M i ∘ plane 1 (Fin.last 1) i) inferInstance := by
  change ((inferInstance : MeasurableSpace (({i} : Finset I) → s.A → Arr I M.Y 0)).prod
    (inferInstance : MeasurableSpace (({i} : Finset I) → s.B → Arr I M.Y 0))).comap _ = _
  rw [MeasurableSpace.comap_prodMk]
  rw [cells_field, cells_field]
  simp only [Finset.mem_singleton,iSup_iSup_eq_left]
  have he (j : I) : missingRow M 0 i j = plane 0 0 j ∘ plane 1 (Fin.last 1) i := by
    exact (plane_first_last M 0 j i).symm
  simp_rw [he]
  have h := field_finset_observation (fun j (y : Arr I M.Y 2) => plane 0 0 j (plane 1 (Fin.last 1) i y)) (s.A ∪ s.B)
  simp only [Finset.mem_union,iSup_or,iSup_sup_eq] at h
  rw [s.union_eq] at h
  exact h.symm

lemma rowActive_single_slot (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2, rowActive M {i} {i} s.A s.B 0 e =
      slotActive M i (cellLaw M {i} {i} 0 e) (plane 1 0 i e) := by
  filter_upwards [rowActive_eq_range M hM {i} s.partition.properP s.partition 0,
    cells_fibre_marginal M hM {i} {i} s.partition.properP 0,
    cells_fibre_marginal M hM {i} s.A s.partition.properP 0,
    cells_fibre_marginal M hM {i} s.B s.partition.properP 0,
    cells_indep_columns_fibre M {i} {i} s.A s.B s.disjointAB s.partition.properAB 0,
    row_marginal_fibre M hM hI i] with e hv hx ha hb hab hr
  have hs : MeasurePreserving (slotCell M i) (M.ownKernel 1 (plane 1 0 i e))
      (cellLaw M {i} {i} 0 e) := JoiningOperator.measurePreserving_of_comp hr
        (measurable_slotCell M i) (by rwa [←cells_single_row])
  have hst : MeasurePreserving (fun y => (cells M {i} s.A 0 y,cells M {i} s.B 0 y))
      (M.ownKernel 2 e) ((cellLaw M {i} s.A 0 e).prod (cellLaw M {i} s.B 0 e)) := by
    refine ⟨ha.measurable.prodMk hb.measurable,?_⟩
    rw [←ha.map_eq,←hb.map_eq]
    exact hab.map_prod_eq_prod_map_map ha.measurable.aemeasurable hb.measurable.aemeasurable
  rw [hv hx hst,slotActive_eq M i _ _ hs]
  have h := JoiningOperator.active_observation_eq hx hst
    ((MeasurePreserving.mk (measurable_slotRest M i) rfl).comp hr) (row_rest_field M i s)
  rw [h]
  have hh := JoiningOperator.operator_pullback hr hs (MeasurePreserving.mk (measurable_slotRest M i) rfl)
  simp only [←cells_single_row] at hh
  rw [hh]

lemma columnActive_single_slot (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2, columnActive M {i} s.A s.B {i} 0 e =
      slotActive M i (cellLaw M {i} {i} 0 e) (plane 1 (Fin.last 1) i e) := by
  filter_upwards [columnActive_eq_range M hM s.partition {i} s.partition.properP 0,
    cells_fibre_marginal M hM {i} {i} s.partition.properP 0,
    cells_fibre_marginal M hM s.A {i} s.partition.properA 0,
    cells_fibre_marginal M hM s.B {i} s.partition.properB 0,
    cells_indep_rows_fibre M hM s.A s.B {i} {i} s.disjointAB s.partition.properAB 0,
    column_marginal_fibre M hI i] with e hv hx ha hb hab hr
  have hs : MeasurePreserving (slotCell M i) (M.ownKernel 1 (plane 1 (Fin.last 1) i e))
      (cellLaw M {i} {i} 0 e) := JoiningOperator.measurePreserving_of_comp hr
        (measurable_slotCell M i) (by rwa [←cells_single_column])
  have hst : MeasurePreserving (fun y => (cells M s.A {i} 0 y,cells M s.B {i} 0 y))
      (M.ownKernel 2 e) ((cellLaw M s.A {i} 0 e).prod (cellLaw M s.B {i} 0 e)) := by
    refine ⟨ha.measurable.prodMk hb.measurable,?_⟩
    rw [←ha.map_eq,←hb.map_eq]
    exact hab.map_prod_eq_prod_map_map ha.measurable.aemeasurable hb.measurable.aemeasurable
  rw [hv hx hst,slotActive_eq M i _ _ hs]
  have h := JoiningOperator.active_observation_eq hx hst
    ((MeasurePreserving.mk (measurable_slotRest M i) rfl).comp hr) (column_rest_field M i s)
  rw [h]
  have hh := JoiningOperator.operator_pullback hr hs (MeasurePreserving.mk (measurable_slotRest M i) rfl)
  simp only [←cells_single_column] at hh
  rw [hh]
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y}

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
noncomputable def pullEquiv (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ) :
    Lp ℂ 2 τ ≃ₗᵢ[ℂ] Lp ℂ 2 ν where
  __ := Lp.compMeasurePreservingₗᵢ ℂ e he
  invFun := Lp.compMeasurePreserving e.symm (he.symm e)
  left_inv f := by
    change Lp.compMeasurePreserving e.symm (he.symm e) (Lp.compMeasurePreserving e he f) = f
    rw [←Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) f) = f
    rw [←Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply f

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
lemma pullEquiv_coe (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ) :
    (pullEquiv e he : Lp ℂ 2 τ →L[ℂ] Lp ℂ 2 ν) = pull he := rfl

lemma operator_reparam (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    pull he ∘L operator (he.comp hx) hy = operator hx hy := by
  have hh : pull he ∘L (pull he).adjoint = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
    rw [←pullEquiv_coe e he]
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro f
    exact (pullEquiv e he).apply_symm_apply f
  calc
    pull he ∘L operator (he.comp hx) hy =
        (pull he ∘L (pull he).adjoint) ∘L operator hx hy := by
      unfold operator
      rw [pull_comp hx he,adjoint_comp]
      simp only [comp_assoc]
    _ = operator hx hy := by rw [hh,id_comp]

lemma active_reparam (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (v : Lp ℂ 2 τ) :
    v ∈ (LinearMap.range (operator (he.comp hx) hy).toLinearMap).topologicalClosure ↔
    pull he v ∈ (LinearMap.range (operator hx hy).toLinearMap).topologicalClosure := by
  let E := pullEquiv e he
  have hr : E '' Set.range (operator (he.comp hx) hy) = Set.range (operator hx hy) := by
    rw [←Set.range_comp]
    have hcomp := operator_reparam e he hx hy
    exact congrArg (fun f : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => Set.range f) hcomp
  have hc := E.toHomeomorph.image_closure (s := Set.range (operator (he.comp hx) hy))
  change E '' closure (Set.range (operator (he.comp hx) hy)) = closure (E '' Set.range (operator (he.comp hx) hy)) at hc
  rw [hr] at hc
  change v ∈ closure (Set.range (operator (he.comp hx) hy)) ↔
    E v ∈ closure (Set.range (operator hx hy))
  rw [←hc]
  constructor
  · exact fun hv => ⟨v,hv,rfl⟩
  · rintro ⟨w,hw,hwe⟩
    exact E.injective hwe ▸ hw
end JoiningOperator

section
open MeasureTheory ProbabilityTheory
section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma circleLp_pull {e : X → Y} (he : MeasurePreserving e μ ν) (f : Y → Circle) (hf : Measurable f) :
    JoiningOperator.pull he (circleLp ν f hf) = circleLp μ (f ∘ e) (hf.comp he.measurable) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ν f hf) he,
    he.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
    circleLp_coe μ (f ∘ e) (hf.comp he.measurable)] with x h1 h2 h3
  exact h1.trans (h2.trans h3.symm)
end
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

abbrev CellAt (a j : I) := ({j} : Finset I) → ({a} : Finset I) → Arr I M.Y 0

def collapseCell (a j : I) : CellAt M a j ≃ᵐ Arr I M.Y 0 where
  toFun y := y ⟨j,Finset.mem_singleton_self j⟩ ⟨a,Finset.mem_singleton_self a⟩
  invFun y := fun _ _ => y
  left_inv y := by
    funext s t
    have hs : s = ⟨j,Finset.mem_singleton_self j⟩ := Subtype.ext (Finset.mem_singleton.mp s.property)
    have ht : t = ⟨a,Finset.mem_singleton_self a⟩ := Subtype.ext (Finset.mem_singleton.mp t.property)
    subst s; subst t; rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_apply _).comp (measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_id

omit [DecidableEq I] in
lemma collapse_cell_row (a j : I) : collapseCell M a j ∘ cells M {a} {j} 0 =
    plane 0 0 j ∘ plane 1 0 a := rfl
omit [DecidableEq I] in
lemma collapse_cell_column (a j : I) : collapseCell M a j ∘ cells M {a} {j} 0 =
    plane 0 0 a ∘ plane 1 (Fin.last 1) j := (plane_first_last M 0 a j).symm

def rawSlotActive (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 ν) := by
  classical
  exact if h : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν then
    (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure
  else ⊥
lemma rawSlotActive_eq (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1)
    (h : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν) :
    rawSlotActive M i ν p = (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure := by
  rw [rawSlotActive,dite_eq_left h]
lemma rawSlotActive_closed (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) :
    IsClosed (rawSlotActive M i ν p : Set (Lp ℂ 2 ν)) := by
  unfold rawSlotActive
  split
  · exact Submodule.isClosed_topologicalClosure _
  · exact isClosed_singleton
instance (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1) :
    CompleteSpace (rawSlotActive M i ν p) := (rawSlotActive_closed M i ν p).completeSpace_coe

lemma row_rest_field_mixed (a j : I) (s : ComplementSplit ({j} : Finset I)) :
    MeasurableSpace.comap (fun y => (cells M {a} s.A 0 y,cells M {a} s.B 0 y)) inferInstance =
      MeasurableSpace.comap (slotRest M j ∘ plane 1 0 a) inferInstance := by
  change ((inferInstance : MeasurableSpace (s.A → ({a} : Finset I) → Arr I M.Y 0)).prod
    (inferInstance : MeasurableSpace (s.B → ({a} : Finset I) → Arr I M.Y 0))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,cells_field,cells_field]
  simp only [Finset.mem_singleton,iSup_iSup_eq_left]
  change (⨆ t ∈ s.A, MeasurableSpace.comap (fun y => plane 0 0 t (plane 1 0 a y)) inferInstance) ⊔
    (⨆ t ∈ s.B, MeasurableSpace.comap (fun y => plane 0 0 t (plane 1 0 a y)) inferInstance) = _
  have h := field_finset_observation (fun t (y : Arr I M.Y 2) => plane 0 0 t (plane 1 0 a y)) (s.A ∪ s.B)
  simp only [Finset.mem_union,iSup_or,iSup_sup_eq] at h
  rw [s.union_eq] at h
  exact h.symm

lemma column_rest_field_mixed (a j : I) (s : ComplementSplit ({a} : Finset I)) :
    MeasurableSpace.comap (fun y => (cells M s.A {j} 0 y,cells M s.B {j} 0 y)) inferInstance =
      MeasurableSpace.comap (slotRest M a ∘ plane 1 (Fin.last 1) j) inferInstance := by
  change ((inferInstance : MeasurableSpace (({j} : Finset I) → s.A → Arr I M.Y 0)).prod
    (inferInstance : MeasurableSpace (({j} : Finset I) → s.B → Arr I M.Y 0))).comap _ = _
  rw [MeasurableSpace.comap_prodMk,cells_field,cells_field]
  simp only [Finset.mem_singleton,iSup_iSup_eq_left]
  have he (t : I) : missingRow M 0 j t = plane 0 0 t ∘ plane 1 (Fin.last 1) j := by
    exact (plane_first_last M 0 t j).symm
  simp_rw [he]
  have h := field_finset_observation (fun t (y : Arr I M.Y 2) => plane 0 0 t (plane 1 (Fin.last 1) j y)) (s.A ∪ s.B)
  simp only [Finset.mem_union,iSup_or,iSup_sup_eq] at h
  rw [s.union_eq] at h
  exact h.symm

lemma singleton_collapse_preserving (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e)
      (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) := by
  have ha : ({a} : Finset I) ≠ Finset.univ := by
    intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton,Finset.card_univ] at this
    omega
  let hr : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent 1 0 a⟩
  have hm := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [cells_fibre_marginal M hM {a} {j} ha 0,row_marginal_fibre M hM hI a,
    hr.quasiMeasurePreserving.ae hm] with e hc hr hm
  exact JoiningOperator.measurePreserving_of_comp hc (collapseCell M a j).measurable
    (by rw [collapse_cell_row]; exact hm.comp hr)

lemma rowActive_mixed_slot (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j : I) (ha : ({a} : Finset I) ≠ Finset.univ) (s : ComplementSplit ({j} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (ν : Measure (Arr I M.Y 0))
      (he : MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e) ν) (v : Lp ℂ 2 ν),
      v ∈ rawSlotActive M j ν (plane 1 0 a e) ↔
      JoiningOperator.pull he v ∈ rowActive M {a} {j} s.A s.B 0 e := by
  filter_upwards [rowActive_eq_range M hM {a} ha s.partition 0,
    cells_fibre_marginal M hM {a} {j} ha 0,
    cells_fibre_marginal M hM {a} s.A ha 0,
    cells_fibre_marginal M hM {a} s.B ha 0,
    cells_indep_columns_fibre M {a} {a} s.A s.B s.disjointAB s.partition.properAB 0,
    row_marginal_fibre M hM hI a] with e hv hx hA hB hAB hr
  intro ν he v
  let hst := cells_pair_preserving M hA hB hAB
  have hs : MeasurePreserving (plane 0 0 j) (M.ownKernel 1 (plane 1 0 a e)) ν :=
    JoiningOperator.measurePreserving_of_comp hr (measurable_plane _ _ _) (he.comp hx)
  rw [hv hx hst,←JoiningOperator.active_reparam (collapseCell M a j) he hx hst]
  have h := JoiningOperator.active_observation_eq (he.comp hx) hst
    ((MeasurePreserving.mk (measurable_slotRest M j) rfl).comp hr) (row_rest_field_mixed M a j s)
  rw [h,rawSlotActive_eq M j ν _ hs]
  have hh : JoiningOperator.operator (he.comp hx)
      ((MeasurePreserving.mk (measurable_slotRest M j) rfl).comp hr) =
      JoiningOperator.operator hs (MeasurePreserving.mk (measurable_slotRest M j) rfl) := by
    exact JoiningOperator.operator_pullback hr hs (MeasurePreserving.mk (measurable_slotRest M j) rfl)
  rw [hh]
lemma columnActive_mixed_slot (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j : I) (hj : ({j} : Finset I) ≠ Finset.univ) (s : ComplementSplit ({a} : Finset I)) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (ν : Measure (Arr I M.Y 0))
      (he : MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e) ν) (v : Lp ℂ 2 ν),
      v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) ↔
      JoiningOperator.pull he v ∈ columnActive M {a} s.A s.B {j} 0 e := by
  filter_upwards [columnActive_eq_range M hM s.partition {j} hj 0,
    cells_fibre_marginal M hM {a} {j} s.partition.properP 0,
    cells_fibre_marginal M hM s.A {j} s.partition.properA 0,
    cells_fibre_marginal M hM s.B {j} s.partition.properB 0,
    cells_indep_rows_fibre M hM s.A s.B {j} {j} s.disjointAB s.partition.properAB 0,
    column_marginal_fibre M hI j] with e hv hx hA hB hAB hr
  intro ν he v
  let hst := cells_pair_preserving M hA hB hAB
  have hraw := he.comp hx
  rw [collapse_cell_column] at hraw
  have hs : MeasurePreserving (plane 0 0 a) (M.ownKernel 1 (plane 1 (Fin.last 1) j e)) ν :=
    JoiningOperator.measurePreserving_of_comp hr (measurable_plane _ _ _) hraw
  rw [hv hx hst,←JoiningOperator.active_reparam (collapseCell M a j) he hx hst]
  have h := JoiningOperator.active_observation_eq (he.comp hx) hst
    ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) (column_rest_field_mixed M a j s)
  rw [h,rawSlotActive_eq M a ν _ hs]
  have hh : JoiningOperator.operator (he.comp hx)
      ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) =
      JoiningOperator.operator hs (MeasurePreserving.mk (measurable_slotRest M a) rfl) := by
    have hc := collapse_cell_column M a j
    have hop : JoiningOperator.operator (he.comp hx)
        ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) =
        JoiningOperator.operator (hs.comp hr)
          ((MeasurePreserving.mk (measurable_slotRest M a) rfl).comp hr) := by
      congr 1
    exact hop.trans (JoiningOperator.operator_pullback hr hs (MeasurePreserving.mk (measurable_slotRest M a) rfl))
  rw [hh]

end ArrayObjects.Object.Rolled
end

section
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in
lemma singleton_proper (hk : 2 ≤ Fintype.card I) (i : I) : ({i} : Finset I) ≠ Finset.univ := by
  intro h
  have := congrArg Finset.card h
  simp only [Finset.card_singleton,Finset.card_univ] at this
  omega
lemma pair_complement_nonempty (hk : 3 ≤ Fintype.card I) (i j : I) :
    (({i,j} : Finset I)ᶜ).Nonempty := by
  apply Finset.card_pos.mp
  have hc := Finset.card_compl ({i,j} : Finset I)
  have hp : ({i,j} : Finset I).card ≤ 2 := by
    by_cases h : i = j
    · simp [h]
    · simp [Finset.card_pair h]
  omega
noncomputable def singletonSplit (hk : 3 ≤ Fintype.card I) (i : I) : ComplementSplit ({i} : Finset I) := by
  have hi : (({i} : Finset I)ᶜ).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_compl ({i} : Finset I)
    simp only [Finset.card_singleton] at hc
    omega
  let j := hi.choose
  have hj : j ∉ ({i} : Finset I) := Finset.mem_compl.mp hi.choose_spec
  exact ComplementSplit.singleton {i} (Finset.singleton_nonempty i) j hj
    (by simpa only [Finset.singleton_union] using pair_complement_nonempty hk i j)

abbrev pairPartition (hk : 3 ≤ Fintype.card I) (j t : I) (hjt : j ≠ t) : TriplePartition I :=
  (ComplementSplit.singleton {j} (Finset.singleton_nonempty j) t
    (by simpa only [Finset.mem_singleton] using Ne.symm hjt)
    (by simpa only [Finset.singleton_union] using pair_complement_nonempty hk j t)).partition.swapPB.swapAB

lemma pairPartition_P (hk : 3 ≤ Fintype.card I) (j t : I) (hjt : j ≠ t) :
    (pairPartition hk j t hjt).P = ({j,t} : Finset I)ᶜ := rfl
lemma pairPartition_A (hk : 3 ≤ Fintype.card I) (j t : I) (hjt : j ≠ t) :
    (pairPartition hk j t hjt).A = ({j} : Finset I) := rfl
lemma pairPartition_B (hk : 3 ≤ Fintype.card I) (j t : I) (hjt : j ≠ t) :
    (pairPartition hk j t hjt).B = ({t} : Finset I) := rfl
end

section
open MeasureTheory
open scoped BigOperators
variable {I Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

def circleComplete (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (j : I) (y : Y) : Circle := if h : j = i then f y else (a ⟨j,by simpa using h⟩ y)⁻¹

omit [MeasurableSpace Y] in
lemma circleComplete_self (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle) :
    circleComplete i f a i = f := by funext y; simp [circleComplete]

lemma measurable_circleComplete (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (hf : Measurable f) (ha : ∀ j, Measurable (a j)) (j : I) : Measurable (circleComplete i f a j) := by
  unfold circleComplete
  by_cases h : j = i
  · simpa only [dite_eq_left h] using hf
  · simp only [dite_eq_right h]
    exact measurable_inv.comp (ha ⟨j,by simpa using h⟩)

lemma prod_complement (i : I) (g : I → Circle) :
    (∏ j, g j) = g i * ∏ j : ↥(({i} : Finset I)ᶜ), g j := by
  rw [Fintype.prod_eq_mul_prod_compl i g,Finset.prod_coe_sort]

omit [MeasurableSpace Y] in
lemma circleComplete_prod (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (y : I → Y) (c : Circle) (h : f (y i) = c * ∏ j, a j (y j)) :
    ∏ j, circleComplete i f a j (y j) = c := by
  rw [prod_complement i,circleComplete_self]
  have ht (j : ↥(({i} : Finset I)ᶜ)) : circleComplete i f a j (y j) = (a j (y j))⁻¹ := by
    have hj : (j : I) ≠ i := fun h => (Finset.mem_compl.mp j.property) (Finset.mem_singleton.mpr h)
    simp only [circleComplete,dite_eq_right hj]
  simp only [ht,Finset.prod_inv_distrib,h,mul_assoc,mul_inv_cancel,mul_one]

lemma prod_equation_solve (i : I) (g : I → Circle) (c : Circle) (h : ∏ j, g j = c) :
    g i = c * ∏ j : ↥(({i} : Finset I)ᶜ), (g j)⁻¹ := by
  rw [Finset.prod_inv_distrib,←h,prod_complement i,mul_assoc,mul_inv_cancel,mul_one]
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma prod_pair_solve (j t : I) (hjt : j ≠ t) (g : I → Circle) (c : Circle)
    (h : ∏ s, g s = c) :
    (g t)⁻¹ = c⁻¹ * (∏ s : ↥(({j,t} : Finset I)ᶜ), g s) * g j := by
  have ht : (g j * g t) * (∏ s : ↥(({j,t} : Finset I)ᶜ), g s) = c := by
    rw [Finset.prod_coe_sort, ←Finset.prod_pair hjt, Finset.prod_mul_prod_compl]
    exact h
  rw [←ht]
  simp [mul_inv_rev,mul_assoc,mul_comm,mul_left_comm]
end
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma raw_row_membership_transfer (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      (circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f j) (hf j) ∈
        rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) ↔
      circleLp (M.ownKernel 0 (plane 0 0 t (plane 1 0 a e))) (f t) (hf t) ∈
        rawSlotActive M a (M.ownKernel 0 (plane 0 0 t (plane 1 0 a e))) (plane 1 (Fin.last 1) t e)) := by
  have hI : 2 ≤ Fintype.card I := by omega
  let s := singletonSplit hk a
  let rows := s.partition.swapPA
  let cols := pairPartition hk j t hjt
  filter_upwards [grouped_row_membership_transfer M hM rows cols 0,
    columnActive_mixed_slot M hM hI a j (singleton_proper hI j) s,
    columnActive_mixed_slot M hM hI a t (singleton_proper hI t) s,
    singleton_collapse_preserving M hM hI a j,
    singleton_collapse_preserving M hM hI a t,
    row_marginal_fibre M hM hI a] with e he hj ht hmj hmt hr
  intro f hf c hc
  rw [hj _ hmj,ht _ hmt,circleLp_pull,circleLp_pull]
  let r : (cols.P → rows.A → Arr I M.Y 0) → Circle :=
    fun z => c⁻¹ * ∏ i : cols.P, f i (z i ⟨a,Finset.mem_singleton_self a⟩)
  have hmr : Measurable r := measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    (hf i).comp ((measurable_pi_apply _).comp (measurable_pi_apply i)))
  apply he (f j ∘ collapseCell M a j) (f t ∘ collapseCell M a t) r
    ((hf j).comp (collapseCell M a j).measurable) ((hf t).comp (collapseCell M a t).measurable) hmr
  filter_upwards [hr.quasiMeasurePreserving.ae hc] with y hy
  exact prod_pair_solve j t hjt (fun i => f i (plane 0 0 i (plane 1 0 a y))) c hy
end ArrayObjects.Object.Rolled
end

section
open scoped InnerProductSpace
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
lemma projection_transport (E : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (C : Submodule ℂ K)
    [D.HasOrthogonalProjection] [C.HasOrthogonalProjection]
    (h : ∀ v, v ∈ D ↔ E v ∈ C) (v : H) :
    E (D.starProjection v) = C.starProjection (E v) := by
  have he : D.map E.toLinearEquiv.toLinearMap = C := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (h v).mp hv
    · intro hw
      exact ⟨E.symm w,(h _).mpr (by simpa using hw),E.apply_symm_apply w⟩
  have hh := Submodule.starProjection_map_apply E D (E v)
  simpa only [he, E.symm_apply_apply] using hh.symm
lemma binary_projection_transport (E : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (C : Submodule ℂ K)
    [D.HasOrthogonalProjection] [C.HasOrthogonalProjection]
    (h : ∀ v, v ∈ D ↔ E v ∈ C) (v : H)
    (hb : C.starProjection (E v) = 0 ∨ C.starProjection (E v) = E v) :
    D.starProjection v = 0 ∨ D.starProjection v = v := by
  rw [←projection_transport E D C h] at hb
  rcases hb with h0 | h1
  · exact Or.inl (E.injective (h0.trans E.map_zero.symm))
  · exact Or.inr (E.injective h1)
end

namespace JoiningOperator
open MeasureTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {x : Ω → X} {y : Ω → Y}
lemma circleLp_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (f : X → Circle) (g : Y → Circle) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ ω ∂μ, f (x ω) = g (y ω)) :
    operator hx hy (circleLp ρ g hg) = circleLp ν f hf := by
  have hp : pull hx (circleLp ν f hf) = pull hy (circleLp ρ g hg) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ν f hf) hx,
      Lp.coeFn_compMeasurePreserving (circleLp ρ g hg) hy,
      hx.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ g hg),he] with ω h1 h2 h3 h4 h5
    exact (h1.trans h3).trans ((congrArg ((↑) : Circle → ℂ) h5).trans (h2.trans h4).symm)
  change (pull hx).adjoint (pull hy (circleLp ρ g hg)) = _
  rw [←hp]
  exact congrArg (fun A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => A (circleLp ν f hf)) (pull_adjoint_pull hx)
end JoiningOperator

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma prod_complement_split (i : I) (s : ComplementSplit ({i} : Finset I)) (g : I → Circle) :
    (∏ j : ↥(({i} : Finset I)ᶜ), g j) = (∏ j : s.A, g j) * ∏ j : s.B, g j := by
  rw [Finset.prod_coe_sort,Finset.prod_coe_sort,Finset.prod_coe_sort,←s.union_eq,
    Finset.prod_union s.disjointAB]
end
namespace ArrayObjects.Object.Rolled

section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma raw_tuple_active (i : I) (p : Arr I M.U 1) (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν]
    (hm : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν)
    (f : I → Arr I M.Y 0 → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f j (plane 0 0 j y) = c) :
    circleLp ν (f i) (hf i) ∈ rawSlotActive M i ν p := by
  rw [rawSlotActive_eq M i ν p hm]
  apply Submodule.le_topologicalClosure
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → Circle :=
    fun z => c * ∏ j : ↥(({i} : Finset I)ᶜ), (f j (z j))⁻¹
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun j _ =>
    ((hf j).comp (measurable_pi_apply j)).inv)
  refine ⟨circleLp ((M.ownKernel 1 p).map (slotRest M i)) g hg,?_⟩
  apply JoiningOperator.circleLp_operator hm (MeasurePreserving.mk (measurable_slotRest M i) rfl)
    (f i) g (hf i) hg
  exact he.mono fun y hy => prod_equation_solve i (fun j => f j (plane 0 0 j y)) c hy

lemma raw_tuple_rowSplitExact (a j : I) (s : ComplementSplit ({j} : Finset I))
    (e : Arr I M.U 2)
    (hr : MeasurePreserving (plane 1 0 a) (M.ownKernel 2 e) (M.ownKernel 1 (plane 1 0 a e)))
    (f : I → Arr I M.Y 0 → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) :
    circleLp (cellLaw M {a} {j} 0 e) (f j ∘ collapseCell M a j)
      ((hf j).comp (collapseCell M a j).measurable) ∈ rowSplitExact M {a} {j} s 0 e := by
  let g : (s.A → ({a} : Finset I) → Arr I M.Y 0) → Circle :=
    fun z => c * ∏ i : s.A, (f i (z i ⟨a,Finset.mem_singleton_self a⟩))⁻¹
  let h : (s.B → ({a} : Finset I) → Arr I M.Y 0) → Circle :=
    fun z => ∏ i : s.B, (f i (z i ⟨a,Finset.mem_singleton_self a⟩))⁻¹
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    ((hf i).comp ((measurable_pi_apply (⟨a,Finset.mem_singleton_self a⟩ : ({a} : Finset I))).comp (measurable_pi_apply i))).inv)
  have hh : Measurable h := Finset.measurable_prod _ fun i _ =>
    ((hf i).comp ((measurable_pi_apply (⟨a,Finset.mem_singleton_self a⟩ : ({a} : Finset I))).comp (measurable_pi_apply i))).inv
  apply JoiningOperator.circle_mem_splitExact _ _ _ _ _ (f j ∘ collapseCell M a j) g h
    ((hf j).comp (collapseCell M a j).measurable) hg hh
  filter_upwards [hr.quasiMeasurePreserving.ae he] with y hy
  have ht := prod_equation_solve j (fun i => f i (plane 0 0 i (plane 1 0 a y))) c hy
  rw [prod_complement_split j s (fun i => (f i (plane 0 0 i (plane 1 0 a y)))⁻¹)] at ht
  change f j (plane 0 0 j (plane 1 0 a y)) =
    (c * ∏ i : s.A, (f i (plane 0 0 i (plane 1 0 a y)))⁻¹) *
      ∏ i : s.B, (f i (plane 0 0 i (plane 1 0 a y)))⁻¹
  simpa only [mul_assoc] using ht

lemma raw_row_line_projection (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      let ν := M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))
      let v := circleLp ν (f j) (hf j)
      (rawSlotActive M a ν (plane 1 (Fin.last 1) j e)).starProjection v = 0 ∨
      (rawSlotActive M a ν (plane 1 (Fin.last 1) j e)).starProjection v = v := by
  have hI : 2 ≤ Fintype.card I := by omega
  let s := singletonSplit hk a
  let t := singletonSplit hk j
  filter_upwards [grouped_row_line_projection M hM {a} {j} s t 0,
    columnActive_mixed_slot M hM hI a j (singleton_proper hI j) s,
    singleton_collapse_preserving M hM hI a j,row_marginal_fibre M hM hI a]
    with e hbin hcol hmp hr
  intro f hf c he
  have hfex := raw_tuple_rowSplitExact M a j t e hr f hf c he
  have hb := hbin _ hfex
  rw [←circleLp_pull hmp (f j) (hf j)] at hb
  exact binary_projection_transport (JoiningOperator.pullEquiv (collapseCell M a j) hmp)
    _ _ (hcol _ hmp) _ hb
end

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawExactCone (i : I) (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    Set (Lp ℂ 2 ν) := {v | ∃ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j))
      (c : Circle) (d : ℂ), v = d • circleLp ν (f i) (hf i) ∧
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f j (plane 0 0 j y) = c}

omit [DecidableEq I] in
lemma rawExactCone_smul (i : I) (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν]
    (p : Arr I M.U 1) (c : ℂ) (v : Lp ℂ 2 ν) (hv : v ∈ rawExactCone M i ν p) :
    c • v ∈ rawExactCone M i ν p := by
  obtain ⟨f,hf,a,d,rfl,he⟩ := hv
  exact ⟨f,hf,a,c*d,by rw [smul_smul],he⟩

omit [DecidableEq I] in
lemma oneRow_single_column (a j : I) (y : Arr I M.Y 2) :
    oneRow M {j} 0 a y = fun _ => plane 0 0 a (plane 1 (Fin.last 1) j y) := by
  funext t
  have ht : (t : I) = j := Finset.mem_singleton.mp t.property
  simp only [oneRow,ht]
  exact (congrFun (plane_first_last M 0 a j) y).symm

lemma fullExact_raw_column (a j : I) (e : Arr I M.U 2)
    (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν]
    (hm : MeasurePreserving (collapseCell M a j) (cellLaw M {a} {j} 0 e) ν)
    (hc : MeasurePreserving (plane 1 (Fin.last 1) j) (M.ownKernel 2 e)
      (M.ownKernel 1 (plane 1 (Fin.last 1) j e)))
    (v : Lp ℂ 2 ν) (hv : JoiningOperator.pull hm v ∈ fullExact M {a} {j} 0 e) :
    v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e) := by
  obtain ⟨f,hf,d,he,_,b,c,hb,hprod⟩ := hv
  let g : Arr I M.Y 0 → Circle := f ∘ (collapseCell M a j).symm
  have hg : Measurable g := hf.comp (collapseCell M a j).symm.measurable
  have hvg : v = d • circleLp ν g hg := by
    apply (JoiningOperator.pullEquiv (collapseCell M a j) hm).injective
    change JoiningOperator.pull hm v = JoiningOperator.pull hm (d • circleLp ν g hg)
    rw [map_smul,circleLp_pull]
    have hgf : g ∘ collapseCell M a j = f := by
      funext z
      exact congrArg f ((collapseCell M a j).symm_apply_apply z)
    simpa only [hgf] using he
  let B : ↥(({a} : Finset I)ᶜ) → Arr I M.Y 0 → Circle := fun t y => b t (fun _ => y)
  have hB (t) : Measurable (B t) := (hb t).comp (Measurable.of_eval fun _ => measurable_id)
  refine ⟨circleComplete a g B,measurable_circleComplete a g B hg hB,c,d,?_,?_⟩
  · simpa only [circleComplete_self] using hvg
  · rw [←hc.map_eq]
    apply ae_map_descent _ hc.measurable
    filter_upwards [hprod] with y hy
    apply circleComplete_prod a g B _ c
    have hcell : (collapseCell M a j).symm (plane 0 0 a (plane 1 (Fin.last 1) j y)) =
        cells M {a} {j} 0 y := by
      apply (collapseCell M a j).injective
      rw [(collapseCell M a j).apply_symm_apply]
      exact (congrFun (collapse_cell_column M a j) y).symm
    simpa only [g,Function.comp_apply,hcell,B,oneRow_single_column] using hy

lemma raw_row_active_to_column_exact (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      let ν := M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))
      let v := circleLp ν (f j) (hf j)
      v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) →
      v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e) := by
  let s := singletonSplit hk a
  let t := singletonSplit hk j
  have hI : 2 ≤ Fintype.card I := by omega
  filter_upwards [grouped_full_row_column_exact M hM {a} {j} s t 0,
    row_marginal_fibre M hM hI a,column_marginal_fibre M hI j,
    singleton_collapse_preserving M hM hI a j,
    columnActive_mixed_slot M hM hI a j (singleton_proper hI j) s]
    with e hfull hr hc hm hcol
  intro f hf c he
  dsimp only
  intro hv
  apply fullExact_raw_column M a j e _ hm hc
  apply hfull
  · intro t'
    rw [circleLp_pull]
    exact raw_tuple_rowSplitExact M a j t' e hr f hf c he
  · exact (hcol _ hm _).mp hv

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma HilbertCode.encode_injective {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ] (u : U) :
    Function.Injective (HilbertCode.encode (κ := κ) u) := by
  intro v w h
  apply distance_code_injective (hilbertTests_dense (κ u))
  funext n
  exact congrArg (fun a : HilbertCode κ => a.code n) h

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

def exactCodeVectors (p : P) (i : I) : Set (Lp ℂ 2 (κ (u p i))) :=
  {v | ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = HilbertCode.encode (u p i) v}

def exactCodeSpan (p : P) (i : I) : Submodule ℂ (Lp ℂ 2 (κ (u p i))) :=
  (Submodule.span ℂ (exactCodeVectors κ Λ u p i)).topologicalClosure

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma exactCodeSpan_congr_kernel (Λ' : Kernel P (I → Y)) [IsMarkovKernel Λ']
    (p : P) (i : I) (he : Λ p = Λ' p) :
    exactCodeSpan κ Λ u p i = exactCodeSpan κ Λ' u p i := by
  have hs : exactCodeVectors κ Λ u p i = exactCodeVectors κ Λ' u p i := by
    ext v
    simp only [exactCodeVectors, exactCodeSet, exactCodeMean, Set.mem_ofPred_eq, he]
  unfold exactCodeSpan
  rw [hs]

omit [DecidableEq I] in
lemma exactCircle_mem_codeSpan (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c) (d : ℂ) :
    d • circleLp (κ (u p i)) (f i) (hf i) ∈ exactCodeSpan κ Λ u p i := by
  obtain ⟨a,b,ha,hb⟩ := normalized_exact_codes κ Λ u p hm f hf c he
  have hv : b i • circleLp (κ (u p i)) (f i) (hf i) ∈ exactCodeSpan κ Λ u p i :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,ha,(hb i).2⟩)
  have hn : b i ≠ 0 := by intro hz; simpa only [hz,norm_zero,zero_ne_one] using (hb i).1
  convert (exactCodeSpan κ Λ u p i).smul_mem (d * (b i)⁻¹) hv using 1
  rw [smul_smul,mul_assoc,inv_mul_cancel₀ hn,mul_one]

omit [DecidableEq I] in
lemma exactVector_circle_tuple (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    {v : Lp ℂ 2 (κ (u p i))} (hv : v ∈ exactCodeVectors κ Λ u p i) :
    ∃ (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      v = circleLp (κ (u p i)) (f i) (hf i) ∧ ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c := by
  obtain ⟨a,ha,hv⟩ := hv
  obtain ⟨c,hc⟩ := exactCode_circle_tuple κ Λ u hm ha
  refine ⟨fun j => HilbertCode.circleRep (a j),
    fun j => HilbertCode.measurable_circleRep_fixed (a j),c,?_,hc⟩
  dsimp only
  simp only [hv]
  have hq : HilbertCode.IsUnimodular (HilbertCode.encode (u p i) v) := by
    rw [←hv]
    exact (ha.2.1 i).2
  exact (HilbertCode.decode_encode (u p i) v).symm.trans
    (HilbertCode.circleLp_circleRep (HilbertCode.encode (u p i) v) hq).symm

variable [StandardBorelSpace P] [StandardBorelSpace U]

lemma exactCodeSpan_sections (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    ∃ s : ℕ → ∀ p, Lp ℂ 2 (κ (u p i)), (∀ n, MeasurableSection (s n)) ∧
      ∀ p, exactCodeSpan κ Λ u p i =
        (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure := by
  obtain ⟨D,a,_,ha,hbase,hmem,hzero,hcover⟩ := exactCode_sections κ Λ u hu hk hm hind
  let s : ℕ → ∀ p, Lp ℂ 2 (κ (u p i)) := fun n p =>
    HilbertCode.atBase (a n p i) (u p i) (hbase n p i)
  have hs (n p) : HilbertCode.encode (u p i) (s n p) = a n p i := HilbertCode.encode_atBase _ _ _
  refine ⟨s,?_,?_⟩
  · intro n
    change Measurable (fun p => HilbertCode.encode (u p i) (s n p))
    simp only [hs]
    exact (measurable_pi_apply i).comp (ha n)
  · intro p
    apply le_antisymm
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_le.mpr
      rintro v ⟨b,hb,hv⟩
      obtain ⟨n,_,hn⟩ := hcover (p,b) hb
      have he : s n p = v := by
        apply HilbertCode.encode_injective (u p i)
        rw [hs,hn]
        exact hv
      exact Submodule.subset_span ⟨n,he⟩
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      by_cases hp : p ∈ D n
      · exact Submodule.subset_span ⟨a n p,hmem n p hp,(hs n p).symm⟩
      · have he : s n p = 0 := by
          apply HilbertCode.encode_injective (u p i)
          rw [hs,hzero n p hp]
        dsimp only
        rw [he]
        exact Submodule.zero_mem _
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] in
lemma canonical_smul_exact_tuple (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (v : Lp ℂ 2 (κ (u p i))) (hv : RayCanonical (hilbertTests (κ (u p i))) v) (hn : ‖v‖ = 1)
    (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle) (d : ℂ)
    (he : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c)
    (hvd : v = d • circleLp (κ (u p i)) (f i) (hf i)) :
    ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧
      a i = HilbertCode.encode (u p i) v := by
  obtain ⟨a,b,ha,hb⟩ := normalized_exact_codes κ Λ u p hm f hf c he
  have hdn : ‖d‖ = 1 := by
    rw [hvd,norm_smul,circleLp_norm,mul_one] at hn
    exact hn
  let w := b i • circleLp (κ (u p i)) (f i) (hf i)
  have hc : RayCanonical (hilbertTests (κ (u p i))) w := by
    have h := (ha.2.1 i).1
    change HilbertCode.IsCanonical (a i) at h
    rw [(hb i).2] at h
    change RayCanonical (hilbertTests (κ (u p i))) (HilbertCode.decode (HilbertCode.encode (u p i) w)) at h
    simpa only [HilbertCode.decode_encode] using h
  have hb0 : b i ≠ 0 := by
    intro hz
    simpa only [hz,norm_zero,zero_ne_one] using (hb i).1
  have heq : v = (d * (b i)⁻¹) • w := by
    dsimp only [w]
    rw [smul_smul,mul_assoc,inv_mul_cancel₀ hb0,mul_one]
    exact hvd
  have hwn : ‖d * (b i)⁻¹‖ = 1 := by rw [norm_mul,norm_inv,hdn,(hb i).1,inv_one,mul_one]
  have hwv := rayCanonical_unique hv hc hwn heq
  exact ⟨a,ha,(hb i).2.trans (congrArg (HilbertCode.encode (u p i)) hwv.symm)⟩
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [retained11 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawLineGraph (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) :
    I → Set (Arr I M.U 1 × HilbertCode (M.ownKernel 0)) := fun i =>
  {pz | ∃ a : I → HilbertCode (M.ownKernel 0),
    (pz.1,a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) ∧ a i = pz.2}

include retained11 in
lemma rawCode_of_cone (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (p : Arr I M.U 1) (i : I) (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (q : HilbertCode (M.ownKernel 0)) (hb : q.base = tupleParameter M p i)
    (hc : q.IsCanonical) (hu : q.IsUnimodular)
    (he : circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
      (HilbertCode.measurable_circleRep_fixed q) ∈
      rawExactCone M i (M.ownKernel 0 (tupleParameter M p i)) p) :
    (p,q) ∈ rawLineGraph M Λ i := by
  let _ := retained11
  have hq : HilbertCode.encode (tupleParameter M p i)
      (circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
        (HilbertCode.measurable_circleRep_fixed q)) = q := by
    rw [←hb,HilbertCode.circleLp_circleRep q hu,HilbertCode.encode_decode]
  have hcan : RayCanonical (hilbertTests (M.ownKernel 0 (tupleParameter M p i)))
      (circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
        (HilbertCode.measurable_circleRep_fixed q)) := by
    rw [←hq] at hc
    change RayCanonical (hilbertTests (M.ownKernel 0 (tupleParameter M p i)))
      (HilbertCode.decode (HilbertCode.encode (tupleParameter M p i) _)) at hc
    simpa only [HilbertCode.decode_encode] using hc
  obtain ⟨f,hf,c,d,hd,he⟩ := he
  have he' : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c := by
    rw [hL,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
    exact ae_map_descent _ (measurable_rawTuple M) he
  obtain ⟨a,ha,hai⟩ := canonical_smul_exact_tuple (M.ownKernel 0) Λ (tupleParameter M)
    p i hm _ hcan (circleLp_norm _ _ _) f hf c d he' hd
  exact ⟨a,ha,hai.trans hq⟩
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P Ω X Y U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]
  [retained12 : StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (hx : Measurable x) (hy : Measurable y)

def joiningPosterior : Kernel (P × X) Y := (Λ.map (fun ω => (x ω,y ω))).condKernel
instance : IsMarkovKernel (joiningPosterior Λ x y) := inferInstanceAs (IsMarkovKernel (Λ.map (fun ω => (x ω,y ω))).condKernel)

omit [StandardBorelSpace Ω] in
include hx hy in
lemma joiningPosterior_conditional (p : P) :
    HasCondDistrib y x ((joiningPosterior Λ x y).sectR p) (Λ p) := by
  let K := Λ.map (fun ω => (x ω,y ω))
  let : IsMarkovKernel K := Kernel.IsMarkovKernel.map _ (hx.prodMk hy)
  have h := congrArg (fun K : Kernel P (X × Y) => K p) (Kernel.disintegrate K K.condKernel)
  rw [Kernel.compProd_apply_eq_compProd_sectR,Kernel.fst_apply,Kernel.map_apply _ (hx.prodMk hy)] at h
  refine ⟨(hx.prodMk hy).aemeasurable,?_⟩
  rw [Measure.map_map measurable_fst (hx.prodMk hy)] at h
  exact h.symm

variable (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)
  (f : Y → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B)

omit [StandardBorelSpace Ω] in
include hf B hB in
lemma posterior_memLp (p : P) :
    MemLp (fun a => ∫ z, f z ∂joiningPosterior Λ x y (p,a)) 2 (κ (u p)) := by
  refine MemLp.of_bound (by
    exact (hf.stronglyMeasurable.integral_kernel (κ := joiningPosterior Λ x y)).comp_measurable
      measurable_prodMk_left |>.aestronglyMeasurable) B ?_
  exact Filter.Eventually.of_forall fun a => by
    simpa only [probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ := joiningPosterior Λ x y (p,a))
        (Filter.Eventually.of_forall hB))

def posteriorVector (p : P) : Lp ℂ 2 (κ (u p)) :=
  (posterior_memLp Λ x y κ u f hf B hB p).toLp _

include retained12 in
lemma measurableSection_posteriorVector (hu : Measurable u) :
    MeasurableSection (posteriorVector Λ x y κ u f hf B hB) := by
  let _ := retained12
  exact measurable_hilbert_encode u hu _ (fun pa => ∫ z, f z ∂joiningPosterior Λ x y pa)
    (hf.stronglyMeasurable.integral_kernel (κ := joiningPosterior Λ x y)).measurable
    (fun p => (posterior_memLp Λ x y κ u f hf B hB p).coeFn_toLp)

lemma posteriorVector_eq_operator (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) :
    posteriorVector Λ x y κ u f hf B hB p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl)
        ((MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f) := by
  let g := (MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f
  have he : (fun ω => g (y ω)) =ᵐ[Λ p] (fun ω => f (y ω)) :=
    (MeasurePreserving.mk hy rfl).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp _)
  have hl : Integrable (fun ω => f (y ω)) (Λ p) :=
    (MemLp.of_bound (hf.comp hy).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun ω => hB (y ω))) : MemLp (fun ω => f (y ω)) 2 (Λ p)).integrable (by norm_num)
  have hop := JoiningOperator.operator_ae_eq_condExp hxm (MeasurePreserving.mk hy rfl) g
  have hce := JoiningOperator.condExp_of_kernel hxm.measurable (joiningPosterior_conditional Λ x y hxm.measurable hy p)
    f hf.stronglyMeasurable hl
  have hop' : (fun ω => JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g (x ω)) =ᵐ[Λ p]
      (fun ω => ∫ z, f z ∂joiningPosterior Λ x y (p,x ω)) :=
    hop.trans ((condExp_congr_ae he).trans hce)
  have hh : ∀ᵐ z ∂(Λ p).map x, posteriorVector Λ x y κ u f hf B hB p z =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g z := by
    apply ae_map_descent _ hxm.measurable
    filter_upwards [hxm.quasiMeasurePreserving.ae_eq_comp
      (posterior_memLp Λ x y κ u f hf B hB p).coeFn_toLp,hop'] with ω hv ho
    exact hv.trans ho.symm
  rw [hxm.map_eq] at hh
  exact Lp.ext hh
end

section
open MeasureTheory ProbabilityTheory Set
variable {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
lemma hilbertTestFunction_bounded (t : HilbertTestKey Y) :
    ∃ B : ℝ, ∀ y, ‖hilbertTestFunction t y‖ ≤ B := by
  induction t with
  | nil => exact ⟨0,fun _ => by simp [hilbertTestFunction]⟩
  | cons p t ih =>
    obtain ⟨B,hB⟩ := ih
    refine ⟨‖(p.1.1 : ℂ) + p.1.2 * Complex.I‖ + B,fun y => ?_⟩
    change ‖((p.1.1 : ℂ) + p.1.2 * Complex.I) * (p.2.val.indicator (fun _ => (1 : ℂ))) y + hilbertTestFunction t y‖ ≤ _
    apply (norm_add_le _ _).trans
    apply add_le_add _ (hB y)
    by_cases h : y ∈ p.2.val
    · simp only [Set.indicator_of_mem h,mul_one,le_refl]
    · simp only [Set.indicator_of_notMem h,mul_zero,norm_zero]
      exact norm_nonneg _
variable {P Ω X U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace U] [StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)

def posteriorTest (n : ℕ) (p : P) : Lp ℂ 2 (κ (u p)) :=
  posteriorVector Λ x y κ u (hilbertTestFunction (hilbertTestKeys n))
    (hilbertTestFunction_measurable _) (hilbertTestFunction_bounded _).choose
    (hilbertTestFunction_bounded _).choose_spec p

lemma measurableSection_posteriorTest (hu : Measurable u) (n : ℕ) :
    MeasurableSection (posteriorTest Λ x y κ u n) :=
  measurableSection_posteriorVector Λ x y κ u _ (hilbertTestFunction_measurable _)
    (hilbertTestFunction_bounded (hilbertTestKeys n)).choose
    (hilbertTestFunction_bounded (hilbertTestKeys n)).choose_spec hu

lemma posteriorTest_eq_operator (hy : Measurable y) (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) (n : ℕ) :
    posteriorTest Λ x y κ u n p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) (hilbertTests ((Λ p).map y) n) := by
  rw [posteriorTest,posteriorVector_eq_operator Λ x y hy κ u _ _ _ _ p hxm]
  congr 1
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (hilbertTestVector_coe _ _).symm

lemma operator_range_le_iff_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) (S : Submodule ℂ B) (hS : IsClosed (S : Set B)) :
    (LinearMap.range L.toLinearMap).topologicalClosure ≤ S ↔ ∀ n, L (v n) ∈ S := by
  constructor
  · intro h n
    exact h (Submodule.le_topologicalClosure _ ⟨v n,rfl⟩)
  · intro h
    apply Submodule.topologicalClosure_minimal _ _ hS
    rintro _ ⟨a,rfl⟩
    exact hv.induction_on a (hS.preimage L.continuous) h
end

section
open MeasureTheory ProbabilityTheory
section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma operator_range_eq_span_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) :
    (LinearMap.range L.toLinearMap).topologicalClosure =
      (Submodule.span ℂ (Set.range (fun n => L (v n)))).topologicalClosure := by
  apply le_antisymm
  · apply (operator_range_le_iff_tests L v hv _ (Submodule.isClosed_topologicalClosure _)).mpr
    intro n
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact ⟨v n,rfl⟩

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
lemma MeasurableSection.circle (u : P → U) (hu : Measurable u) (f : P → Y → Circle)
    (hf : Measurable (Function.uncurry f)) :
    MeasurableSection (fun p => circleLp (κ (u p)) (f p)
      (hf.comp (measurable_const.prodMk measurable_id))) := by
  apply measurable_hilbert_encode u hu _ (fun py : P × Y => (f py.1 py.2 : ℂ))
    (measurable_subtype_coe.comp hf)
  intro p
  exact circleLp_coe _ _ _

lemma MeasurableSection.comp {Q : Type*} [MeasurableSpace Q] {u : P → U}
    {v : ∀ p, Lp ℂ 2 (κ (u p))} (hv : MeasurableSection v) (g : Q → P) (hg : Measurable g) :
    MeasurableSection (fun q => v (g q)) := Measurable.comp hv hg
end
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rawSlotTest (i : I) (n : ℕ) (p : Arr I M.U 1) : Lp ℂ 2 (M.ownKernel 0 (plane 0 0 i p)) :=
  posteriorTest (M.ownKernel 1) (plane 0 0 i) (slotRest M i) (M.ownKernel 0) (plane 0 0 i) n p

def rawSlotTestSpan (i : I) (p : Arr I M.U 1) : Submodule ℂ (Lp ℂ 2 (M.ownKernel 0 (plane 0 0 i p))) :=
  (Submodule.span ℂ (Set.range (fun n => rawSlotTest M i n p))).topologicalClosure

lemma measurableSection_rawSlotTest (i : I) (n : ℕ) : MeasurableSection (rawSlotTest M i n) :=
  measurableSection_posteriorTest _ _ _ _ _ (measurable_plane _ _ _) n

lemma rawSlotTest_eq_operator (i : I) (p : Arr I M.U 1)
    (hp : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p))) (n : ℕ) :
    rawSlotTest M i n p = JoiningOperator.operator hp
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n) :=
  posteriorTest_eq_operator _ _ _ _ _ (measurable_slotRest M i) p hp n

lemma rawSlotActive_eq_testSpan (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ p ∂M.parameterLaw 1,
      rawSlotActive M i (M.ownKernel 0 (plane 0 0 i p)) p = rawSlotTestSpan M i p := by
  have hm := ConditionalFibres.marginal (measurable_plane 0 0 i)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i)
  filter_upwards [hm] with p hp
  have hp' : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p)) := hp
  rw [rawSlotActive_eq M i _ p hp',rawSlotTestSpan]
  have ht : (fun n => rawSlotTest M i n p) = (fun n => JoiningOperator.operator hp'
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n)) :=
    funext (rawSlotTest_eq_operator M i p hp')
  rw [ht]
  exact operator_range_eq_span_tests _ _ (hilbertTests_dense _)

variable {P : Type*} [MeasurableSpace P]
lemma measurableSet_rawSlot_mem (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) :
    MeasurableSet {pq : P × Arr I M.U 1 | circleLp (M.ownKernel 0 (plane 0 0 i pq.2)) (f pq.1)
      (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i pq.2} := by
  apply measurableSet_section_mem_span ((measurable_plane _ _ _).comp measurable_snd)
    (fun n => (measurableSection_rawSlotTest M i n).comp Prod.snd measurable_snd)
  exact MeasurableSection.circle _ ((measurable_plane _ _ _).comp measurable_snd)
    (fun pq => f pq.1) (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

def rawSlotIndicator (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) (p : P) (q : Arr I M.U 1) : Bool := by
  classical
  exact decide (circleLp (M.ownKernel 0 (plane 0 0 i q)) (f p)
    (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i q)

lemma measurable_rawSlotIndicator (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) : Measurable (Function.uncurry (rawSlotIndicator M i f hf)) := by
  classical
  change Measurable (fun pq : P × Arr I M.U 1 => decide
    (circleLp (M.ownKernel 0 (plane 0 0 i pq.2)) (f pq.1)
      (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i pq.2))
  apply measurable_to_bool
  simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using
    measurableSet_rawSlot_mem M i f hf

lemma rawSlotIndicator_eq_true_iff (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) (p : P) (q : Arr I M.U 1) :
    rawSlotIndicator M i f hf p q = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 i q)) (f p)
        (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i q := by
  classical
  exact decide_eq_true_iff
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma independent_equal_indicators {f g : Ω → Bool}
    (hf : Measurable f) (hfg : IndepFun f g μ) (he : f =ᵐ[μ] g) :
    (∀ᵐ ω ∂μ, f ω = false) ∨ ∀ᵐ ω ∂μ, f ω = true := by
  have hi : IndepFun f f μ := hfg.congr Filter.EventuallyEq.rfl he.symm
  have hp := hi.measure_inter_preimage_eq_mul ({true} : Set Bool) ({true} : Set Bool)
    (measurableSet_singleton _) (measurableSet_singleton _)
  simp only [inter_self] at hp
  let p := μ (f ⁻¹' ({true} : Set Bool))
  have hfin : p ≠ ∞ := measure_ne_top _ _
  have hz : p = 0 ∨ p = 1 := by
    by_cases h : p = 0
    · exact Or.inl h
    · right
      apply (ENNReal.mul_right_inj h hfin).mp
      simpa only [p,mul_one] using hp.symm
  rcases hz with hz | ho
  · left
    have ha : ∀ᵐ ω ∂μ, ω ∉ f ⁻¹' ({true} : Set Bool) := by
      exact ae_iff.mpr (by simpa only [p,not_not,Set.ofPred_mem_eq] using hz)
    filter_upwards [ha] with ω hω
    cases h : f ω <;> simp_all
  · right
    exact (mem_ae_iff_prob_eq_one ((measurableSet_singleton true).preimage hf)).mpr ho
end

section
open MeasureTheory ProbabilityTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
lemma product_equal_positive_indicators (f : X → Bool) (g : Y → Bool)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ p ∂μ.prod ν, f p.1 = g p.2)
    (hp : μ {x | f x = true} ≠ 0) :
    (∀ᵐ x ∂μ, f x = true) ∧ ∀ᵐ y ∂ν, g y = true := by
  have h := independent_equal_indicators (hf.comp measurable_fst) (indepFun_prod hf hg) he
  have htrue : ∀ᵐ p ∂μ.prod ν, f p.1 = true := by
    rcases h with hz | ht
    · have hfalse : ∀ᵐ x ∂μ, f x = false := by
        rw [←(measurePreserving_fst (μ := μ) (ν := ν)).map_eq]
        exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hf measurable_const)).mpr hz
      apply False.elim
      apply hp
      simpa only [Bool.not_eq_false] using (ae_iff.mp hfalse)
    · exact ht
  constructor
  · rw [←(measurePreserving_fst (μ := μ) (ν := ν)).map_eq]
    exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hf measurable_const)).mpr htrue
  · rw [←(measurePreserving_snd (μ := μ) (ν := ν)).map_eq]
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun hg measurable_const)).mpr
    filter_upwards [htrue,he] with p hp he
    exact he ▸ hp

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace X] [StandardBorelSpace Y]
  {ρ : Measure Ω} [IsProbabilityMeasure ρ] {s : Ω → S} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel S X} {l : Kernel S Y} [IsMarkovKernel κ] [IsMarkovKernel l]
omit [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace X] in
lemma conditional_joint_ae_lift (hs : Measurable s) (hx : Measurable x)
    (hκ : HasCondDistrib x s κ ρ) {P : S → X → Prop}
    (hPm : MeasurableSet {p : S × X | P p.1 p.2})
    (hP : ∀ᵐ a ∂ρ.map s, ∀ᵐ b ∂κ a, P a b) : ∀ᵐ ω ∂ρ, P (s ω) (x ω) := by
  have h : ∀ᵐ p ∂(ρ.map s) ⊗ₘ κ, P p.1 p.2 := (Measure.ae_compProd_iff hPm).mpr hP
  rw [←hκ.map_eq] at h
  exact ae_of_ae_map (hs.prodMk hx).aemeasurable h

lemma conditional_equal_positive_indicators
    (hs : Measurable s) (hx : Measurable x) (hy : Measurable y)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) s (κ ×ₖ l) ρ)
    (f : S → X → Bool) (g : S → Y → Bool)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (he : ∀ᵐ ω ∂ρ, f (s ω) (x ω) = g (s ω) (y ω))
    (hp : ∀ᵐ a ∂ρ.map s, κ a {z | f a z = true} ≠ 0) :
    ∀ᵐ ω ∂ρ, f (s ω) (x ω) = true ∧ g (s ω) (y ω) = true := by
  have hd := conditional_ae_descent (κ := κ ×ₖ l)
    (P := fun a p => f a p.1 = g a p.2) hs (hx.prodMk hy) hκ he
  have ht : ∀ᵐ a ∂ρ.map s, ∀ᵐ p ∂(κ ×ₖ l) a, f a p.1 = true ∧ g a p.2 = true := by
    filter_upwards [hd,hp] with a ha hp
    rw [Kernel.prod_apply] at ha ⊢
    have h := product_equal_positive_indicators (f a) (g a)
      (hf.comp (measurable_const.prodMk measurable_id))
      (hg.comp (measurable_const.prodMk measurable_id)) ha hp
    exact (measurePreserving_fst.quasiMeasurePreserving.ae h.1).and
      (measurePreserving_snd.quasiMeasurePreserving.ae h.2)
  apply conditional_joint_ae_lift hs (hx.prodMk hy) hκ _ ht
  exact ((measurableSet_eq_fun (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    measurable_const).inter (measurableSet_eq_fun
      (hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) measurable_const))
end

section
open MeasureTheory ProbabilityTheory
variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} {z : Ω → Z}
  {κ : Kernel S Z} [IsSFiniteKernel κ]
lemma conditional_ae_lift (hs : Measurable s) (hz : Measurable z)
    (hκ : HasCondDistrib z s κ μ) {P : Z → Prop} (hPm : MeasurableSet {z | P z})
    (hP : ∀ᵐ a ∂μ.map s, ∀ᵐ b ∂κ a, P b) : ∀ᵐ ω ∂μ, P (z ω) := by
  have h : ∀ᵐ sb ∂(μ.map s) ⊗ₘ κ, P sb.2 :=
    (Measure.ae_compProd_iff (hPm.preimage measurable_snd)).mpr hP
  rw [←hκ.map_eq] at h
  exact ae_of_ae_map (hs.prodMk hz).aemeasurable h
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma parameterCoordinate_conditional (i : I) :
    HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
  ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib (by fun_prop) measurable_id.aemeasurable).symm⟩

omit [DecidableEq I] in
lemma coordinate_conditional_descent (i : I) {P : Arr I M.U 0 → Arr I M.U 1 → Prop}
    (hP : ∀ᵐ p ∂M.parameterLaw 1, P (plane 0 0 i p) p) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u, P u p := by
  have h := conditional_ae_descent (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hP
  rwa [M.parameterLaw_consistent 0 0 i] at h

lemma raw_diagonal_binary (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0,
    ∀ᵐ pq ∂(M.parameterCoordinateKernel i u).prod (M.parameterCoordinateKernel i u),
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v := by
  let P : Arr I M.U 0 → (Arr I M.U 1 × Arr I M.U 1) → Prop := fun u pq =>
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v
  have h := conditional_ae_descent (P := P)
    ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _))
    (M.diagonal_parameter_product hM (by omega) i) (raw_row_line_projection M hM hk i i)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simpa only [Kernel.prod_apply] using h

omit [DecidableEq I] in
lemma raw_coordinate_marginal (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) (M.ownKernel 0 u) := by
  exact coordinate_conditional_descent M i
    (ConditionalFibres.marginal (measurable_plane 0 0 i)
      (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i))

lemma raw_slot_mem_parameter_congr (i : I) (u v : Arr I M.U 0) (h : u = v)
    (p : Arr I M.U 1) (f : Arr I M.Y 0 → Circle) (hf : Measurable f) :
    (circleLp (M.ownKernel 0 u) f hf ∈ rawSlotActive M i (M.ownKernel 0 u) p) ↔
    (circleLp (M.ownKernel 0 v) f hf ∈ rawSlotActive M i (M.ownKernel 0 v) p) := by
  subst v
  rfl

lemma raw_diagonal_positive (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (i : I)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ j, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 j py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f p j (plane 0 0 j y) = c) :
    ∀ᵐ p ∂M.parameterLaw 1,
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0 := by
  have hI : 2 ≤ Fintype.card I := by omega
  have hq := coordinate_conditional_descent M i
    (P := fun u p => plane 0 0 i p = u) (Filter.Eventually.of_forall fun _ => rfl)
  have ht := coordinate_conditional_descent M i
    (P := fun _ p => rawSlotActive M i (M.ownKernel 0 (plane 0 0 i p)) p = rawSlotTestSpan M i p)
    (rawSlotActive_eq_testSpan M hI i)
  have hex := coordinate_conditional_descent M i (P := fun _ p => ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f p j (plane 0 0 j y) = c) he
  have hp : ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0 := by
    filter_upwards [raw_diagonal_binary M hM hk i,raw_coordinate_marginal M hI i,hq,ht,hex]
      with u hbin hm hq ht hex
    have hnon := active_projection_not_ae_zero (M.parameterCoordinateKernel i u)
      (fun p => rawSlotActive M i (M.ownKernel 0 u) p)
    filter_upwards [Measure.ae_ae_of_ae_prod hbin,hm,hq,hex,hnon] with p hbin hm hpu hex hnon
    obtain ⟨c, hc⟩ := hex
    let hf' : ∀ j, Measurable (f p j) := fun j => (hf j).comp (measurable_const.prodMk measurable_id)
    let v := circleLp (M.ownKernel 0 u) (f p i) (hf' i)
    have hva : v ∈ rawSlotActive M i (M.ownKernel 0 u) p := raw_tuple_active M i p _ hm (f p) hf' c hc
    have hne : v ≠ 0 := circleLp_ne_zero _ _ _
    intro hz
    rw [hpu] at hz
    have hnmem : ∀ᵐ q ∂M.parameterCoordinateKernel i u,
        rawSlotIndicator M i (fun p => f p i) (hf i) p q ≠ true := by
      apply ae_iff.mpr
      simpa only [not_not] using hz
    apply hnon v hva hne
    filter_upwards [hbin,hq,ht,hnmem] with q hbin hqu ht hnmem
    rcases hbin (f p) hf' c hc with hzero | hself
    · exact hzero
    · apply False.elim
      apply hnmem
      apply (rawSlotIndicator_eq_true_iff M i (fun p => f p i) (hf i) p q).mpr
      rw [←ht]

      have hmem := (rawSlotActive M i (M.ownKernel 0 u) q).starProjection_eq_self_iff.mp hself
      exact (raw_slot_mem_parameter_congr M i u _ hqu.symm q (f p i) (hf' i)).mp hmem
  have hmeas : MeasurableSet {p : Arr I M.U 1 |
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0} := by
    have h := Kernel.measurable_kernel_prodMk_left
      (κ := (M.parameterCoordinateKernel i).comap (plane 0 0 i) (measurable_plane _ _ _))
      (measurableSet_eq_fun (measurable_rawSlotIndicator M i (fun p => f p i) (hf i)) (measurable_const (a := true)))
    exact (measurableSet_eq_fun h (measurable_const (a := (0 : ℝ≥0∞)))).compl
  apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hmeas
  rwa [M.parameterLaw_consistent 0 0 i]
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
namespace FiniteKernel
variable {ι S Y : Type*} [Fintype ι] [MeasurableSpace S] [MeasurableSpace Y]
lemma map_pair (κ : ι → Kernel S Y) [∀ i, IsMarkovKernel (κ i)]
    (i j : ι) (hij : i ≠ j) :
    (pi κ).map (fun y => (y i,y j)) = κ i ×ₖ κ j := by
  ext s : 1
  rw [Kernel.map_apply _ ((measurable_pi_apply i).prodMk (measurable_pi_apply j)),pi_apply,Kernel.prod_apply]
  have hi : iIndepFun (fun i : ι => Function.eval i) (Measure.pi (fun i => κ i s)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun i => κ i s) i).map_eq,
    (measurePreserving_eval (fun i => κ i s) j).map_eq]
end FiniteKernel
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma parameter_pair_geometry (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t) :
    HasCondDistrib (fun e => (plane 1 (Fin.last 1) j e,plane 1 (Fin.last 1) t e))
      (plane 1 0 a)
      ((M.parameterCoordinateKernel a).comap (plane 0 0 j) (measurable_plane _ _ _) ×ₖ
       (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _))
      (M.parameterLaw 2) := by
  have hpair : ({j,t} : Finset I) ≠ Finset.univ := by
    intro h
    have := pair_complement_nonempty hk j t
    simp only [h,Finset.compl_univ,Finset.not_nonempty_empty] at this
  let j' : ({j,t} : Finset I) := ⟨j,by simp⟩
  let t' : ({j,t} : Finset I) := ⟨t,by simp⟩
  have hne : j' ≠ t' := fun h => hjt (congrArg Subtype.val h)
  have h := (parameter_geometry M hM (by omega) a {j,t} hpair).comp_left
    ((measurable_pi_apply j').prodMk (measurable_pi_apply t'))
  rw [FiniteKernel.map_pair _ j' t' hne] at h
  exact h
end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section CircleSlotIndicators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawSlotIndicator_on_square (hI : 2 ≤ Fintype.card I) (a j : I)
    (f : Arr I M.U 1 → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a f hf (plane 1 0 a e) (plane 1 (Fin.last 1) j e) = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f (plane 1 0 a e))
        (hf.comp (measurable_const.prodMk measurable_id)) ∈
      rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) := by
  have hmp : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (rawSlotActive_eq_testSpan M hI a)] with e he
  rw [rawSlotIndicator_eq_true_iff,←he]
  have hloc : plane 0 0 j (plane 1 0 a e) = plane 0 0 a (plane 1 (Fin.last 1) j e) := by
    funext x
    simp only [plane]
    congr 1
    funext t
    fin_cases t <;> rfl

  rw [hloc]

lemma raw_row_indicators_equal (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) =
      rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e) := by
  have hr : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [raw_row_membership_transfer M hM hk a j t hjt,
    rawSlotIndicator_on_square M (by omega) a j (fun p => f p j) (hf j),
    rawSlotIndicator_on_square M (by omega) a t (fun p => f p t) (hf t),hr.quasiMeasurePreserving.ae he]
    with e htrans hj ht hex
  obtain ⟨c,hc⟩ := hex
  apply Bool.eq_iff_iff.mpr
  rw [hj,ht]
  exact htrans (f (plane 1 0 a e))
    (fun i => (hf i).comp (measurable_const.prodMk measurable_id)) c hc

lemma raw_row_membership_forced (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
    ∀ᵐ e ∂M.parameterLaw 2,
      circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f (plane 1 0 a e) j)
        ((hf j).comp (measurable_const.prodMk measurable_id)) ∈
      rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) := by
  have hforce (t : I) (hat : a ≠ t) :
      ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p a) (hf a) (plane 1 0 a e) (plane 1 (Fin.last 1) a e) = true ∧
      rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e) = true := by
    apply conditional_equal_positive_indicators (measurable_plane _ _ _) (measurable_plane _ _ _)
      (measurable_plane _ _ _) (parameter_pair_geometry M hM hk a a t hat)
      (rawSlotIndicator M a (fun p => f p a) (hf a)) (rawSlotIndicator M a (fun p => f p t) (hf t))
      (measurable_rawSlotIndicator M a _ _) (measurable_rawSlotIndicator M a _ _)
      (raw_row_indicators_equal M hM hk a a t hat f hf he)
    rw [M.parameterLaw_consistent 1 0 a]
    exact raw_diagonal_positive M hM hk a f hf he
  have hind : ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) = true := by
    by_cases haj : a = j
    · subst j
      have hex : ∃ t : I, a ≠ t := by
        by_contra! h
        have hc : Fintype.card I ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => (h x).symm.trans (h y))
        omega
      obtain ⟨t,hat⟩ := hex
      exact (hforce t hat).mono fun _ h => h.1
    · exact (hforce j haj).mono fun _ h => h.2
  filter_upwards [hind,rawSlotIndicator_on_square M (by omega) a j (fun p => f p j) (hf j)] with e he hh
  exact hh.mp he

omit [DecidableEq I] in
lemma parameter_cell_commute (a j : I) (e : Arr I M.U 2) :
    tupleParameter M (plane 1 0 a e) j = tupleParameter M (plane 1 (Fin.last 1) j e) a := by
  funext x
  simp only [tupleParameter,plane]
  congr 1
  funext t
  fin_cases t <;> rfl

omit [DecidableEq I] in
lemma rawExactCone_parameter_congr (i : I) (u v : Arr I M.U 0) (h : u = v)
    (p : Arr I M.U 1) (f : Arr I M.Y 0 → Circle) (hf : Measurable f) :
    (circleLp (M.ownKernel 0 u) f hf ∈ rawExactCone M i (M.ownKernel 0 u) p) ↔
    (circleLp (M.ownKernel 0 v) f hf ∈ rawExactCone M i (M.ownKernel 0 v) p) := by
  subst v
  rfl

lemma rawLineGraph_row_inclusion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ q : HilbertCode (M.ownKernel 0),
      (plane 1 0 a e,q) ∈ rawLineGraph M Λ j →
      (plane 1 (Fin.last 1) j e,q) ∈ rawLineGraph M Λ a := by
  classical
  obtain ⟨D,s,hD,hs,hbase,hmem,_,hcover⟩ := exactCode_sections (M.ownKernel 0) Λ
    (tupleParameter M) (measurable_tupleParameter M) hk hm hind
  let f : ℕ → Arr I M.U 1 → I → Arr I M.Y 0 → Circle :=
    fun n p i y => if p ∈ D n then HilbertCode.circleRep (s n p i) y else 1
  have hf (n i) : Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f n py.1 i py.2) := by
    exact (HilbertCode.measurable_circleRep.comp
      ((((measurable_pi_apply i).comp (hs n)).comp measurable_fst).prodMk measurable_snd)).ite
      ((hD n).preimage measurable_fst) measurable_const
  have hex (n) : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f n p i (plane 0 0 i y) = c := by
    filter_upwards [hL] with p hp
    by_cases hpd : p ∈ D n
    · obtain ⟨c,hc⟩ := exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm p) (hmem n p hpd)
      rw [hp,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)] at hc
      refine ⟨c,?_⟩
      have he := ae_of_ae_map (measurable_rawTuple M).aemeasurable hc
      simpa only [f,ite_eq_left hpd,rawTuple] using he
    · exact ⟨1,Filter.Eventually.of_forall (fun _ => by simp only [f,ite_eq_right hpd,Finset.prod_const_one])⟩
  have hrow : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have hcol : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [ae_all_iff.mpr (fun n => raw_row_membership_forced M hM hk a j (f n) (hf n) (hex n)),
    raw_row_active_to_column_exact M hM hk a j,
    hrow.quasiMeasurePreserving.ae (ae_all_iff.mpr hex),hcol.quasiMeasurePreserving.ae hL]
    with e hforce hcone hexes hLe
  intro q hq
  obtain ⟨b,hb,hbi⟩ := hq
  dsimp only [Prod.fst,Prod.snd] at hb hbi
  obtain ⟨n,hnd,hns⟩ := hcover (_,b) hb
  dsimp only [Prod.fst,Prod.snd] at hnd hns
  have hfq : f n (plane 1 0 a e) j = HilbertCode.circleRep q := by
    funext y
    dsimp only [f]
    rw [ite_eq_left hnd,hns,hbi]
  obtain ⟨c,hc⟩ := hexes n
  have hce := hcone (f n (plane 1 0 a e))
    (fun i => (hf n i).comp (measurable_const.prodMk measurable_id)) c hc (hforce n)
  have hcc : q.IsCanonical ∧ q.IsUnimodular := by
    rw [←hbi]
    exact hb.2.1 j
  have hqb : q.base = tupleParameter M (plane 1 (Fin.last 1) j e) a := by
    rw [←hbi]
    exact (hb.1 j).trans (parameter_cell_commute M a j e)
  apply rawCode_of_cone M Λ _ a hLe (hm _) q hqb hcc.1 hcc.2
  change circleLp (M.ownKernel 0 (tupleParameter M (plane 1 0 a e) j)) _ _ ∈
    rawExactCone M a (M.ownKernel 0 (tupleParameter M (plane 1 0 a e) j)) _ at hce
  apply (rawExactCone_parameter_congr M a _ _ (parameter_cell_commute M a j e)
    _ q.circleRep (HilbertCode.measurable_circleRep_fixed q)).mp
  simpa only [hfq] using hce
end CircleSlotIndicators


universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma rawLineGraph_base {Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)}
    {p : Arr I M.U 1} {i : I} {q : HilbertCode (M.ownKernel 0)}
    (h : (p,q) ∈ rawLineGraph M Λ i) : q.base = tupleParameter M p i := by
  obtain ⟨a,ha,hq⟩ := h
  dsimp only [Prod.fst,Prod.snd] at ha hq
  rw [←hq]
  exact ha.1 i
omit [DecidableEq I] in
lemma rawLineGraph_canonical {Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)}
    {p : Arr I M.U 1} {i : I} {q : HilbertCode (M.ownKernel 0)}
    (h : (p,q) ∈ rawLineGraph M Λ i) : q.IsCanonical ∧ q.IsUnimodular := by
  obtain ⟨a,ha,hq⟩ := h
  dsimp only [Prod.fst,Prod.snd] at ha hq
  rw [←hq]
  exact ha.2.1 i
lemma rawLineGraph_separated (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (p : Arr I M.U 1) (i : I) (q r : HilbertCode (M.ownKernel 0))
    (hq : (p,q) ∈ rawLineGraph M Λ i) (hr : (p,r) ∈ rawLineGraph M Λ i)
    (hne : q ≠ r) : 1 ≤ HilbertCode.distance q r := by
  obtain ⟨a,ha,hai⟩ := hq
  obtain ⟨b,hb,hbi⟩ := hr
  dsimp only [Prod.fst,Prod.snd] at ha hb hai hbi
  have h := HilbertCode.exact_codes_dichotomy (κ := M.ownKernel 0) hk (Λ p) a b
    (fun j => (ha.1 j).trans (hb.1 j).symm) ha.2.1 hb.2.1
    (fun j => by simpa only [ha.1 j] using hm p j) (hind p) ha.2.2 hb.2.2
  rcases h with h | h
  · exact (hne (hai.symm.trans ((congrFun h i).trans hbi))).elim
  · simpa only [hai,hbi] using h i
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P Z U : Type*} [MeasurableSpace P] [MeasurableSpace Z] [MeasurableSpace U]

omit [MeasurableSpace Z] in

lemma iid_random_set_descent (μ : Measure P) [IsProbabilityMeasure μ]
    (S : P → Set Z) (he : ∀ᵐ pq ∂μ.prod μ, S pq.1 = S pq.2) :
    ∀ᵐ p ∂μ, S p = {z | ∀ᵐ q ∂μ, z ∈ S q} := by
  filter_upwards [Measure.ae_ae_of_ae_prod he] with p hp
  ext z
  constructor
  · intro hz
    filter_upwards [hp] with q hq
    rwa [←hq]
  · intro hz
    obtain ⟨q,hq,hzq⟩ := (hp.and hz).exists
    rwa [hq]

def essentialMembership (κ : Kernel U P) (S : Set (P × Z)) : Set (U × Z) :=
  {uz | κ uz.1 {p | (p,uz.2) ∈ S} = 1}

lemma measurableSet_essentialMembership (κ : Kernel U P) [IsSFiniteKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) :
    MeasurableSet (essentialMembership κ S) := by
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ.comap Prod.fst measurable_fst)
    (hS.preimage (measurable_snd.prodMk measurable_fst.snd))
  exact measurableSet_eq_fun h measurable_const

lemma mem_essentialMembership_iff (κ : Kernel U P) [IsMarkovKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) (u : U) (z : Z) :
    (u,z) ∈ essentialMembership κ S ↔ ∀ᵐ p ∂κ u, (p,z) ∈ S := by
  exact (mem_ae_iff_prob_eq_one (hS.preimage (measurable_id.prodMk measurable_const))).symm

lemma conditional_random_set_descent (κ : Kernel U P) [IsMarkovKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) (u : U)
    (he : ∀ᵐ pq ∂(κ u).prod (κ u), {z | (pq.1,z) ∈ S} = {z | (pq.2,z) ∈ S}) :
    ∀ᵐ p ∂κ u, {z | (p,z) ∈ S} = {z | (u,z) ∈ essentialMembership κ S} := by
  filter_upwards [iid_random_set_descent (κ u) (fun p => {z | (p,z) ∈ S}) he] with p hp
  rw [hp]
  ext z
  exact (mem_essentialMembership_iff κ hS u z).symm
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Z : Type*} [MeasurableSpace P]
lemma iid_random_set_equality (μ : Measure P) [IsProbabilityMeasure μ]
    (S : P → Set Z) (he : ∀ᵐ pq ∂μ.prod μ, S pq.1 ⊆ S pq.2) :
    ∀ᵐ pq ∂μ.prod μ, S pq.1 = S pq.2 := by
  have hs : MeasurePreserving (Prod.swap : P × P → P × P) (μ.prod μ) (μ.prod μ) :=
    ⟨measurable_swap,Measure.prod_swap⟩
  filter_upwards [he,hs.quasiMeasurePreserving.ae he] with pq hp hq
  exact Set.Subset.antisymm hp hq
end

section
open MeasureTheory ProbabilityTheory Set
variable {U Y : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]

lemma separated_family_sections (S : Set (U × HilbertCode κ)) (hS : MeasurableSet S)
    (hb : ∀ u q, (u,q) ∈ S → q.base = u)
    (hsep : ∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) :
    ∃ (D : ℕ → Set U) (s : ℕ → U → HilbertCode κ),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n u, (s n u).base = u) ∧
      (∀ n u, u ∈ D n → (u,s n u) ∈ S) ∧
      (∀ u q, (u,q) ∈ S → ∃ n, u ∈ D n ∧ s n u = q) := by
  let : StandardBorelSpace S := hS.standardBorel
  obtain ⟨C,_,hcover,_,hemb⟩ := HilbertCode.separated_branches
    (fun x : S => x.1.1) measurable_subtype_coe.fst
    (fun x : S => x.1.2) measurable_subtype_coe.snd
    (fun x y he => (hb _ _ x.property).trans (he.trans (hb _ _ y.property).symm))
    1 (by norm_num) (by
      intro x y he hne
      apply hsep x.1.1 x.1.2 y.1.2 x.property
      · rw [he]
        exact y.property
      · intro h
        exact hne (Subtype.ext (Prod.ext he h)))
  obtain ⟨D,s,hD,hs,hzero,hmem,hcov⟩ := measurable_branch_sections
    (fun x : S => x.1.1) (fun x : S => x.1.2) measurable_subtype_coe.snd
    (fun u => HilbertCode.encode u 0) (MeasurableSection.zero measurable_id) C hcover hemb
  refine ⟨D,s,hD,hs,?_,?_,?_⟩
  · intro n u
    by_cases hu : u ∈ D n
    · obtain ⟨x,hx,he⟩ := hmem n u hu
      rw [he]
      exact (hb _ _ x.property).trans hx
    · rw [hzero n u hu]
      rfl
  · intro n u hu
    obtain ⟨x,hx,he⟩ := hmem n u hu
    rw [he,←hx]
    exact x.property
  · intro u q hq
    exact hcov ⟨(u,q),hq⟩
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Z : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Z]
lemma measurableSet_enumerated_fibre_eq
    (S : Set (P × Z)) (T : Set (U × Z)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (f : P → U) (hf : Measurable f)
    (D : ℕ → Set P) (s : ℕ → P → Z) (hD : ∀ n, MeasurableSet (D n))
    (hs : ∀ n, Measurable (s n))
    (hsm : ∀ n p, p ∈ D n → (p,s n p) ∈ S)
    (hsc : ∀ p z, (p,z) ∈ S → ∃ n, p ∈ D n ∧ s n p = z)
    (E : ℕ → Set U) (t : ℕ → U → Z) (hE : ∀ n, MeasurableSet (E n))
    (ht : ∀ n, Measurable (t n))
    (htm : ∀ n u, u ∈ E n → (u,t n u) ∈ T)
    (htc : ∀ u z, (u,z) ∈ T → ∃ n, u ∈ E n ∧ t n u = z) :
    MeasurableSet {p | {z | (p,z) ∈ S} = {z | (f p,z) ∈ T}} := by
  have he : {p | {z | (p,z) ∈ S} = {z | (f p,z) ∈ T}} =
      {p | (∀ n, p ∈ D n → (f p,s n p) ∈ T) ∧
           (∀ n, f p ∈ E n → (p,t n (f p)) ∈ S)} := by
    ext p
    constructor
    · intro hp
      constructor
      · intro n hn
        exact Set.ext_iff.mp hp (s n p) |>.mp (hsm n p hn)
      · intro n hn
        exact Set.ext_iff.mp hp (t n (f p)) |>.mpr (htm n (f p) hn)
    · rintro ⟨ha,hb⟩
      ext z
      constructor
      · intro hz
        obtain ⟨n,hn,rfl⟩ := hsc p z hz
        exact ha n hn
      · intro hz
        obtain ⟨n,hn,rfl⟩ := htc (f p) z hz
        exact hb n hn
  rw [he]
  change MeasurableSet ({p | ∀ n, p ∈ D n → (f p,s n p) ∈ T} ∩
    {p | ∀ n, f p ∈ E n → (p,t n (f p)) ∈ S})
  simp only [Set.ofPred_forall]
  refine (MeasurableSet.iInter fun n => ?_).inter (MeasurableSet.iInter fun n => ?_)
  · convert (hD n).compl.union (hT.preimage (hf.prodMk (hs n))) using 1
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage]
    tauto
  · convert ((hE n).preimage hf).compl.union (hS.preimage (measurable_id.prodMk ((ht n).comp hf))) using 1
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,Function.comp_apply,id_eq]
    tauto
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))

include hk hm hind in
lemma measurableSet_rawLineGraph (i : I) : MeasurableSet (rawLineGraph M Λ i) :=
  measurableSet_exactCodeSlot (M.ownKernel 0) Λ (tupleParameter M) (measurable_tupleParameter M) hk hm hind i

include hM hk hL hm hind in
lemma rawLineGraph_conditional_descent (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (u,q) ∈ essentialMembership (M.parameterCoordinateKernel i) (rawLineGraph M Λ i)} := by
  have h := conditional_ae_descent
    (P := fun _ pq => {q | (pq.1,q) ∈ rawLineGraph M Λ i} ⊆ {q | (pq.2,q) ∈ rawLineGraph M Λ i})
    ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _))
    (M.diagonal_parameter_product hM (by omega) i)
    (rawLineGraph_row_inclusion M hM hk Λ hL hm hind i i)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simp only [Kernel.prod_apply] at h
  filter_upwards [h] with u hu
  exact conditional_random_set_descent (M.parameterCoordinateKernel i)
    (measurableSet_rawLineGraph M hk Λ hm hind i) u
    (iid_random_set_equality _ (fun p => {q | (p,q) ∈ rawLineGraph M Λ i}) hu)

include hM hk hL hm hind in
lemma exists_localLineGraph (i : I) :
    ∃ S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)),
      MeasurableSet S ∧
      (∀ u q, (u,q) ∈ S → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
      (∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) ∧
      (∀ᵐ p ∂M.parameterLaw 1, {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (tupleParameter M p i,q) ∈ S}) := by
  let S₀ := essentialMembership (M.parameterCoordinateKernel i) (rawLineGraph M Λ i)
  have hS₀ : MeasurableSet S₀ := measurableSet_essentialMembership _
    (measurableSet_rawLineGraph M hk Λ hm hind i)
  have ha := rawLineGraph_conditional_descent M hM hk Λ hL hm hind i
  have hb := coordinate_conditional_descent M i
    (P := fun u p => tupleParameter M p i = u) (Filter.Eventually.of_forall fun _ => rfl)
  let Q : Arr I M.U 0 → Prop := fun u =>
    (∀ q, (u,q) ∈ S₀ → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
    (∀ q r, (u,q) ∈ S₀ → (u,r) ∈ S₀ → q ≠ r → 1 ≤ HilbertCode.distance q r)
  have hQ : ∀ᵐ u ∂M.parameterLaw 0, Q u := by
    filter_upwards [ha,hb] with u ha hb
    obtain ⟨p,hp,hpu⟩ := (ha.and hb).exists
    have heq (q) : (p,q) ∈ rawLineGraph M Λ i ↔ (u,q) ∈ S₀ := Set.ext_iff.mp hp q
    constructor
    · intro q hq
      have hq' := (heq q).mpr hq
      exact ⟨(rawLineGraph_base M hq').trans hpu,rawLineGraph_canonical M hq'⟩
    · intro q r hq hr hne
      exact rawLineGraph_separated M hk Λ hm hind p i q r ((heq q).mpr hq) ((heq r).mpr hr) hne
  have hn : NullMeasurableSet {u | Q u} (M.parameterLaw 0) :=
    NullMeasurableSet.congr (nullMeasurableSet_univ (μ := M.parameterLaw 0))
      (by filter_upwards [hQ] with u h; exact propext (iff_of_true trivial h))
  obtain ⟨A,hA,hAm,hAe⟩ := hn.exists_measurable_subset_ae_eq
  let S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)) := (Prod.fst ⁻¹' A) ∩ S₀
  have hS : MeasurableSet S := (hAm.preimage measurable_fst).inter hS₀
  have hSb (u q) (hq : (u,q) ∈ S) : q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular :=
    (hA hq.1).1 q hq.2
  have hSs (u q r) (hq : (u,q) ∈ S) (hr : (u,r) ∈ S) (hne : q ≠ r) :
      1 ≤ HilbertCode.distance q r := (hA hq.1).2 q r hq.2 hr.2 hne
  obtain ⟨E,t,hE,ht,_,htm,htc⟩ := separated_family_sections (M.ownKernel 0) S hS
    (fun u q hq => (hSb u q hq).1) hSs
  obtain ⟨D,s,hD,hs,_,hsm,_,hsc⟩ := exactCode_sections (M.ownKernel 0) Λ
    (tupleParameter M) (measurable_tupleParameter M) hk hm hind
  have hemeas : MeasurableSet {p | {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}} :=
    measurableSet_enumerated_fibre_eq (rawLineGraph M Λ i) S
      (measurableSet_rawLineGraph M hk Λ hm hind i) hS (fun p => tupleParameter M p i)
      ((measurable_pi_apply i).comp (measurable_tupleParameter M))
      D (fun n p => s n p i) hD (fun n => (measurable_pi_apply i).comp (hs n))
      (fun n p hp => ⟨s n p,hsm n p hp,rfl⟩) (by
        intro p q hq
        obtain ⟨b,hb,hbi⟩ := hq
        obtain ⟨n,hn,he⟩ := hsc (p,b) hb
        exact ⟨n,hn,(congrFun he i).trans hbi⟩)
      E t hE ht htm htc
  refine ⟨S,hS,hSb,hSs,?_⟩
  apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hemeas
  rw [M.parameterLaw_consistent 0 0 i]
  filter_upwards [ha,hb,hQ,hAe] with u ha hb hQ hAe
  filter_upwards [ha,hb] with p hp hpu
  rw [hpu,hp]
  ext q
  exact (and_iff_right (hAe.mpr hQ)).symm
end

universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma localLineGraph_inclusion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : I → Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ i, ∀ᵐ p ∂M.parameterLaw 1, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S i}) (a j : I) :
    ∀ᵐ u ∂M.parameterLaw 0, {q | (u,q) ∈ S j} ⊆ {q | (u,q) ∈ S a} := by
  have hrow : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have hcol : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have h : ∀ᵐ e ∂M.parameterLaw 2,
      {q | (tupleParameter M (plane 1 0 a e) j,q) ∈ S j} ⊆
      {q | (tupleParameter M (plane 1 0 a e) j,q) ∈ S a} := by
    filter_upwards [rawLineGraph_row_inclusion M hM hk Λ hL hm hind a j,
      hrow.quasiMeasurePreserving.ae (hS j),hcol.quasiMeasurePreserving.ae (hS a)] with e he hr hc
    rw [parameter_cell_commute M a j e] at hr ⊢
    rw [←hr,←hc]
    exact he
  have hd := ae_map_descent (P := fun u => {q | (u,q) ∈ S j} ⊆ {q | (u,q) ∈ S a}) (M.parameterLaw 2)
    ((measurable_plane 0 0 j).comp (measurable_plane 1 0 a)) h
  rwa [←Measure.map_map (measurable_plane 0 0 j) (measurable_plane 1 0 a),
    M.parameterLaw_consistent 1 0 a,M.parameterLaw_consistent 0 0 j] at hd

lemma exists_commonLocalLineGraph (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) :
    ∃ S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)),
      MeasurableSet S ∧
      (∀ u q, (u,q) ∈ S → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
      (∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) ∧
      (∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (tupleParameter M p i,q) ∈ S}) := by
  classical
  have hI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i₀ : I := Classical.choice hI
  choose S hSm hSb hSs hSe using exists_localLineGraph M hM hk Λ hL hm hind
  have he (i : I) : ∀ᵐ u ∂M.parameterLaw 0, {q | (u,q) ∈ S i} = {q | (u,q) ∈ S i₀} := by
    filter_upwards [localLineGraph_inclusion M hM hk Λ hL hm hind S hSe i₀ i,
      localLineGraph_inclusion M hM hk Λ hL hm hind S hSe i i₀] with u ha hb
    exact Subset.antisymm ha hb
  have hep (i : I) : ∀ᵐ p ∂M.parameterLaw 1,
      {q | (tupleParameter M p i,q) ∈ S i} = {q | (tupleParameter M p i,q) ∈ S i₀} :=
    (show MeasurePreserving (plane 0 0 i) (M.parameterLaw 1) (M.parameterLaw 0) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae (he i)
  refine ⟨S i₀,hSm i₀,hSb i₀,hSs i₀,?_⟩
  filter_upwards [ae_all_iff.mpr hSe,ae_all_iff.mpr hep] with p h₁ h₂ i
  exact (h₁ i).trans (h₂ i)

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)
lemma exactCode_of_circle_tuple {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hb : ∀ i, (a i).base = u p i)
    (hcan : ∀ i, (a i).IsCanonical ∧ (a i).IsUnimodular)
    (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ i, HilbertCode.circleRep (a i) (y i) = c) :
    (p,a) ∈ exactCodeSet κ Λ u := by
  refine ⟨hb,hcan,?_⟩
  have hrep (i) : ∀ᵐ y ∂Λ p,
      (HilbertCode.circleRep (a i) (y i) : ℂ) = HilbertCode.representative (a i,y i) := by
    have h := HilbertCode.circleRep_ae (a i) (hcan i).2
    rw [hb i] at h
    exact (hm i).quasiMeasurePreserving.ae h
  have hmean : (fun y => ∏ i, HilbertCode.representative (a i,y i)) =ᵐ[Λ p]
      fun _ => (c : ℂ) := by
    filter_upwards [he,ae_all_iff.mpr hrep] with y hy hr
    calc
      _ = ∏ i, (HilbertCode.circleRep (a i) (y i) : ℂ) :=
        Finset.prod_congr rfl (fun i _ => (hr i).symm)
      _ = ((∏ i, HilbertCode.circleRep (a i) (y i) : Circle) : ℂ) :=
        (map_prod Circle.coeHom (fun i => HilbertCode.circleRep (a i) (y i)) Finset.univ).symm
      _ = _ := congrArg (fun z : Circle => (z : ℂ)) hy
  change ‖∫ y, ∏ i, HilbertCode.representative (a i,y i) ∂Λ p‖ = 1
  rw [integral_congr_ae hmean,integral_const,probReal_univ,one_smul,Circle.norm_coe]
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma independent_circle_product_constant
    (f : I → Ω → Circle) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f μ) (c : Circle)
    (he : ∀ᵐ x ∂μ, ∏ i, f i x = c) :
    ∀ i, ∃ d : Circle, f i =ᵐ[μ] fun _ => d := by
  classical
  let g : I → Ω → ℂ := fun i x => (f i x : ℂ)
  have hg (i) : Measurable (g i) := measurable_subtype_coe.comp (hf i)
  have hgi : iIndepFun g μ := by
    exact hind.comp (fun (_ : I) (z : Circle) => (z : ℂ)) (fun _ => measurable_subtype_coe)
  have hprod : (∏ i, ∫ x, g i x ∂μ) = (c : ℂ) := by
    rw [←hgi.integral_fun_prod_eq_prod_integral (fun i => (hg i).aestronglyMeasurable)]
    have he' : (fun x => ∏ i, g i x) =ᵐ[μ] fun _ => (c : ℂ) := by
      filter_upwards [he] with x hx
      exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun z : Circle => (z : ℂ)) hx)
    rw [integral_congr_ae he',integral_const,probReal_univ,one_smul]
  have hle (i) : ‖∫ x, g i x ∂μ‖ ≤ 1 := by
    calc
      _ ≤ ∫ x, ‖g i x‖ ∂μ := norm_integral_le_integral_norm _
      _ = 1 := by simp only [g,Circle.norm_coe,integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hnorm : (∏ i, ‖∫ x, g i x ∂μ‖) = 1 := by
    rw [←norm_prod,hprod,Circle.norm_coe]
  intro i
  have hone : ‖∫ x, g i x ∂μ‖ = 1 := by
    apply le_antisymm (hle i)
    calc
      1 = ‖∫ x, g i x ∂μ‖ * ∏ j ∈ Finset.univ.erase i, ‖∫ x, g j x ∂μ‖ := by
        rw [mul_comm,Finset.prod_erase_mul _ _ (Finset.mem_univ i),hnorm]
      _ ≤ ‖∫ x, g i x ∂μ‖ * 1 := mul_le_mul_of_nonneg_left
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hle j)) (norm_nonneg _)
      _ = _ := mul_one _
  have heq : g i =ᵐ[μ] fun _ => ∫ x, g i x ∂μ := by
    rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const
      (μ := μ) (f := g i) (C := (1 : ℝ))
      (Filter.Eventually.of_forall fun x => (Circle.norm_coe (f i x)).le) with h | h
    · simpa only [average_eq_integral,Function.const_def] using h
    · simp only [hone,probReal_univ,one_mul,lt_self_iff_false] at h
  refine ⟨⟨∫ x, g i x ∂μ,mem_sphere_zero_iff_norm.mpr hone⟩,?_⟩
  exact heq.mono fun _ h => Circle.coe_injective h
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma circle_square_consistency [DecidableEq I]
    (f : I → J → Ω → Circle) (hf : ∀ i j, Measurable (f i j))
    (a : I)
    (hind : iIndepFun (fun i : (Finset.univ.erase a : Finset I) =>
      fun x => ∏ j, f i j x) μ)
    (c : J → Circle) (hc : ∀ j, ∀ᵐ x ∂μ, ∏ i, f i j x = c j)
    (d : Circle) (hd : ∀ᵐ x ∂μ, ∏ j, f a j x = d) :
    ∀ i, ∃ e : Circle, ∀ᵐ x ∂μ, ∏ j, f i j x = e := by
  have ht : ∀ᵐ x ∂μ, ∏ i, ∏ j, f i j x = ∏ j, c j := by
    filter_upwards [ae_all_iff.mpr hc] with x hx
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl (fun j _ => hx j)
  have hp : ∀ᵐ x ∂μ,
      ∏ i : (Finset.univ.erase a : Finset I), ∏ j, f i j x = (∏ j, c j) / d := by
    filter_upwards [ht,hd] with x htx hdx
    rw [Finset.prod_coe_sort (Finset.univ.erase a) (fun i => ∏ j, f i j x)]
    apply (eq_div_iff_mul_eq').mpr
    rw [←hdx,Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    exact htx
  have hfm (i : (Finset.univ.erase a : Finset I)) : Measurable (fun x => ∏ j, f i j x) :=
    Finset.measurable_prod _ (fun j _ => hf i j)
  have he := independent_circle_product_constant μ
    (fun i : (Finset.univ.erase a : Finset I) => fun x => ∏ j, f i j x)
    hfm hind ((∏ j, c j) / d) hp
  intro i
  by_cases hi : i = a
  · subst i; exact ⟨d,hd⟩
  · exact he ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩⟩
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma whole_rows_independent_fibre (hM : M.IsSaturated) (a : I) :
    ∀ᵐ e ∂M.parameterLaw 2, iIndepFun
      (fun i : (Finset.univ.erase a : Finset I) => plane 1 0 (i : I)) (M.ownKernel 2 e) := by
  have hp := ConditionalFibres.marginal (measurable_parents M (Finset.univ.erase a) 1)
    (M.ownKernel_conditional 2)
    (rows_conditional M hM (Finset.univ.erase a) (by
      intro he; have := Finset.mem_univ a; rw [←he] at this; exact Finset.notMem_erase a _ this) 0)
  filter_upwards [hp] with e he
  change MeasurePreserving _ _ (Measure.pi (fun i : (Finset.univ.erase a : Finset I) =>
    M.ownKernel 1 (plane 1 0 (i : I) e))) at he
  have h := iIndepFun_pi (μ := fun i : (Finset.univ.erase a : Finset I) =>
    M.ownKernel 1 (plane 1 0 (i : I) e)) (fun _ => measurable_id.aemeasurable)
  rw [←he.map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 2 e)
    (fun (z : ∀ _ : (Finset.univ.erase a : Finset I), Arr I M.Y 1) i => z i)
    (fun y i => plane 1 0 (i : I) y) (fun i => measurable_pi_apply i)
    (measurable_parents M _ _)).mp h

lemma rawSquare_marginals (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M) :
    ∀ᵐ e ∂M.parameterLaw 2, (∀ i, MeasurePreserving
      (rawTuple M ∘ plane 1 0 i) (M.ownKernel 2 e) (Λ (plane 1 0 i e))) ∧
      (∀ j, MeasurePreserving (rawTuple M ∘ plane 1 (Fin.last 1) j)
        (M.ownKernel 2 e) (Λ (plane 1 (Fin.last 1) j e))) := by
  have hrow (i : I) : ∀ᵐ e ∂M.parameterLaw 2,
      Λ (plane 1 0 i e) = rawTupleKernel M (plane 1 0 i e) :=
    (show MeasurePreserving (plane 1 0 i) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hL
  have hcol (j : I) : ∀ᵐ e ∂M.parameterLaw 2,
      Λ (plane 1 (Fin.last 1) j e) = rawTupleKernel M (plane 1 (Fin.last 1) j e) :=
    (show MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae hL
  filter_upwards [ae_all_iff.mpr hrow,ae_all_iff.mpr hcol,
    ae_all_iff.mpr (row_marginal_fibre M hM hI),ae_all_iff.mpr (column_marginal_fibre M hI)]
    with e hr hc hmr hmc
  constructor
  · intro i
    rw [hr i]
    exact (MeasurePreserving.mk (measurable_rawTuple M)
      (Kernel.map_apply _ (measurable_rawTuple M) _).symm).comp (hmr i)
  · intro j
    rw [hc j]
    exact (MeasurePreserving.mk (measurable_rawTuple M)
      (Kernel.map_apply _ (measurable_rawTuple M) _).symm).comp (hmc j)

lemma rawSquare_exact_consistency (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j))) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (q : I → I → HilbertCode (M.ownKernel 0)) (a : I),
      (∀ j, (plane 1 (Fin.last 1) j e,fun i => q i j) ∈
        exactCodeSet (M.ownKernel 0) Λ (tupleParameter M)) →
      (plane 1 0 a e,q a) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) →
      ∀ i, (plane 1 0 i e,q i) ∈ exactCodeSet (M.ownKernel 0) Λ (tupleParameter M) := by
  filter_upwards [rawSquare_marginals M hM hI Λ hL,
    ae_all_iff.mpr (whole_rows_independent_fibre M hM)] with e hmar hind q a hcodes hr
  let f : I → I → Arr I M.Y 2 → Circle := fun i j y =>
    HilbertCode.circleRep (q i j) (missingRow M 0 j i y)
  have hf (i j : I) : Measurable (f i j) :=
    (HilbertCode.measurable_circleRep_fixed _).comp (measurable_missingRow M _ _ _)
  choose c hconst using fun j => exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M)
    (hm _) (hcodes j)
  have hcol (j : I) : ∀ᵐ y ∂M.ownKernel 2 e, ∏ i, f i j y = c j := by
    have h := (hmar.2 j).quasiMeasurePreserving.ae (hconst j)
    convert h using 1
    congr! 3 with y i
    exact congrArg (HilbertCode.circleRep (q i j)) (congrFun (plane_first_last M 0 i j) y).symm
  obtain ⟨d,hd⟩ := exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm _) hr
  have hrow : ∀ᵐ y ∂M.ownKernel 2 e, ∏ j, f a j y = d :=
    (hmar.1 a).quasiMeasurePreserving.ae hd
  have hi : iIndepFun (fun i : (Finset.univ.erase a : Finset I) => fun y => ∏ j, f i j y)
      (M.ownKernel 2 e) := by
    exact (hind a).comp (fun (i : (Finset.univ.erase a : Finset I)) (y : Arr I M.Y 1) =>
      ∏ j, HilbertCode.circleRep (q i j) (plane 0 0 j y)) (fun i =>
        Finset.measurable_prod _ (fun j _ =>
          (HilbertCode.measurable_circleRep_fixed _).comp (measurable_plane _ _ _)))
  have hex := circle_square_consistency (M.ownKernel 2 e) f hf a hi c hcol d hrow
  intro i
  obtain ⟨b,hb⟩ := hex i
  have hbe : ∀ᵐ z ∂Λ (plane 1 0 i e), ∏ j, HilbertCode.circleRep (q i j) (z j) = b := by
    have hh := ae_map_descent (P := fun z : I → Arr I M.Y 0 =>
      ∏ j, HilbertCode.circleRep (q i j) (z j) = b)
      (M.ownKernel 2 e) (hmar.1 i).measurable hb
    rwa [(hmar.1 i).map_eq] at hh
  apply exactCode_of_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm _) _ _ b hbe
  · intro j
    exact ((hcodes j).1 i).trans (parameter_cell_commute M i j e).symm
  · intro j
    exact (hcodes j).2.1 i
end ArrayObjects.Object.Rolled

open MeasureTheory Set
variable {U Z : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableEq Z]

lemma enumerate_without_repetition (S : Set (U × Z))
    (D : ℕ → Set U) (s : ℕ → U → Z)
    (hD : ∀ n, MeasurableSet (D n)) (hs : ∀ n, Measurable (s n))
    (hm : ∀ n u, u ∈ D n → (u,s n u) ∈ S)
    (hc : ∀ u z, (u,z) ∈ S → ∃ n, u ∈ D n ∧ s n u = z) :
    ∃ E : ℕ → Set U, (∀ n, MeasurableSet (E n)) ∧
      (∀ n, E n ⊆ D n) ∧
      (∀ n u, u ∈ E n → (u,s n u) ∈ S) ∧
      (∀ u z, (u,z) ∈ S → ∃ n, u ∈ E n ∧ s n u = z) ∧
      (∀ u n m, u ∈ E n → u ∈ E m → s n u = s m u → n = m) := by
  classical
  let E : ℕ → Set U := fun n => D n \ ⋃ m < n, {u | u ∈ D m ∧ s m u = s n u}
  have hED (n) : E n ⊆ D n := fun _ h => h.1
  refine ⟨E,?_,hED,(fun n u h => hm n u (hED n h)),?_,?_⟩
  · intro n
    exact (hD n).diff (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
      (hD m).inter (measurableSet_eq_fun (hs m) (hs n)))
  · intro u z hz
    have hex := hc u z hz
    let n := Nat.find hex
    have hn : u ∈ D n ∧ s n u = z := Nat.find_spec hex
    refine ⟨n,⟨hn.1,?_⟩,hn.2⟩
    intro hu
    obtain ⟨m,hem⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hmn,he⟩ := Set.mem_iUnion.mp hem
    exact Nat.find_min hex hmn ⟨he.1,he.2.trans hn.2⟩
  · intro u n m hn hm he
    have hnot (n m : ℕ) (hn : u ∈ E n) (hm : u ∈ E m) (he : s n u = s m u) : ¬n < m := by
      intro hnm
      exact hm.2 (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hnm,hn.1,he⟩⟩)
    exact Nat.le_antisymm (not_lt.mp (hnot m n hm hn he.symm)) (not_lt.mp (hnot n m hn hm he))

end Rokhlin

end

end OAI
