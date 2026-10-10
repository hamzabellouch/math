import OAI.Dynamics.MultipleMixing.Arrays

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

abbrev pull (hx : MeasurePreserving x μ ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ x hx).toContinuousLinearMap

def operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν := (pull hx).adjoint ∘L pull hy

lemma pull_norm_le (hx : MeasurePreserving x μ ν) : ‖pull hx‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp [pull]

lemma operator_norm_le (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    ‖operator hx hy‖ ≤ 1 := by
  apply le_trans (opNorm_comp_le _ _)
  simpa using (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (by simpa using pull_norm_le hx) (norm_nonneg _) (pull_norm_le hy)

lemma operator_adjoint (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    (operator hx hy).adjoint = operator hy hx := by simp [operator]

lemma pull_adjoint_pull (hx : MeasurePreserving x μ ν) :
    (pull hx).adjoint ∘L pull hx = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pull hx)).mp
  intro g
  exact Lp.norm_compMeasurePreserving g hx

lemma operator_self (hx : MeasurePreserving x μ ν) :
    operator hx hx = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := pull_adjoint_pull hx

lemma pull_comp (hx : MeasurePreserving x μ ν) (hz : MeasurePreserving z ν τ) :
    pull (hz.comp hx) = pull hx ∘L pull hz := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.compMeasurePreserving_comp_apply f hz hx

lemma inner_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx hy h) = ∫ ω, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  change inner ℂ g ((pull hx).adjoint (pull hy h)) = _
  rw [adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

lemma operator_pullback {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f μ' μ)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) :
    operator (hx.comp hf) (hy.comp hf) = operator hx hy := by
  simp only [operator]
  rw [pull_comp hf hx, pull_comp hf hy, adjoint_comp]
  calc
    ((pull hx).adjoint ∘L (pull hf).adjoint) ∘L (pull hf ∘L pull hy) =
        (pull hx).adjoint ∘L (((pull hf).adjoint ∘L pull hf) ∘L pull hy) := by
      simp only [comp_assoc]
    _ = (pull hx).adjoint ∘L pull hy := by rw [pull_adjoint_pull, id_comp]

end
section

variable {Ω X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma pull_range (hx : MeasurePreserving x μ ν) :
    LinearMap.range (pull hx).toLinearMap =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    have hm : StronglyMeasurable[MeasurableSpace.comap x inferInstance] (fun ω => g (x ω)) :=
      g.1.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
    exact hm.aestronglyMeasurable.congr (Lp.coeFn_compMeasurePreserving g hx).symm
  · intro hf
    have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
    obtain ⟨g, hg, he⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
    have hfe : f =ᵐ[μ] g ∘ x := hm.ae_eq_mk.trans (Filter.Eventually.of_forall (congrFun he))
    have hLp : MemLp g 2 ν := by
      rw [← hx.map_eq]
      exact (memLp_map_measure_iff hg.aestronglyMeasurable hx.aemeasurable).mpr
        ((memLp_congr_ae hfe).mp (Lp.memLp f))
    refine ⟨hLp.toLp g, ?_⟩
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving (hLp.toLp g) hx).trans
      ((hx.quasiMeasurePreserving.ae_eq_comp hLp.coeFn_toLp).trans hfe.symm)

lemma pull_adjoint_projection (hx : MeasurePreserving x μ ν) (f : Lp ℂ 2 μ) :
    pull hx ((pull hx).adjoint f) =
      (condExpL2 ℂ ℂ hx.measurable.comap_le f : Lp ℂ 2 μ) := by
  let S := lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  change _ = S.starProjection f
  apply (S.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · change _ ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
    rw [← pull_range hx]
    exact ⟨(pull hx).adjoint f, rfl⟩
  · intro u hu
    change u ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ at hu
    rw [← pull_range hx] at hu
    obtain ⟨g, rfl⟩ := hu
    rw [inner_sub_left]
    change inner ℂ f (pull hx g) -
      inner ℂ (pull hx ((pull hx).adjoint f)) (pull hx g) = 0
    rw [← adjoint_inner_left, ← adjoint_inner_left]
    change inner ℂ ((pull hx).adjoint f) g -
      inner ℂ (((pull hx).adjoint ∘L pull hx) ((pull hx).adjoint f)) g = 0
    rw [pull_adjoint_pull]
    simp

lemma operator_ae_eq_condExp [IsFiniteMeasure μ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (h : Lp ℂ 2 ρ) :
    (fun ω => operator hx hy h (x ω)) =ᵐ[μ]
      μ[(fun ω => h (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hp := pull_adjoint_projection hx (pull hy h)
  have hc := (Lp.memLp (pull hy h)).condExpL2_ae_eq_condExp (𝕜 := ℂ) hx.measurable.comap_le
  rw [Lp.toLp_coeFn, ← hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy h) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving h hy)))


end
section

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  {τ : Measure Z} {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma condExp_of_kernel (hx : Measurable x) {κ : Kernel X Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x κ μ) (g : Y → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ v, g v ∂κ (x ω)) := by
  have he : condDistrib y x μ =ᵐ[μ.map x] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd h.aemeasurable_fst h.aemeasurable_snd h.map_eq
  have he' := ae_of_ae_map hx.aemeasurable he
  filter_upwards [condExp_ae_eq_integral_condDistrib hx h.aemeasurable_snd hg hgi, he']
    with ω hω heω
  exact hω.trans (by rw [heω])

lemma screened_condExp (hx : Measurable x) (hz : Measurable z)
    {κ : Kernel Z Y} [IsMarkovKernel κ] (h : HasCondDistrib y x (κ.comap z hz) μ)
    (g : Y → ℂ) (hg : StronglyMeasurable g) (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      μ[(fun ω => g (y ω)) | MeasurableSpace.comap (z ∘ x) inferInstance] :=
  (condExp_of_kernel hx h g hg hgi).trans
    (condExp_of_kernel (hz.comp hx) h.comp_right g hg hgi).symm

theorem screened_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hz : MeasurePreserving z ν τ) {κ : Kernel Z Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x (κ.comap z hz.measurable) μ) :
    operator hx hy = pull hz ∘L operator (hz.comp hx) hy := by
  apply ContinuousLinearMap.ext
  intro g
  apply (Lp.compMeasurePreservingₗᵢ ℂ x hx).injective
  change pull hx (operator hx hy g) = (pull hx ∘L pull hz) (operator (hz.comp hx) hy g)
  rw [← pull_comp]
  apply Lp.ext
  have hgi : Integrable (fun ω => g (y ω)) μ :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ((Lp.memLp g).comp_measurePreserving hy)
  have hce := screened_condExp hx.measurable hz.measurable h g g.1.stronglyMeasurable hgi
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    ((operator_ae_eq_condExp hx hy g).trans
      (hce.trans ((operator_ae_eq_condExp (hz.comp hx) hy g).symm.trans
        (Lp.coeFn_compMeasurePreserving _ (hz.comp hx)).symm)))


end


lemma operator_comp_right {Ω S A : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace A] {μ : Measure Ω} {ν : Measure S} {ρ : Measure A}
    {T : Type*} [MeasurableSpace T] {τ : Measure T}
    {s : Ω → S} {t : Ω → T} {a : T → A}
    (hs : MeasurePreserving s μ ν) (ht : MeasurePreserving t μ τ)
    (ha : MeasurePreserving a τ ρ) :
    operator hs (ha.comp ht) = operator hs ht ∘L pull ha := by
  unfold operator
  rw [pull_comp ht ha]
  simp only [comp_assoc]

variable {Ω S T A B C D : Type*}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
  [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
  [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {νs : Measure S} {νt : Measure T}
  {νa : Measure A} {νb : Measure B} {νc : Measure C} {νd : Measure D}
  {s : Ω → S} {t : Ω → T} {a : S → A} {b : S → B} {c : T → C} {d : T → D}

theorem square_rectangle
    (hs : MeasurePreserving s μ νs) (ht : MeasurePreserving t μ νt)
    (ha : MeasurePreserving a νs νa) (hb : MeasurePreserving b νs νb)
    (hc : MeasurePreserving c νt νc) (hd : MeasurePreserving d νt νd)
    {κac : Kernel A C} [IsMarkovKernel κac] {κbd : Kernel B D} [IsMarkovKernel κbd]
    {κca : Kernel C A} [IsMarkovKernel κca] {κdb : Kernel D B} [IsMarkovKernel κdb]
    (hac : HasCondDistrib (c ∘ t) s (κac.comap a ha.measurable) μ)
    (hbd : HasCondDistrib (d ∘ t) s (κbd.comap b hb.measurable) μ)
    (hca : HasCondDistrib (a ∘ s) t (κca.comap c hc.measurable) μ)
    (hdb : HasCondDistrib (b ∘ s) t (κdb.comap d hd.measurable) μ) :
    let F := operator (ha.comp hs) (hc.comp ht)
    let G := operator (hb.comp hs) (hd.comp ht)
    let K := operator ha hb
    let N := operator hc hd
    F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint := by
  dsimp only
  let Q := operator hs ht
  let F := operator (ha.comp hs) (hc.comp ht)
  let G := operator (hb.comp hs) (hd.comp ht)
  have haf : Q ∘L pull hc = pull ha ∘L F := by
    rw [← operator_comp_right]
    exact screened_operator hs (hc.comp ht) ha hac
  have hbf : Q ∘L pull hd = pull hb ∘L G := by
    rw [← operator_comp_right]
    exact screened_operator hs (hd.comp ht) hb hbd
  have har : Q.adjoint ∘L pull ha = pull hc ∘L F.adjoint := by
    dsimp only [Q, F]
    rw [operator_adjoint, operator_adjoint, ← operator_comp_right]
    exact screened_operator ht (ha.comp hs) hc hca
  have hbr : Q.adjoint ∘L pull hb = pull hd ∘L G.adjoint := by
    dsimp only [Q, G]
    rw [operator_adjoint, operator_adjoint, ← operator_comp_right]
    exact screened_operator ht (hb.comp hs) hd hdb
  have hara : (pull ha).adjoint ∘L Q = F ∘L (pull hc).adjoint := by
    have hh := congrArg ContinuousLinearMap.adjoint har
    simpa only [adjoint_comp, adjoint_adjoint] using hh
  have hafa : (pull hc).adjoint ∘L Q.adjoint = F.adjoint ∘L (pull ha).adjoint := by
    simpa only [adjoint_comp] using congrArg ContinuousLinearMap.adjoint haf
  constructor
  · change F ∘L ((pull hc).adjoint ∘L pull hd) =
      ((pull ha).adjoint ∘L pull hb) ∘L G
    calc
      _ = ((pull ha).adjoint ∘L Q) ∘L pull hd := by rw [hara]; simp only [comp_assoc]
      _ = _ := by rw [comp_assoc, hbf]; simp only [comp_assoc]
  · change F.adjoint ∘L ((pull ha).adjoint ∘L pull hb) =
      ((pull hc).adjoint ∘L pull hd) ∘L G.adjoint
    calc
      _ = ((pull hc).adjoint ∘L Q.adjoint) ∘L pull hb := by
        rw [hafa]; simp only [comp_assoc]
      _ = _ := by rw [comp_assoc, hbr]; simp only [comp_assoc]


end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def tupleUnion {Z : Type*} (R S : Finset I) (v : (R → Z) × (S → Z)) : ↥(R ∪ S) → Z :=
  fun i => if h : (i : I) ∈ R then v.1 ⟨i,h⟩ else v.2 ⟨i,(Finset.mem_union.mp i.property).resolve_left h⟩
omit [Fintype I] in
@[fun_prop] lemma measurable_tupleUnion {Z : Type*} [MeasurableSpace Z] (R S : Finset I) :
    Measurable (tupleUnion (Z := Z) R S) := by
  unfold tupleUnion
  apply Measurable.of_eval
  intro i
  split_ifs <;> fun_prop

def tupleSelect {Z : Type*} (R S : Finset I) (h : R ⊆ S) (v : S → Z) : R → Z :=
  fun i => v ⟨i,h i.property⟩
omit [Fintype I] [DecidableEq I] in
@[fun_prop] lemma measurable_tupleSelect {Z : Type*} [MeasurableSpace Z]
    (R S : Finset I) (h : R ⊆ S) : Measurable (tupleSelect (Z := Z) R S h) := by
  unfold tupleSelect
  fun_prop

lemma fullGroupedLocality (hM : M.IsSaturated) (P A C D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint C D)
    (hcover : C ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    HasCondDistrib (cells M A D n) (wholeGroupData M P C n)
      ((condDistrib (cells M A D n) (groupData M A C n) (M.law (n+2))).comap
        (groupSelect M P A C n) (measurable_groupSelect M P A C n)) (M.law (n+2)) := by
  obtain ⟨j,hj⟩ := hD
  have hd : Disjoint C (D.erase j) := hCD.mono_right (Finset.erase_subset _ _)
  have hcj : C ∪ D.erase j = Outside j := by
    ext i
    have hjC : j ∉ C := fun h => Finset.disjoint_left.mp hCD h hj
    have hi : i ∈ C ∨ i ∈ D := Finset.mem_union.mp (hcover ▸ Finset.mem_univ i)
    simp only [Finset.mem_union, Finset.mem_erase, Outside, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · rintro (h | h)
      · exact fun e => hjC (e ▸ h)
      · exact h.1
    · intro h
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inr ⟨h,hi⟩
  have h := grouped_cell_locality M hM P A C (D.erase j) hP hPA hcard hproper hd n j hcj
  erw [Finset.insert_erase hj] at h
  exact h

def splitOwnData (P A R S : Finset I) (n : ℕ)
    (v : WholeGroupData M P R n × (S → A → Arr I M.Y n)) : GroupData M A (R ∪ S) n :=
  (v.1.1.1, tupleUnion R S (columnRestrict M A R n v.1.2, v.2))
@[fun_prop] lemma measurable_splitOwnData (P A R S : Finset I) (n : ℕ) :
    Measurable (splitOwnData M P A R S n) := by
  unfold splitOwnData
  fun_prop

def splitRowKernel (P A R S D : Finset I) (n : ℕ) :
    Kernel (WholeGroupData M P R n × (S → A → Arr I M.Y n)) (D → A → Arr I M.Y n) :=
  (condDistrib (cells M A D n) (groupData M A (R ∪ S) n) (M.law (n+2))).comap
    (splitOwnData M P A R S n) (measurable_splitOwnData M P A R S n)
instance splitRowKernel_markov (P A R S D : Finset I) (n : ℕ) :
    IsMarkovKernel (splitRowKernel M P A R S D n) := by unfold splitRowKernel; infer_instance

lemma wholeSplit_field (P R S : Finset I) (n : ℕ) :
    MeasurableSpace.comap (wholeGroupData M P (R ∪ S) n) inferInstance =
      MeasurableSpace.comap (fun y => (wholeGroupData M P R n y, planes (n+1) S y)) inferInstance := by
  apply le_antisymm
  · apply ConditionalTransport.comap_le_of_factor
      (p := fun v : WholeGroupData M P R n × (S → Arr I M.Y (n+1)) =>
        (v.1.1, tupleUnion R S (v.1.2,v.2))) (by fun_prop)
    funext y
    apply Prod.ext
    · rfl
    · funext i
      simp only [Function.comp_apply, wholeGroupData,tupleUnion,planes]
      split_ifs <;> rfl
  · apply ConditionalTransport.comap_le_of_factor
      (p := fun v : WholeGroupData M P (R ∪ S) n =>
        ((v.1,tupleSelect R (R∪S) Finset.subset_union_left v.2),
          tupleSelect S (R∪S) Finset.subset_union_right v.2)) (by fun_prop)
    rfl

lemma splitRowScreen (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint (R ∪ S) D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    HasCondDistrib (cells M A D n)
      (fun y => (wholeGroupData M P R n y, planes (n+1) S y))
      ((splitRowKernel M P A R S D n).comap
        (Prod.map id (columnRestrict M A S n)) (by fun_prop)) (M.law (n+2)) := by
  apply ConditionalTransport.recondition (measurable_wholeGroupData M P (R∪S) n)
    (by fun_prop) (measurable_cells M A D n)
    (fullGroupedLocality M hM P A (R∪S) D hP hPA hcard hproper hCD hcover hD n)
    (wholeSplit_field M P R S n)
  apply Filter.Eventually.of_forall
  intro y
  change (condDistrib (cells M A D n) (groupData M A (R∪S) n) (M.law (n+2)))
      (groupSelect M P A (R∪S) n (wholeGroupData M P (R∪S) n y)) =
    (condDistrib (cells M A D n) (groupData M A (R∪S) n) (M.law (n+2))) _
  congr 1
  apply Prod.ext
  · rfl
  · funext i a
    simp only [groupSelect,splitOwnData,Prod.map_apply,Function.id_def,wholeGroupData,
      tupleUnion,columnRestrict,planes]
    split_ifs <;> rfl

lemma splitRowScreen_fibre (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint (R ∪ S) D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      HasCondDistrib (cells M A D n) (planes (n+1) S)
        (((splitRowKernel M P A R S D n).sectR u).comap
          (columnRestrict M A S n) (measurable_columnRestrict M A S n))
        (condDistrib id (wholeGroupData M P R n) (M.law (n+2)) u) := by
  have hη := (show HasCondDistrib id (wholeGroupData M P R n)
      (condDistrib id (wholeGroupData M P R n) (M.law (n+2))) (M.law (n+2)) from
      ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) (by fun_prop) measurable_id.aemeasurable).symm⟩)
  exact ConditionalFibres.disintegrate (measurable_planes _ _) (measurable_cells M A D n)
    hη (splitRowScreen M hM P A R S D hP hPA hcard hproper hCD hcover hD n)

abbrev squareFibre (P R : Finset I) (n : ℕ) :=
  condDistrib id (wholeGroupData M P R n) (M.law (n+2))
abbrev cellLaw (A S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  groupMarginal M A S n e

lemma cellMarginal_fibre (hM : M.IsSaturated) (P A R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hproper : P ∪ A ≠ Finset.univ) (hRS : Disjoint R S)
    (hcols : R ∪ S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      MeasurePreserving (columnRestrict M A S n)
        ((squareFibre M P R n u).map (planes (n+1) S)) (cellLaw M A S n u.1.1) := by
  have hη : HasCondDistrib id (wholeGroupData M P R n) (squareFibre M P R n) (M.law (n+2)) :=
    ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) (by fun_prop) measurable_id.aemeasurable).symm⟩
  have h := ConditionalFibres.marginal (measurable_cells M A S n) hη
    (group_intermediate_marginal M hM P A R S hP hPA hproper hRS hcols n)
  filter_upwards [h] with u hu
  refine ⟨measurable_columnRestrict M A S n, ?_⟩
  rw [Measure.map_map (measurable_columnRestrict M A S n) (measurable_planes _ _),
    columnRestrict_planes]
  exact hu.map_eq

theorem grouped_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      let μ := squareFibre M P R n u
      let hs : MeasurePreserving (planes (n+1) S) μ (μ.map (planes (n+1) S)) :=
        ⟨measurable_planes _ _, rfl⟩
      let ht : MeasurePreserving (planes (n+1) D) μ (μ.map (planes (n+1) D)) :=
        ⟨measurable_planes _ _, rfl⟩
      ∃ (ha : MeasurePreserving (columnRestrict M A S n) (μ.map (planes (n+1) S)) (cellLaw M A S n u.1.1))
        (hb : MeasurePreserving (columnRestrict M B S n) (μ.map (planes (n+1) S)) (cellLaw M B S n u.1.1))
        (hc : MeasurePreserving (columnRestrict M A D n) (μ.map (planes (n+1) D)) (cellLaw M A D n u.1.1))
        (hd : MeasurePreserving (columnRestrict M B D n) (μ.map (planes (n+1) D)) (cellLaw M B D n u.1.1)),
        let F := JoiningOperator.operator (ha.comp hs) (hc.comp ht)
        let G := JoiningOperator.operator (hb.comp hs) (hd.comp ht)
        let K := JoiningOperator.operator ha hb
        let N := JoiningOperator.operator hc hd
        F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint := by
  have hSD' : Disjoint (R ∪ S) D := Finset.disjoint_union_left.mpr ⟨hRD,hSD⟩
  have hDS' : Disjoint (R ∪ D) S := Finset.disjoint_union_left.mpr ⟨hRS,hSD.symm⟩
  have hcover' : (R ∪ D) ∪ S = Finset.univ := by simpa only [Finset.union_right_comm] using hcover
  have hproperRS : R ∪ S ≠ Finset.univ := by
    intro h
    obtain ⟨d,hd⟩ := hD
    exact Finset.disjoint_left.mp hSD' (h ▸ Finset.mem_univ d) hd
  have hproperRD : R ∪ D ≠ Finset.univ := by
    intro h
    obtain ⟨s,hs⟩ := hS
    exact Finset.disjoint_left.mp hDS' (h ▸ Finset.mem_univ s) hs
  filter_upwards [cellMarginal_fibre M hM P A R S hP hPA hproperA hRS hproperRS n,
    cellMarginal_fibre M hM P B R S hP hPB hproperB hRS hproperRS n,
    cellMarginal_fibre M hM P A R D hP hPA hproperA hRD hproperRD n,
    cellMarginal_fibre M hM P B R D hP hPB hproperB hRD hproperRD n,
    splitRowScreen_fibre M hM P A R S D hP hPA hcardA hproperA hSD' hcover hD n,
    splitRowScreen_fibre M hM P B R S D hP hPB hcardB hproperB hSD' hcover hD n,
    splitRowScreen_fibre M hM P A R D S hP hPA hcardA hproperA hDS' hcover' hS n,
    splitRowScreen_fibre M hM P B R D S hP hPB hcardB hproperB hDS' hcover' hS n]
    with u ha hb hc hd hac hbd hca hdb
  refine ⟨ha,hb,hc,hd,?_⟩
  apply JoiningOperator.square_rectangle
    (hs := ⟨measurable_planes _ _, rfl⟩) (ht := ⟨measurable_planes _ _, rfl⟩)
    (κac := (splitRowKernel M P A R S D n).sectR u)
    (κbd := (splitRowKernel M P B R S D n).sectR u)
    (κca := (splitRowKernel M P A R D S n).sectR u)
    (κdb := (splitRowKernel M P B R D S n).sectR u)
  · simpa only [columnRestrict_planes] using hac
  · simpa only [columnRestrict_planes] using hbd
  · simpa only [columnRestrict_planes] using hca
  · simpa only [columnRestrict_planes] using hdb
end

universe u
variable {I : Type u} [Fintype I] [retained7 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowPairKernel (A R S D : Finset I) (n : ℕ) :
    Kernel (GroupData M A R n) ((S → A → Arr I M.Y n) × (D → A → Arr I M.Y n)) :=
  condDistrib (fun y => (cells M A S n y,cells M A D n y)) (groupData M A R n) (M.law (n+2))
instance rowPairKernel_markov (A R S D : Finset I) (n : ℕ) :
    IsMarkovKernel (rowPairKernel M A R S D n) := by unfold rowPairKernel; infer_instance

lemma rowPair_conditional (hM : M.IsSaturated) (P A R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A)
    (hcard : P.card + A.card + 1 ≤ Fintype.card I)
    (hproper : P ∪ A ≠ Finset.univ) (hCD : Disjoint R (S∪D))
    (hcover : R ∪ (S∪D) = Finset.univ) (hSD : (S∪D).Nonempty) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M A D n y)) (wholeGroupData M P R n)
      ((rowPairKernel M A R S D n).comap (groupSelect M P A R n)
        (measurable_groupSelect M P A R n)) (M.law (n+2)) := by
  let f : (↥(S∪D) → A → Arr I M.Y n) → (S → A → Arr I M.Y n) × (D → A → Arr I M.Y n) :=
    fun y => (tupleSelect S (S∪D) Finset.subset_union_left y,
      tupleSelect D (S∪D) Finset.subset_union_right y)
  have hf : Measurable f := by fun_prop
  have h := (fullGroupedLocality M hM P A R (S∪D) hP hPA hcard hproper hCD hcover hSD n).comp_left hf
  rw [← Kernel.comap_map_comm _ _ hf] at h
  have : IsMarkovKernel ((condDistrib (cells M A (S∪D) n) (groupData M A R n) (M.law (n+2))).map f) :=
    Kernel.IsMarkovKernel.map _ hf
  have h' := ConditionalScreens.canonical_screen (measurable_wholeGroupData M P R n)
    (groupSelect M P A R n) (measurable_groupSelect M P A R n) h
  rw [groupSelect_observation] at h'
  exact h'

omit [DecidableEq I] in
lemma parameterEquiv_plane (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    parameterEquiv M P n (plane n (Fin.last n) j ((parameterEquiv M P (n+1)).symm v)) =
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  apply Prod.ext
  · funext w
    simp [parameterEquiv, plane, Fin.insertNth_last', cons_snoc]
  · rfl

include retained7 in
lemma columnKernel_eq_posterior (P : Finset I) (n : ℕ) (j : I) (v : ParentData M P n) :
    columnKernel M P n j v = posterior M P n
      (plane (n+1) (Fin.last (n+1)) j v.1,
        fun p : P => plane n (Fin.last n) j (v.2 p)) := by
  let _ := retained7
  simp only [columnKernel,Kernel.comap_apply,Function.comp_apply,
    Kernel.map_apply _ (roll n).symm.measurable,ownPosterior, Kernel.map_apply _ (roll n).measurable]
  rw [Measure.map_map (roll n).symm.measurable (roll n).measurable,
    MeasurableEquiv.symm_comp_self,Measure.map_id,parameterEquiv_plane]

def columnGroupKernel (P S : Finset I) (n : ℕ) :
    Kernel (GroupData M P S n) (S → Arr I M.Y (n+1)) :=
  FiniteKernel.pi (fun j : S => (posterior M P n).comap
    (fun v => (plane (n+1) (Fin.last (n+1)) j v.1, fun p : P => v.2 j p)) (by fun_prop))
instance columnGroupKernel_markov (P S : Finset I) (n : ℕ) :
    IsMarkovKernel (columnGroupKernel M P S n) := by unfold columnGroupKernel; infer_instance

def columnOwnData (P R S : Finset I) (n : ℕ) (u : WholeGroupData M P R n) : GroupData M P S n :=
  (u.1.1,rowRestrict M P S n u.1.2)
omit [DecidableEq I] in
@[fun_prop] lemma measurable_columnOwnData (P R S : Finset I) (n : ℕ) :
    Measurable (columnOwnData M P R S n) := by unfold columnOwnData; fun_prop

lemma columns_group_screen (hM : M.IsSaturated) (P R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (planes (n+1) S) (wholeGroupData M P R n)
      ((columnGroupKernel M P S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (parentData M P n)
    (fun j => plane (n+1) (Fin.last (n+1)) j) (columnKernel M P n)
    Finset.subset_union_left Finset.subset_union_right hRS
    (columns_with_parents M hM P hP n (R∪S) hproper)
  have he : (columnGroupKernel M P S n).comap (columnOwnData M P R S n)
      (measurable_columnOwnData M P R S n) =
      (FiniteKernel.pi (fun j : S => columnKernel M P n j)).prodMkRight (R → Arr I M.Y (n+1)) := by
    ext v : 1
    change Measure.pi (fun j : S => posterior M P n _) =
      Measure.pi (fun j : S => columnKernel M P n j v.1)
    congr 1
    funext j
    exact (columnKernel_eq_posterior M P n j v.1).symm
  rw [he]
  exact h

end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace

section

lemma aestronglyMeasurable_of_inner {U H : Type*} [MeasurableSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H] {μ : Measure U} {f : U → H}
    (hf : ∀ h : H, AEStronglyMeasurable (fun u => inner ℂ h (f u)) μ) :
    AEStronglyMeasurable f μ := by
  borelize H
  let e : H → ℕ → ℂ := fun h n => inner ℂ (TopologicalSpace.denseSeq H n) h
  have hec : Continuous e := by fun_prop
  have hei : Function.Injective e := by
    intro v w h
    have hh : (fun z : H => inner ℂ z v) = (fun z : H => inner ℂ z w) := by
      apply (TopologicalSpace.denseRange_denseSeq H).equalizer (by fun_prop) (by fun_prop)
      funext n
      exact congrFun h n
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_right, congrFun hh (v - w), sub_self]
  have he := hec.measurableEmbedding hei
  apply (he.aemeasurable_comp_iff.mp ?_).aestronglyMeasurable
  exact AEMeasurable.of_eval (fun n => (hf (TopologicalSpace.denseSeq H n)).aemeasurable)

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)

def family (u : U) : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν := by
  classical
  exact if h : MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ
  then operator h.1 h.2 else 0

lemma family_eq (u : U) (hx : MeasurePreserving Prod.fst (κ u) ν)
    (hy : MeasurePreserving Prod.snd (κ u) ρ) : family κ ν ρ u = operator hx hy := by
  classical
  unfold family
  split_ifs with h
  · rfl
  · exact (h ⟨hx, hy⟩).elim

lemma family_norm_le (u : U) : ‖family κ ν ρ u‖ ≤ 1 := by
  classical
  unfold family
  split_ifs with h
  · exact operator_norm_le h.1 h.2
  · simp

variable {κ ν ρ} {m : Measure U}

lemma family_inner (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    (fun u => inner ℂ g (family κ ν ρ u h)) =ᵐ[m]
      (fun u => ∫ p, inner ℂ (g p.1) (h p.2) ∂κ u) := by
  filter_upwards [hm] with u hu
  rw [family_eq κ ν ρ u hu.1 hu.2]
  exact inner_operator hu.1 hu.2 g h

lemma family_inner_aestronglyMeasurable (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    AEStronglyMeasurable (fun u => inner ℂ g (family κ ν ρ u h)) m := by
  have hf : StronglyMeasurable (fun p : X × Y => inner ℂ (g p.1) (h p.2)) :=
    (g.1.stronglyMeasurable.comp_measurable measurable_fst).inner
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)
  exact hf.integral_kernel.aestronglyMeasurable.congr (family_inner hm g h).symm

lemma family_aestronglyMeasurable [SecondCountableTopology (Lp ℂ 2 ν)]
    (hm : ∀ᵐ u ∂m,
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ)
    (h : Lp ℂ 2 ρ) : AEStronglyMeasurable (fun u => family κ ν ρ u h) m :=
  aestronglyMeasurable_of_inner (fun g => family_inner_aestronglyMeasurable hm g h)

end


lemma family_eq_of_joint {Ω U A B : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ν : Measure A} {ρ : Measure B} {a : Ω → A} {b : Ω → B}
    (κ : Kernel U (A × B)) (u : U)
    (hab : MeasurePreserving (fun ω => (a ω, b ω)) μ (κ u))
    (ha : MeasurePreserving Prod.fst (κ u) ν) (hb : MeasurePreserving Prod.snd (κ u) ρ) :
    family κ ν ρ u = operator (ha.comp hab) (hb.comp hab) := by
  rw [family_eq κ ν ρ u ha hb]
  exact (operator_pullback hab ha hb).symm

variable {Ω U X Y V W A B C D : Type*}
  [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
  [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
  [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {a : Ω → A} {b : Ω → B} {c : Ω → C} {d : Ω → D}
  {x : U → X} {y : U → Y} {v : U → V} {w : U → W}
  {νa : Measure A} {νb : Measure B} {νc : Measure C} {νd : Measure D}
  {η : Kernel U Ω} [IsMarkovKernel η]
  {F : Kernel X (A × C)} [IsMarkovKernel F]
  {G : Kernel Y (B × D)} [IsMarkovKernel G]
  {K : Kernel V (A × B)} [IsMarkovKernel K]
  {N : Kernel W (C × D)} [IsMarkovKernel N]
  {α : Kernel (U × A) C} [IsMarkovKernel α]
  {β : Kernel (U × B) D} [IsMarkovKernel β]
  {γ : Kernel (U × C) A} [IsMarkovKernel γ]
  {δ : Kernel (U × D) B} [IsMarkovKernel δ]

theorem conditional_square_rectangle
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    (hx : Measurable x) (hy : Measurable y) (hv : Measurable v) (hw : Measurable w)
    (hη : HasCondDistrib id u η μ)
    (hF : HasCondDistrib (fun ω => (a ω, c ω)) u (F.comap x hx) μ)
    (hG : HasCondDistrib (fun ω => (b ω, d ω)) u (G.comap y hy) μ)
    (hK : HasCondDistrib (fun ω => (a ω, b ω)) u (K.comap v hv) μ)
    (hN : HasCondDistrib (fun ω => (c ω, d ω)) u (N.comap w hw) μ)
    (hg : ∀ᵐ q ∂μ.map u,
      (MeasurePreserving Prod.fst (F (x q)) νa ∧ MeasurePreserving Prod.snd (F (x q)) νc) ∧
      (MeasurePreserving Prod.fst (G (y q)) νb ∧ MeasurePreserving Prod.snd (G (y q)) νd) ∧
      (MeasurePreserving Prod.fst (K (v q)) νa ∧ MeasurePreserving Prod.snd (K (v q)) νb) ∧
      (MeasurePreserving Prod.fst (N (w q)) νc ∧ MeasurePreserving Prod.snd (N (w q)) νd))
    (hα : HasCondDistrib c (fun ω => (u ω, (a ω, b ω)))
      (α.comap (fun p : U × (A × B) => (p.1, p.2.1)) (by fun_prop)) μ)
    (hβ : HasCondDistrib d (fun ω => (u ω, (a ω, b ω)))
      (β.comap (fun p : U × (A × B) => (p.1, p.2.2)) (by fun_prop)) μ)
    (hγ : HasCondDistrib a (fun ω => (u ω, (c ω, d ω)))
      (γ.comap (fun p : U × (C × D) => (p.1, p.2.1)) (by fun_prop)) μ)
    (hδ : HasCondDistrib b (fun ω => (u ω, (c ω, d ω)))
      (δ.comap (fun p : U × (C × D) => (p.1, p.2.2)) (by fun_prop)) μ) :
    ∀ᵐ q ∂μ.map u,
      family F νa νc (x q) ∘L family N νc νd (w q) =
        family K νa νb (v q) ∘L family G νb νd (y q) ∧
      (family F νa νc (x q)).adjoint ∘L family K νa νb (v q) =
        family N νc νd (w q) ∘L (family G νb νd (y q)).adjoint := by
  have hFm := ConditionalFibres.marginal (ha.prodMk hc) hη hF
  have hGm := ConditionalFibres.marginal (hb.prodMk hd) hη hG
  have hKm := ConditionalFibres.marginal (ha.prodMk hb) hη hK
  have hNm := ConditionalFibres.marginal (hc.prodMk hd) hη hN
  have hαm := ConditionalFibres.disintegrate (ha.prodMk hb) hc hη hα
  have hβm := ConditionalFibres.disintegrate (ha.prodMk hb) hd hη hβ
  have hγm := ConditionalFibres.disintegrate (hc.prodMk hd) ha hη hγ
  have hδm := ConditionalFibres.disintegrate (hc.prodMk hd) hb hη hδ
  filter_upwards [hFm, hGm, hKm, hNm, hαm, hβm, hγm, hδm, hg] with q hf hg hk hn hα hβ hγ hδ he
  obtain ⟨heF, heG, heK, heN⟩ := he
  have hr := square_rectangle hk hn heK.1 heK.2 heN.1 heN.2
    (κac := α.sectR q) (κbd := β.sectR q) (κca := γ.sectR q) (κdb := δ.sectR q)
    hα hβ hγ hδ
  rw [family_eq_of_joint F _ hf heF.1 heF.2,
      family_eq_of_joint G _ hg heG.1 heG.2,
      family_eq K _ _ _ heK.1 heK.2, family_eq N _ _ _ heN.1 heN.2]
  exact hr

end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace JoiningOperator
variable {A B C D : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
def IsRectangle (F : C →L[ℂ] A) (G : D →L[ℂ] B) (K : B →L[ℂ] A) (N : D →L[ℂ] C) : Prop :=
  F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint
end JoiningOperator
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def columnPairKernel (P A B S : Finset I) (n : ℕ) :
    Kernel (GroupData M P S n) ((S → A → Arr I M.Y n) × (S → B → Arr I M.Y n)) :=
  (columnGroupKernel M P S n).map (fun y => (columnRestrict M A S n y,columnRestrict M B S n y))
instance columnPairKernel_markov (P A B S : Finset I) (n : ℕ) :
    IsMarkovKernel (columnPairKernel M P A B S n) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

omit [DecidableEq I] in
lemma columnPairRestrict_planes (A B S : Finset I) (n : ℕ) :
    (fun y => (columnRestrict M A S n y,columnRestrict M B S n y)) ∘ planes (n+1) S =
      fun y => (cells M A S n y,cells M B S n y) := by
  funext y
  exact Prod.ext (congrFun (columnRestrict_planes M A S n) y)
    (congrFun (columnRestrict_planes M B S n) y)

lemma columnPair_conditional (hM : M.IsSaturated) (P A B R S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hRS : Disjoint R S)
    (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (wholeGroupData M P R n)
      ((columnPairKernel M P A B S n).comap (columnOwnData M P R S n)
        (measurable_columnOwnData M P R S n)) (M.law (n+2)) := by
  have h := (columns_group_screen M hM P R S hP hRS hproper n).comp_left
    ((measurable_columnRestrict M A S n).prodMk (measurable_columnRestrict M B S n))
  rw [← Kernel.comap_map_comm _ _ (by fun_prop)] at h
  simpa only [columnPairKernel,columnPairRestrict_planes] using h

omit [DecidableEq I] in
lemma pair_fst_push {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ρ : Measure (A × B)} {ν : Measure A} {a : Ω → A} {b : Ω → B}
    (hab : MeasurePreserving (fun ω => (a ω,b ω)) μ ρ) (ha : MeasurePreserving a μ ν) :
    MeasurePreserving Prod.fst ρ ν := by
  refine ⟨measurable_fst,?_⟩
  rw [← hab.map_eq,Measure.map_map measurable_fst hab.measurable]
  exact ha.map_eq

omit [DecidableEq I] in
lemma pair_snd_push {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} {ρ : Measure (A × B)} {ν : Measure B} {a : Ω → A} {b : Ω → B}
    (hab : MeasurePreserving (fun ω => (a ω,b ω)) μ ρ) (hb : MeasurePreserving b μ ν) :
    MeasurePreserving Prod.snd ρ ν := by
  refine ⟨measurable_snd,?_⟩
  rw [← hab.map_eq,Measure.map_map measurable_snd hab.measurable]
  exact hb.map_eq

def rowEdge (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (p : GroupData M A R n) : Lp ℂ 2 (cellLaw M A D n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  JoiningOperator.family (rowPairKernel M A R S D n)
    (cellLaw M A S n e) (cellLaw M A D n e) p

def columnEdge (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (p : GroupData M P S n) : Lp ℂ 2 (cellLaw M B S n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  JoiningOperator.family (columnPairKernel M P A B S n)
    (cellLaw M A S n e) (cellLaw M B S n e) p

theorem grouped_family_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ u ∂(M.law (n+2)).map (wholeGroupData M P R n),
      let F := rowEdge M A R S D n u.1.1 (groupSelect M P A R n u)
      let G := rowEdge M B R S D n u.1.1 (groupSelect M P B R n u)
      let K := columnEdge M P A B S n u.1.1 (columnOwnData M P R S n u)
      let N := columnEdge M P A B D n u.1.1 (columnOwnData M P R D n u)
      JoiningOperator.IsRectangle F G K N := by
  have hRSD : Disjoint R (S∪D) := Finset.disjoint_union_right.mpr ⟨hRS,hRD⟩
  have hcover' : R ∪ (S∪D) = Finset.univ := by simpa only [Finset.union_assoc] using hcover
  have hproperRS : R ∪ S ≠ Finset.univ := by
    intro h
    obtain ⟨d,hd⟩ := hD
    exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨hRD,hSD⟩) (h ▸ Finset.mem_univ d) hd
  have hproperRD : R ∪ D ≠ Finset.univ := by
    intro h
    obtain ⟨s,hs⟩ := hS
    exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨hRS,hSD.symm⟩) (h ▸ Finset.mem_univ s) hs
  have hη : HasCondDistrib id (wholeGroupData M P R n) (squareFibre M P R n) (M.law (n+2)) :=
    ⟨(by fun_prop), (compProd_map_condDistrib (μ := M.law (n+2)) (by fun_prop) measurable_id.aemeasurable).symm⟩
  have hF := ConditionalFibres.marginal ((measurable_cells M A S n).prodMk (measurable_cells M A D n)) hη
    (rowPair_conditional M hM P A R S D hP hPA hcardA hproperA hRSD hcover' (hS.mono Finset.subset_union_left) n)
  have hG := ConditionalFibres.marginal ((measurable_cells M B S n).prodMk (measurable_cells M B D n)) hη
    (rowPair_conditional M hM P B R S D hP hPB hcardB hproperB hRSD hcover' (hS.mono Finset.subset_union_left) n)
  have hK := ConditionalFibres.marginal ((measurable_cells M A S n).prodMk (measurable_cells M B S n)) hη
    (columnPair_conditional M hM P A B R S hP hRS hproperRS n)
  have hN := ConditionalFibres.marginal ((measurable_cells M A D n).prodMk (measurable_cells M B D n)) hη
    (columnPair_conditional M hM P A B R D hP hRD hproperRD n)
  filter_upwards [grouped_rectangle M hM P A B R S D hP hPA hPB hcardA hcardB hproperA hproperB
    hRS hRD hSD hcover hS hD n,hF,hG,hK,hN] with u hu hf hg hk hn
  obtain ⟨ha,hb,hc,hd,hr⟩ := hu
  let hs : MeasurePreserving (planes (n+1) S) (squareFibre M P R n u)
      ((squareFibre M P R n u).map (planes (n+1) S)) := ⟨measurable_planes _ _,rfl⟩
  let ht : MeasurePreserving (planes (n+1) D) (squareFibre M P R n u)
      ((squareFibre M P R n u).map (planes (n+1) D)) := ⟨measurable_planes _ _,rfl⟩
  have hks : MeasurePreserving (fun y => (columnRestrict M A S n y,columnRestrict M B S n y))
      ((squareFibre M P R n u).map (planes (n+1) S))
      (columnPairKernel M P A B S n (columnOwnData M P R S n u)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_map (by fun_prop) (measurable_planes _ _)]
    rw [columnPairRestrict_planes]
    exact hk.map_eq
  have hnt : MeasurePreserving (fun y => (columnRestrict M A D n y,columnRestrict M B D n y))
      ((squareFibre M P R n u).map (planes (n+1) D))
      (columnPairKernel M P A B D n (columnOwnData M P R D n u)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_map (by fun_prop) (measurable_planes _ _)]
    rw [columnPairRestrict_planes]
    exact hn.map_eq
  simp only [← columnRestrict_planes M A S n, ← columnRestrict_planes M A D n] at hf
  simp only [← columnRestrict_planes M B S n, ← columnRestrict_planes M B D n] at hg
  dsimp only [rowEdge,columnEdge,JoiningOperator.IsRectangle]
  rw [JoiningOperator.family_eq_of_joint (rowPairKernel M A R S D n) (groupSelect M P A R n u) hf (pair_fst_push hf (ha.comp hs)) (pair_snd_push hf (hc.comp ht)),
    JoiningOperator.family_eq_of_joint (rowPairKernel M B R S D n) (groupSelect M P B R n u) hg (pair_fst_push hg (hb.comp hs)) (pair_snd_push hg (hd.comp ht)),
    JoiningOperator.family_eq_of_joint _ _ hks (pair_fst_push hks ha) (pair_snd_push hks hb),
    JoiningOperator.family_eq_of_joint _ _ hnt (pair_fst_push hnt hc) (pair_snd_push hnt hd)]
  exact hr
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory
namespace ConditionalFibres
variable {Ω U X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U}
  {η : Kernel U Ω} [IsMarkovKernel η]

lemma ae_ae (hη : HasCondDistrib id u η μ) {p : Ω → Prop} (hp : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ a ∂μ.map u, ∀ᵐ ω ∂η a, p ω := by
  have hs : MeasurePreserving Prod.snd (μ.map u ⊗ₘ η) μ := by
    refine ⟨measurable_snd, ?_⟩
    rw [← hη.map_eq, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hη.aemeasurable]
    exact Measure.map_id
  exact Measure.ae_ae_of_ae_compProd (hs.quasiMeasurePreserving.ae hp)

lemma parameter_fixed [StandardBorelSpace U] (hu : Measurable u)
    (hη : HasCondDistrib id u η μ) :
    ∀ᵐ a ∂μ.map u, ∀ᵐ ω ∂η a, u ω = a := by
  apply Measure.ae_ae_of_ae_compProd (p := fun q => u q.2 = q.1)
  rw [← hη.map_eq]
  exact (ae_map_iff hη.aemeasurable (measurableSet_eq_fun (hu.comp measurable_snd) measurable_fst)).mpr
    (Filter.Eventually.of_forall fun _ => rfl)

lemma indep_of_screen [StandardBorelSpace X] [StandardBorelSpace Y]
    {x : Ω → X} {y : Ω → Y} {α : Kernel U Y} [IsMarkovKernel α]
    (hx : Measurable x) (hy : Measurable y)
    (hη : HasCondDistrib id u η μ)
    (h : HasCondDistrib y (fun ω => (u ω,x ω)) (α.prodMkRight X) μ) :
    ∀ᵐ a ∂μ.map u, IndepFun x y (η a) := by
  filter_upwards [disintegrate hx hy hη h] with a ha
  have he : (α.prodMkRight X).sectR a = Kernel.const X (α a) := by
    ext x : 1
    rfl
  rw [he] at ha
  apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr
  rw [ha.map_eq, ha.hasLaw_of_const.map_eq, Measure.compProd_const]

lemma triple_product {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hxy : IndepFun x y μ) (hxyz : IndepFun (fun ω => (x ω,y ω)) z μ) :
    MeasurePreserving (fun ω => (x ω,y ω,z ω)) μ
      ((μ.map x).prod ((μ.map y).prod (μ.map z))) := by
  refine ⟨hx.prodMk (hy.prodMk hz),?_⟩
  have h := hxyz.map_prod_eq_prod_map_map (hx.prodMk hy).aemeasurable hz.aemeasurable
  rw [hxy.map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable] at h
  have h' := congrArg (fun ν => ν.map MeasurableEquiv.prodAssoc) h
  rw [Measure.map_map (by fun_prop) ((hx.prodMk hy).prodMk hz), Measure.prodAssoc_prod] at h'
  exact h'

end ConditionalFibres

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rows_indep_fibre (hM : M.IsSaturated) (P A : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (parents M P (n+1)) (parents M A (n+1)) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun a => plane (n+1) 0 a)
    (fun a => (M.ownKernel (n+1)).comap (plane (n+1) 0 a) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hPA
    (rows_conditional M hM (P∪A) hproper n)
  exact ConditionalFibres.indep_of_screen (measurable_parents M P _) (measurable_parents M A _)
    (M.ownKernel_conditional (n+2)) h

lemma columns_indep_fibre (S D : Finset I)
    (hSD : Disjoint S D) (hproper : S ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (planes (n+1) S) (planes (n+1) D) (M.ownKernel (n+2) e) := by
  have h := ConditionalReveal.disjoint_families (M.law (n+2)) (amap M.par (n+2))
    (fun j => plane (n+1) (Fin.last (n+1)) j)
    (fun j => (M.ownKernel (n+1)).comap (plane (n+1) (Fin.last (n+1)) j) (measurable_plane _ _ _))
    Finset.subset_union_left Finset.subset_union_right hSD
    (M.planes_conditional (n+1) (S∪D) hproper)
  exact ConditionalFibres.indep_of_screen (measurable_planes _ _) (measurable_planes _ _)
    (M.ownKernel_conditional (n+2)) h

omit [DecidableEq I] in
lemma rowRestrict_parents (A S : Finset I) (n : ℕ) :
    rowRestrict M A S n ∘ parents M A (n+1) = cells M A S n := rfl

lemma cells_indep_rows_fibre (hM : M.IsSaturated) (P A S R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp (measurable_rowRestrict M P S n) (measurable_rowRestrict M A R n)

lemma cells_indep_columns_fibre (P A S R : Finset I)
    (hSR : Disjoint S R) (hproper : S ∪ R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (cells M P S n) (cells M A R n) (M.ownKernel (n+2) e) := by
  filter_upwards [columns_indep_fibre M S R hSR hproper n] with e he
  simpa only [columnRestrict_planes] using
    he.comp (measurable_columnRestrict M P S n) (measurable_columnRestrict M A R n)

lemma cells_colpair_indep_row_fibre (hM : M.IsSaturated) (P A S D R : Finset I)
    (hPA : Disjoint P A) (hproper : P ∪ A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (fun y => (cells M P S n y,cells M P D n y)) (cells M A R n)
        (M.ownKernel (n+2) e) := by
  filter_upwards [rows_indep_fibre M hM P A hPA hproper n] with e he
  exact he.comp ((measurable_rowRestrict M P S n).prodMk (measurable_rowRestrict M P D n))
    (measurable_rowRestrict M A R n)

lemma cells_rowpair_indep_column_fibre (A B P R S : Finset I)
    (hRS : Disjoint R S) (hproper : R ∪ S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      IndepFun (fun y => (cells M A R n y,cells M B R n y)) (cells M P S n)
        (M.ownKernel (n+2) e) := by
  filter_upwards [columns_indep_fibre M R S hRS hproper n] with e he
  have h := he.comp ((measurable_columnRestrict M A R n).prodMk
    (measurable_columnRestrict M B R n)) (measurable_columnRestrict M P S n)
  simpa only [columnPairRestrict_planes,columnRestrict_planes] using h

theorem grouped_product_triples (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hPA : Disjoint P A) (hPB : Disjoint P B) (hAB : Disjoint A B)
    (hproperPA : P ∪ A ≠ Finset.univ) (hproperPB : P ∪ B ≠ Finset.univ)
    (hproperAB : A ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hproperRS : R ∪ S ≠ Finset.univ) (hproperRD : R ∪ D ≠ Finset.univ)
    (hproperSD : S ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μ := M.ownKernel (n+2) e
      let x := cells M A R n
      let y := cells M B R n
      let c := cells M P S n
      let d := cells M P D n
      MeasurePreserving (fun ω => (c ω,d ω,x ω)) μ
        ((μ.map c).prod ((μ.map d).prod (μ.map x))) ∧
      MeasurePreserving (fun ω => (c ω,d ω,y ω)) μ
        ((μ.map c).prod ((μ.map d).prod (μ.map y))) ∧
      MeasurePreserving (fun ω => (x ω,y ω,c ω)) μ
        ((μ.map x).prod ((μ.map y).prod (μ.map c))) ∧
      MeasurePreserving (fun ω => (x ω,y ω,d ω)) μ
        ((μ.map x).prod ((μ.map y).prod (μ.map d))) := by
  filter_upwards [cells_colpair_indep_row_fibre M hM P A S D R hPA hproperPA n,
    cells_colpair_indep_row_fibre M hM P B S D R hPB hproperPB n,
    cells_rowpair_indep_column_fibre M A B P R S hRS hproperRS n,
    cells_rowpair_indep_column_fibre M A B P R D hRD hproperRD n,
    cells_indep_rows_fibre M hM A B R R hAB hproperAB n,
    cells_indep_columns_fibre M P P S D hSD hproperSD n] with e hxa hxb hcs hds hxy hcd
  exact ⟨ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hcd hxa,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hcd hxb,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hxy hcs,
    ConditionalFibres.triple_product (by fun_prop) (by fun_prop) (by fun_prop) hxy hds⟩


def fibreRowEdge (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (x : R → A → Arr I M.Y n) : Lp ℂ 2 (cellLaw M A D n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  rowEdge M A R S D n e (e,x)

def fibreColumnEdge (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2))
    (c : S → P → Arr I M.Y n) : Lp ℂ 2 (cellLaw M B S n e) →L[ℂ] Lp ℂ 2 (cellLaw M A S n e) :=
  columnEdge M P A B S n e (e,c)

theorem grouped_fibre_rectangle (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hcardA : P.card + A.card + 1 ≤ Fintype.card I)
    (hcardB : P.card + B.card + 1 ≤ Fintype.card I)
    (hproperA : P ∪ A ≠ Finset.univ) (hproperB : P ∪ B ≠ Finset.univ)
    (hRS : Disjoint R S) (hRD : Disjoint R D) (hSD : Disjoint S D)
    (hcover : (R ∪ S) ∪ D = Finset.univ) (hS : S.Nonempty) (hD : D.Nonempty) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ y ∂M.ownKernel (n+2) e,
        JoiningOperator.IsRectangle
          (fibreRowEdge M A R S D n e (cells M A R n y))
          (fibreRowEdge M B R S D n e (cells M B R n y))
          (fibreColumnEdge M P A B S n e (cells M P S n y))
          (fibreColumnEdge M P A B D n e (cells M P D n y)) := by
  have h := ae_of_ae_map (measurable_wholeGroupData M P R n).aemeasurable
    (grouped_family_rectangle M hM P A B R S D hP hPA hPB hcardA hcardB hproperA hproperB
      hRS hRD hSD hcover hS hD n)
  filter_upwards [ConditionalFibres.ae_ae (M.ownKernel_conditional (n+2)) h,
    ConditionalFibres.parameter_fixed (measurable_amap M.measurable_par _) (M.ownKernel_conditional (n+2))]
    with e he hp
  filter_upwards [he,hp] with y hy hparam
  have ha := congrFun (groupSelect_observation M P A R n) y
  have hb := congrFun (groupSelect_observation M P B R n) y
  dsimp only [Function.comp_apply] at ha hb
  change JoiningOperator.IsRectangle
    (rowEdge M A R S D n (amap M.par (n+2) y) (groupSelect M P A R n (wholeGroupData M P R n y)))
    (rowEdge M B R S D n (amap M.par (n+2) y) (groupSelect M P B R n (wholeGroupData M P R n y)))
    (columnEdge M P A B S n (amap M.par (n+2) y) (columnOwnData M P R S n (wholeGroupData M P R n y)))
    (columnEdge M P A B D n (amap M.par (n+2) y) (columnOwnData M P R D n (wholeGroupData M P R n y))) at hy
  rw [ha,hb] at hy
  change JoiningOperator.IsRectangle
    (rowEdge M A R S D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M A R n y))
    (rowEdge M B R S D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M B R n y))
    (columnEdge M P A B S n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M P S n y))
    (columnEdge M P A B D n (amap M.par (n+2) y) (amap M.par (n+2) y,cells M P D n y)) at hy
  rw [hparam] at hy
  exact hy

end ArrayObjects.Object.Rolled
end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section ConditionalMarginals

section
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

lemma conditional_pair_marginals [StandardBorelSpace X] [StandardBorelSpace Y]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hux : IndepFun u x μ) (huy : IndepFun u y μ) :
    ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ := by
  have : IsProbabilityMeasure ν := hx.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hx.aemeasurable
  have : IsProbabilityMeasure ρ := hy.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hy.aemeasurable
  have : IsMarkovKernel (κ.map Prod.fst) := Kernel.IsMarkovKernel.map κ measurable_fst
  have : IsMarkovKernel (κ.map Prod.snd) := Kernel.IsMarkovKernel.map κ measurable_snd
  have hxc : HasCondDistrib x u (Kernel.const U ν) μ := by
    refine ⟨(hu.prodMk hx.measurable).aemeasurable, ?_⟩
    rw [Measure.compProd_const, ← hx.map_eq]
    exact hux.map_prod_eq_prod_map_map hu.aemeasurable hx.aemeasurable
  have hyc : HasCondDistrib y u (Kernel.const U ρ) μ := by
    refine ⟨(hu.prodMk hy.measurable).aemeasurable, ?_⟩
    rw [Measure.compProd_const, ← hy.map_eq]
    exact huy.map_prod_eq_prod_map_map hu.aemeasurable hy.aemeasurable
  have he1 := Kernel.ae_eq_of_compProd_eq
    ((hκ.comp_left measurable_fst).map_eq.symm.trans hxc.map_eq)
  have he2 := Kernel.ae_eq_of_compProd_eq
    ((hκ.comp_left measurable_snd).map_eq.symm.trans hyc.map_eq)
  filter_upwards [he1, he2] with a ha hb
  exact ⟨⟨measurable_fst, (Kernel.map_apply κ measurable_fst a).symm.trans ha⟩,
    ⟨measurable_snd, (Kernel.map_apply κ measurable_snd a).symm.trans hb⟩⟩

omit [IsProbabilityMeasure μ] in
lemma integrable_inner_comp (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    Integrable (fun ω => inner ℂ (g (x ω)) (h (y ω))) μ := by
  apply (L2.integrable_inner (pull hx g) (pull hy h)).congr
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

lemma family_setIntegral (hu : Measurable u)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (A : Set U) (hA : MeasurableSet A) (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    ∫ a in A, inner ℂ g (family κ ν ρ a h) ∂μ.map u =
      ∫ ω in u ⁻¹' A, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  let f : U × (X × Y) → ℂ := fun p =>
    (Prod.fst ⁻¹' A).indicator (fun p => inner ℂ (g p.2.1) (h p.2.2)) p
  have hfm : StronglyMeasurable f :=
    ((g.1.stronglyMeasurable.comp_measurable (by fun_prop)).inner
      (h.1.stronglyMeasurable.comp_measurable (by fun_prop))).indicator (measurable_fst hA)
  have hfi : Integrable f (μ.map u ⊗ₘ κ) := by
    rw [← hκ.map_eq]
    apply (integrable_map_measure hfm.aestronglyMeasurable hκ.aemeasurable).mpr
    exact (integrable_inner_comp hx hy g h).indicator (hu hA)
  calc
    _ = ∫ a in A, ∫ p, inner ℂ (g p.1) (h p.2) ∂κ a ∂μ.map u :=
      setIntegral_congr_ae hA ((family_inner hm g h).mono (fun _ ha _ => ha))
    _ = ∫ a, ∫ p, f (a, p) ∂κ a ∂μ.map u := by
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards with a
      by_cases ha : a ∈ A <;> simp [f, ha]
    _ = ∫ p, f p ∂μ.map u ⊗ₘ κ := (Measure.integral_compProd hfi).symm
    _ = ∫ ω, f (u ω, x ω, y ω) ∂μ := (hκ.integral_comp hfm.aestronglyMeasurable).symm
    _ = _ := by
      change ∫ ω, (u ⁻¹' A).indicator (fun ω => inner ℂ (g (x ω)) (h (y ω))) ω ∂μ = _
      exact integral_indicator (hu hA)

end


lemma ae_eq_zero_of_rectangles {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    {m : Measure (U × Y)} {f : U × Y → ℂ} (hf : Integrable f m)
    (hz : ∀ A B, MeasurableSet A → MeasurableSet B → ∫ p in A ×ˢ B, f p ∂m = 0) :
    f =ᵐ[m] 0 := by
  suffices ∀ S, MeasurableSet S → ∫ p in S, f p ∂m = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun S hS _ => this S hS)
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter generateFrom_prod.symm
      isPiSystem_prod with
  | empty => simp
  | basic S hS =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hS
    exact hz A B hA hB
  | compl S hS ih =>
    have htot : ∫ p, f p ∂m = 0 := by
      simpa using hz Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa [ih, htot] using integral_add_compl hS hf
  | iUnion S hdis hS ih => simp [integral_iUnion hS hdis hf.integrableOn, ih]

variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  {m : Measure (U × Y)} {ρ : Measure Y}

def weightedTest (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (h : Lp ℂ 2 ρ) : Lp ℂ 2 m :=
  (((Lp.memLp h).comp_measurePreserving hy).indicator (measurable_fst hA)).toLp _

lemma coe_weightedTest (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (h : Lp ℂ 2 ρ) :
    (weightedTest hy A hA h : U × Y → ℂ) =ᵐ[m]
      (Prod.fst ⁻¹' A).indicator (fun p => h p.2) := MemLp.coeFn_toLp _

lemma weightedTest_indicator [IsFiniteMeasure m] [IsFiniteMeasure ρ]
    (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B) :
    weightedTest hy A hA (indicatorConstLp 2 hB (measure_ne_top ρ B) (1 : ℂ)) =
      indicatorConstLp 2 (hA.prod hB) (measure_ne_top m _) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [coe_weightedTest hy A hA (indicatorConstLp 2 hB (measure_ne_top ρ B) (1 : ℂ)),
    hy.quasiMeasurePreserving.ae (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top ρ B) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hA.prod hB) (hμs := measure_ne_top m _) (c := (1 : ℂ))]
    with p hp hq hr
  rw [hp, hr]
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp_all


end ConditionalMarginals


variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

omit [IsProbabilityMeasure μ] in
lemma snd_observation (hu : Measurable u) (hy : MeasurePreserving y μ ρ) :
    MeasurePreserving Prod.snd (μ.map (fun ω => (u ω, y ω))) ρ := by
  refine ⟨measurable_snd, ?_⟩
  rw [Measure.map_map measurable_snd (hu.prodMk hy.measurable)]
  exact hy.map_eq

lemma weighted_inner (hu : Measurable u)
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (A : Set U) (hA : MeasurableSet A) (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx ⟨hu.prodMk hy.measurable, rfl⟩
      (weightedTest (snd_observation hu hy) A hA h)) =
      ∫ a in A, inner ℂ g (family κ ν ρ a h) ∂μ.map u := by
  rw [inner_operator, family_setIntegral hu hx hy hκ hm A hA]
  rw [← integral_indicator (hu hA)]
  apply integral_congr_ae
  have hz : MeasurePreserving (fun ω => (u ω, y ω)) μ (μ.map (fun ω => (u ω, y ω))) :=
    ⟨hu.prodMk hy.measurable, rfl⟩
  filter_upwards [hz.quasiMeasurePreserving.ae_eq_comp
    (coe_weightedTest (snd_observation hu hy) A hA h)] with ω hω
  simp only [Function.comp_apply] at hω
  rw [hω]
  by_cases ha : u ω ∈ A <;> simp [ha]

omit [IsMarkovKernel κ] in
lemma family_inner_integrable (hu : Measurable u)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    Integrable (fun a => inner ℂ g (family κ ν ρ a h)) (μ.map u) := by
  have : IsProbabilityMeasure (μ.map u) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hu.aemeasurable
  apply Integrable.of_bound (family_inner_aestronglyMeasurable hm g h) (‖g‖ * ‖h‖)
  filter_upwards with a
  calc
    _ ≤ ‖g‖ * ‖family κ ν ρ a h‖ := norm_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖family κ ν ρ a‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left ((family κ ν ρ a).le_opNorm h) (norm_nonneg _)
    _ ≤ _ := by grw [family_norm_le]; simp

lemma active_kernel [SecondCountableTopology (Lp ℂ 2 ρ)]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 ν) :
    (operator hx ⟨hu.prodMk hy.measurable, rfl⟩).adjoint g = 0 ↔
      ∀ᵐ a ∂μ.map u, (family κ ν ρ a).adjoint g = 0 := by
  let Q := operator hx (show MeasurePreserving (fun ω => (u ω, y ω)) μ
    (μ.map (fun ω => (u ω, y ω))) from ⟨hu.prodMk hy.measurable, rfl⟩)
  have : IsProbabilityMeasure (μ.map (fun ω => (u ω, y ω))) :=
    (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (hu.prodMk hy.measurable).aemeasurable
  have : IsProbabilityMeasure ρ := hy.map_eq ▸ (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hy.aemeasurable
  constructor
  · intro hz
    have hh (h : Lp ℂ 2 ρ) : ∀ᵐ a ∂μ.map u, inner ℂ g (family κ ν ρ a h) = 0 := by
      apply (family_inner_integrable hu hm g h).ae_eq_zero_of_forall_setIntegral_eq_zero
      intro A hA _
      rw [← weighted_inner hu hx hy hκ hm A hA, ← adjoint_inner_left, hz, inner_zero_left]
    filter_upwards [ae_all_iff.mpr (fun n => hh (TopologicalSpace.denseSeq (Lp ℂ 2 ρ) n))]
      with a ha
    have he : (fun h : Lp ℂ 2 ρ => inner ℂ ((family κ ν ρ a).adjoint g) h) =
        (fun _ => (0 : ℂ)) := by
      apply (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ρ)).equalizer (by fun_prop) (by fun_prop)
      funext n
      simpa only [Function.comp_apply, adjoint_inner_left] using ha n
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (congrFun he ((family κ ν ρ a).adjoint g))
  · intro hz
    apply Lp.ext
    apply (ae_eq_zero_of_rectangles (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (Q.adjoint g))) ?_).trans
      (Lp.coeFn_zero _ _ _).symm
    intro A B hA hB
    rw [← L2.inner_indicatorConstLp_one (hA.prod hB) (measure_ne_top _ _)]
    apply inner_eq_zero_symm.mp
    rw [← weightedTest_indicator (snd_observation hu hy) A hA B hB, adjoint_inner_left]
    change inner ℂ g (operator hx ⟨hu.prodMk hy.measurable, rfl⟩ _) = 0
    rw [weighted_inner hu hx hy hκ hm A hA]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hz] with a ha
    simp only [← adjoint_inner_left, ha, inner_zero_left, Pi.zero_apply]

end JoiningOperator

section

open MeasureTheory Filter ContinuousLinearMap
open scoped InnerProductSpace Topology

section EssentialKernel
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def essentialKernel (μ : Measure X) (A : X → E →L[ℂ] H) : Submodule ℂ E where
  carrier := {v | ∀ᵐ x ∂μ, A x v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∀ᵐ x ∂μ, A x (v + w) = 0
    change ∀ᵐ x ∂μ, A x v = 0 at hv
    change ∀ᵐ x ∂μ, A x w = 0 at hw
    filter_upwards [hv, hw] with x hx hy
    simp [map_add, hx, hy]
  smul_mem' := by
    intro c v hv
    change ∀ᵐ x ∂μ, A x (c • v) = 0
    change ∀ᵐ x ∂μ, A x v = 0 at hv
    filter_upwards [hv] with x hx
    simp [hx]

theorem essentialKernel.ae_annihilate [SecondCountableTopology E]
    (μ : Measure X) (A : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, ∀ v : essentialKernel μ A, A x v = 0 := by
  let K := essentialKernel μ A
  have h (n : ℕ) : ∀ᵐ x ∂μ, A x (TopologicalSpace.denseSeq K n) = 0 :=
    (TopologicalSpace.denseSeq K n).property
  filter_upwards [ae_all_iff.mpr h] with x hx
  have hh : (fun v : K => A x v) = (fun _ : K => (0 : H)) := by
    apply (TopologicalSpace.denseRange_denseSeq K).equalizer
      ((A x).continuous.comp continuous_subtype_val) continuous_const
    funext n
    exact hx n
  intro v
  exact congrFun hh v
end EssentialKernel

section EssentialRange
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def essentialRange (μ : Measure X) (F : X → E →L[ℂ] H) : Submodule ℂ H :=
  (essentialKernel μ (fun x => (F x).adjoint))ᗮ

lemma essentialRange.isClosed (μ : Measure X) (F : X → E →L[ℂ] H) :
    IsClosed (essentialRange μ F : Set H) := Submodule.isClosed_orthogonal _

instance essentialRange.completeSpace (μ : Measure X) (F : X → E →L[ℂ] H) :
    CompleteSpace (essentialRange μ F) := (essentialRange.isClosed μ F).completeSpace_coe

lemma essentialRange.ae_range_le [SecondCountableTopology H]
    (μ : Measure X) (F : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ essentialRange μ F := by
  filter_upwards [essentialKernel.ae_annihilate μ (fun x => (F x).adjoint)] with x hx
  rintro v ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  change inner ℂ z (F x w) = 0
  rw [← adjoint_inner_left, hx ⟨z, hz⟩, inner_zero_left]

lemma essentialRange.le_of_ae_range (μ : Measure X) (F : X → E →L[ℂ] H)
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (hF : ∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ V) :
    essentialRange μ F ≤ V := by
  let : CompleteSpace V := hV.completeSpace_coe
  have h : Vᗮ ≤ essentialKernel μ (fun x => (F x).adjoint) := by
    intro v hv
    change ∀ᵐ x ∂μ, (F x).adjoint v = 0
    filter_upwards [hF] with x hx
    apply ext_inner_right ℂ
    intro w
    rw [inner_zero_left, adjoint_inner_left]
    exact V.inner_left_of_mem_orthogonal (hx ⟨w, rfl⟩) hv
  simpa only [essentialRange, Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le h

omit [CompleteSpace J] in
lemma essentialRange.le_comap_of_ae_comp (μ : Measure X) (F : X → E →L[ℂ] H)
    (A : H →L[ℂ] J) (V : Submodule ℂ J) (hV : IsClosed (V : Set J))
    (hF : ∀ᵐ x ∂μ, LinearMap.range (A ∘L F x).toLinearMap ≤ V) :
    essentialRange μ F ≤ V.comap A.toLinearMap := by
  apply essentialRange.le_of_ae_range μ F _ (hV.preimage A.continuous)
  filter_upwards [hF] with x hx
  rintro v ⟨w, rfl⟩
  exact hx ⟨w, rfl⟩
end EssentialRange

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : ∀ v ∈ V, A v ∈ W) (hAa : ∀ w ∈ W, A.adjoint w ∈ V) :
    W.starProjection ∘L A = A ∘L V.starProjection := by
  ext v
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hA _ (V.starProjection_apply_mem v)
  · change A v - A (V.starProjection v) ∈ Wᗮ
    rw [← map_sub]
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    rw [← adjoint_inner_left]
    exact V.inner_right_of_mem_orthogonal (hAa w hw) (V.sub_starProjection_mem_orthogonal v)

lemma projection_commutes_of_invariant (V W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : ∀ w ∈ W, V.starProjection w ∈ W) :
    W.starProjection ∘L V.starProjection = V.starProjection ∘L W.starProjection := by
  apply projection_intertwines _ W W hVW
  simpa only [(isSelfAdjoint_starProjection V).adjoint_eq] using hVW

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

lemma active_eq_essentialRange [SecondCountableTopology (Lp ℂ 2 ρ)]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ) :
    (LinearMap.range (operator hx ⟨hu.prodMk hy.measurable, rfl⟩).toLinearMap).topologicalClosure =
      essentialRange (μ.map u) (family κ ν ρ) := by
  let Q := operator hx (show MeasurePreserving (fun ω => (u ω, y ω)) μ
    (μ.map (fun ω => (u ω, y ω))) from ⟨hu.prodMk hy.measurable, rfl⟩)
  have hker : Q.adjoint.ker = essentialKernel (μ.map u) (fun a => (family κ ν ρ a).adjoint) := by
    ext g
    exact active_kernel hu hx hy hκ hm g
  have h := (orthogonal_ker Q.adjoint).symm
  rw [adjoint_adjoint, hker] at h
  exact h
end


lemma kernel_measurableSet_eq_const {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]
    [StandardBorelSpace X] (κ : Kernel U X) [IsMarkovKernel κ]
    (ν : Measure X) [IsProbabilityMeasure ν] : MeasurableSet {u | κ u = ν} := by
  let e := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  let η : Kernel U ℝ := κ.map e
  have : IsMarkovKernel η := Kernel.IsMarkovKernel.map κ he.measurable
  have : IsProbabilityMeasure (ν.map e) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) he.measurable.aemeasurable
  have eq_iff (u : U) : κ u = ν ↔ ∀ q : ℚ, η u (Set.Iic (q : ℝ)) = ν.map e (Set.Iic (q : ℝ)) := by
    constructor
    · intro h q
      simp [η, Kernel.map_apply κ he.measurable, h]
    · intro h
      apply he.map_injective
      have h' : η u = ν.map e := by
        apply ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
        · intro S hS
          simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at hS
          obtain ⟨q, rfl⟩ := hS
          exact h q
        · simp
      simpa [η, Kernel.map_apply κ he.measurable] using h'
  simp_rw [eq_iff]
  simp_rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun q => measurableSet_eq_fun
    (Kernel.measurable_coe η measurableSet_Iic) measurable_const)

lemma stronglyMeasurable_of_inner {U H : Type*} [MeasurableSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H] {f : U → H}
    (hf : ∀ h : H, StronglyMeasurable (fun u => inner ℂ h (f u))) :
    StronglyMeasurable f := by
  borelize H
  let e : H → ℕ → ℂ := fun h n => inner ℂ (TopologicalSpace.denseSeq H n) h
  have hec : Continuous e := by fun_prop
  have hei : Function.Injective e := by
    intro v w h
    have hh : (fun z : H => inner ℂ z v) = (fun z : H => inner ℂ z w) := by
      apply (TopologicalSpace.denseRange_denseSeq H).equalizer (by fun_prop) (by fun_prop)
      exact h
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_right, congrFun hh (v - w), sub_self]
  exact ((hec.measurableEmbedding hei).measurable_comp_iff.mp
    (Measurable.of_eval (fun n => (hf (TopologicalSpace.denseSeq H n)).measurable))).stronglyMeasurable

variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]
  (κ : Kernel U (X × Y)) [IsMarkovKernel κ] (ν : Measure X) (ρ : Measure Y)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

lemma family_good_measurable : MeasurableSet {u |
    MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ} := by
  have : IsMarkovKernel (κ.map Prod.fst) := Kernel.IsMarkovKernel.map κ measurable_fst
  have : IsMarkovKernel (κ.map Prod.snd) := Kernel.IsMarkovKernel.map κ measurable_snd
  convert (kernel_measurableSet_eq_const (κ.map Prod.fst) ν).inter
    (kernel_measurableSet_eq_const (κ.map Prod.snd) ρ) using 1
  ext u
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd]
  exact and_congr ⟨fun h => h.map_eq, fun h => ⟨measurable_fst, h⟩⟩
    ⟨fun h => h.map_eq, fun h => ⟨measurable_snd, h⟩⟩

lemma family_inner_stronglyMeasurable (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    StronglyMeasurable (fun u => inner ℂ g (family κ ν ρ u h)) := by
  classical
  have hf : StronglyMeasurable (fun p : X × Y => inner ℂ (g p.1) (h p.2)) :=
    (g.1.stronglyMeasurable.comp_measurable measurable_fst).inner
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)
  convert (hf.integral_kernel (κ := κ)).indicator (family_good_measurable κ ν ρ) using 1
  funext u
  unfold family
  split_ifs with hu
  · rw [Set.indicator_of_mem (show u ∈ {u | MeasurePreserving Prod.fst (κ u) ν ∧ MeasurePreserving Prod.snd (κ u) ρ} from hu)]
    exact inner_operator hu.1 hu.2 g h
  · simp [hu]

lemma family_stronglyMeasurable [SecondCountableTopology (Lp ℂ 2 ν)] (h : Lp ℂ 2 ρ) :
    StronglyMeasurable (fun u => family κ ν ρ u h) :=
  stronglyMeasurable_of_inner (fun g => family_inner_stronglyMeasurable κ ν ρ g h)


end JoiningOperator

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

def VectorMeasurable (F : X → E →L[ℂ] H) : Prop :=
  ∀ v : E, StronglyMeasurable (fun x => F x v)

lemma VectorMeasurable.adjoint [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) :
    VectorMeasurable (fun x => (F x).adjoint) := by
  intro w
  apply JoiningOperator.stronglyMeasurable_of_inner
  intro v
  simpa only [adjoint_inner_right] using (hF v).inner stronglyMeasurable_const

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.apply [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) {v : X → E}
    (hv : StronglyMeasurable v) : StronglyMeasurable (fun x => F x (v x)) := by
  borelize E
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun x => (F x).continuous) hF).comp_measurable (hv.measurable.prodMk measurable_id)

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace J] in
lemma VectorMeasurable.comp [SecondCountableTopology H]
    {F : X → H →L[ℂ] J} {G : X → E →L[ℂ] H}
    (hF : VectorMeasurable F) (hG : VectorMeasurable G) :
    VectorMeasurable (fun x => F x ∘L G x) := fun v => hF.apply (hG v)

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.comap {Y : Type*} [MeasurableSpace Y]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F) {f : Y → X}
    (hf : Measurable f) : VectorMeasurable (F ∘ f) :=
  fun v => (hF v).comp_measurable hf

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.measurableSet_eq [SecondCountableTopology E] [SecondCountableTopology H]
    {F G : X → E →L[ℂ] H} (hF : VectorMeasurable F) (hG : VectorMeasurable G) :
    MeasurableSet {x | F x = G x} := by
  borelize H
  have heq (x : X) : F x = G x ↔ ∀ n : ℕ,
      F x (TopologicalSpace.denseSeq E n) = G x (TopologicalSpace.denseSeq E n) := by
    constructor
    · intro h n; rw [h]
    · intro h
      apply DFunLike.ext'
      exact (TopologicalSpace.denseRange_denseSeq E).equalizer
        (F x).continuous (G x).continuous (funext h)
  simp_rw [heq, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_eq_fun
    (hF _).measurable (hG _).measurable)

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.measurableSet_range_le [SecondCountableTopology E]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F)
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    MeasurableSet {x | LinearMap.range (F x).toLinearMap ≤ V} := by
  borelize H
  have heq (x : X) : LinearMap.range (F x).toLinearMap ≤ V ↔
      ∀ n : ℕ, F x (TopologicalSpace.denseSeq E n) ∈ V := by
    constructor
    · intro h n; exact h ⟨_, rfl⟩
    · intro h
      have hall : ∀ v : E, F x v ∈ V := by
        intro v
        exact (TopologicalSpace.denseRange_denseSeq E).induction_on v
          (hV.preimage (F x).continuous) h
      rintro v ⟨w, rfl⟩
      exact hall w
  simp_rw [heq, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (hF _).measurable hV.measurableSet)
end

namespace ArrayObjects.Object.Rolled
open scoped ENNReal
open MeasureTheory ProbabilityTheory
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma cells_conditional (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (cells M A S n) (amap M.par (n+2)) (groupMarginal M A S n) (M.law (n+2)) := by
  exact (rows_conditional M hM A hA n).comp_left (measurable_rowRestrict M A S n)

lemma cells_fibre_marginal (hM : M.IsSaturated) (A S : Finset I)
    (hA : A ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      MeasurePreserving (cells M A S n) (M.ownKernel (n+2) e) (cellLaw M A S n e) :=
  ConditionalFibres.marginal (measurable_cells M A S n) (M.ownKernel_conditional (n+2))
    (cells_conditional M hM A S hA n)

omit [DecidableEq I] in
lemma rowPair_fixed_conditional (A R S D : Finset I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => (cells M A S n y,cells M A D n y)) (cells M A R n)
        ((rowPairKernel M A R S D n).sectR e) (M.ownKernel (n+2) e) := by
  apply ConditionalFibres.disintegrate (measurable_cells M A R n) (by fun_prop)
    (M.ownKernel_conditional (n+2))
  exact ⟨((measurable_amap M.measurable_par _).prodMk (measurable_cells M A R n)).prodMk
    ((measurable_cells M A S n).prodMk (measurable_cells M A D n)) |>.aemeasurable, (compProd_map_condDistrib (μ := M.law (n+2))
    ((measurable_amap M.measurable_par _).prodMk (measurable_cells M A R n)).aemeasurable
    ((measurable_cells M A S n).prodMk (measurable_cells M A D n)).aemeasurable).symm⟩

lemma columnPair_own_conditional (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (groupData M P S n)
      (columnPairKernel M P A B S n) (M.law (n+2)) := by
  have h := (columnPair_conditional M hM P A B ∅ S hP (Finset.disjoint_empty_left S)
    (by simpa using hS) n).comp_right
  exact h

lemma columnPair_fixed_conditional (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => (cells M A S n y,cells M B S n y)) (cells M P S n)
        ((columnPairKernel M P A B S n).sectR e) (M.ownKernel (n+2) e) :=
  ConditionalFibres.disintegrate (measurable_cells M P S n) (by fun_prop)
    (M.ownKernel_conditional (n+2)) (columnPair_own_conditional M hM P A B S hP hS n)

omit [DecidableEq I] in
lemma fibreRowEdge_eq (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreRowEdge M A R S D n e = JoiningOperator.family ((rowPairKernel M A R S D n).sectR e)
      (cellLaw M A S n e) (cellLaw M A D n e) := by
  ext x h
  rfl

omit [DecidableEq I] in
lemma fibreColumnEdge_eq (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    fibreColumnEdge M P A B S n e = JoiningOperator.family ((columnPairKernel M P A B S n).sectR e)
      (cellLaw M A S n e) (cellLaw M B S n e) := by
  ext x h
  rfl

omit [DecidableEq I] in
lemma fibreRowEdge_measurable (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    VectorMeasurable (fibreRowEdge M A R S D n e) := by
  rw [fibreRowEdge_eq]
  exact JoiningOperator.family_stronglyMeasurable _ _ _

omit [DecidableEq I] in
lemma fibreColumnEdge_measurable (P A B S : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    VectorMeasurable (fibreColumnEdge M P A B S n e) := by
  rw [fibreColumnEdge_eq]
  exact JoiningOperator.family_stronglyMeasurable _ _ _

lemma rowPair_fixed_marginals (hM : M.IsSaturated) (A R S D : Finset I)
    (hA : A ≠ Finset.univ) (hRS : Disjoint R S) (hRD : Disjoint R D)
    (hproperRS : R ∪ S ≠ Finset.univ) (hproperRD : R ∪ D ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ x ∂(M.ownKernel (n+2) e).map (cells M A R n),
        MeasurePreserving Prod.fst (rowPairKernel M A R S D n (e,x)) (cellLaw M A S n e) ∧
        MeasurePreserving Prod.snd (rowPairKernel M A R S D n (e,x)) (cellLaw M A D n e) := by
  filter_upwards [rowPair_fixed_conditional M A R S D n,
    cells_fibre_marginal M hM A S hA n, cells_fibre_marginal M hM A D hA n,
    cells_indep_columns_fibre M A A R S hRS hproperRS n,
    cells_indep_columns_fibre M A A R D hRD hproperRD n] with e hκ hs hd hrs hrd
  exact JoiningOperator.conditional_pair_marginals (measurable_cells M A R n) hs hd hκ hrs hrd

lemma columnPair_fixed_marginals (hM : M.IsSaturated) (P A B S : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hS : S ≠ Finset.univ)
    (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hPA : Disjoint P A) (hPB : Disjoint P B)
    (hproperPA : P ∪ A ≠ Finset.univ) (hproperPB : P ∪ B ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ c ∂(M.ownKernel (n+2) e).map (cells M P S n),
        MeasurePreserving Prod.fst (columnPairKernel M P A B S n (e,c)) (cellLaw M A S n e) ∧
        MeasurePreserving Prod.snd (columnPairKernel M P A B S n (e,c)) (cellLaw M B S n e) := by
  filter_upwards [columnPair_fixed_conditional M hM P A B S hP hS n,
    cells_fibre_marginal M hM A S hA n, cells_fibre_marginal M hM B S hB n,
    cells_indep_rows_fibre M hM P A S S hPA hproperPA n,
    cells_indep_rows_fibre M hM P B S S hPB hproperPB n] with e hκ hs hd hrs hrd
  exact JoiningOperator.conditional_pair_marginals (measurable_cells M P S n) hs hd hκ hrs hrd

end ArrayObjects.Object.Rolled

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
section Propagate
variable {Z X Y E H J K : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma essentialRange.ae_intertwining (μZ : Measure Z) (μX : Measure X) (μY : Measure Y)
    [SFinite μZ] [SFinite μX] [SFinite μY]
    (A : Z → E →L[ℂ] H) (F : X → J →L[ℂ] H) (G : Y → K →L[ℂ] E)
    (h1 : ∀ᵐ p ∂μZ.prod μY,
      LinearMap.range (A p.1 ∘L G p.2).toLinearMap ≤ essentialRange μX F)
    (h2 : ∀ᵐ p ∂μZ.prod μX,
      LinearMap.range ((A p.1).adjoint ∘L F p.2).toLinearMap ≤ essentialRange μY G) :
    ∀ᵐ z ∂μZ, (essentialRange μX F).starProjection ∘L A z =
      A z ∘L (essentialRange μY G).starProjection := by
  filter_upwards [Measure.ae_ae_of_ae_prod h1, Measure.ae_ae_of_ae_prod h2] with z hz1 hz2
  apply projection_intertwines
  · intro v hv
    exact essentialRange.le_comap_of_ae_comp μY G (A z) _ (essentialRange.isClosed μX F) hz1 hv
  · intro w hw
    exact essentialRange.le_comap_of_ae_comp μX F (A z).adjoint _ (essentialRange.isClosed μY G) hz2 hw

lemma essentialRange.projection_commutes [SecondCountableTopology H]
    (μ : Measure Z) (A : Z → E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : ∀ᵐ z ∂μ, W.starProjection ∘L A z = A z ∘L V.starProjection) :
    (essentialRange μ A).starProjection ∘L W.starProjection =
      W.starProjection ∘L (essentialRange μ A).starProjection := by
  apply projection_commutes_of_invariant
  have h := essentialRange.le_comap_of_ae_comp μ A W.starProjection (essentialRange μ A)
    (essentialRange.isClosed μ A) ?_
  · exact fun w hw => h hw
  · filter_upwards [hA, essentialRange.ae_range_le μ A] with z hz ha
    rw [hz]
    rintro w ⟨v, rfl⟩
    exact ha ⟨V.starProjection v, rfl⟩

lemma essentialRange.own_intertwines [SecondCountableTopology E] [SecondCountableTopology H]
    (μ : Measure Z) (F : Z → E →L[ℂ] H) :
    ∀ᵐ z ∂μ, (essentialRange μ F).starProjection ∘L F z =
      F z ∘L (essentialRange μ (fun z => (F z).adjoint)).starProjection := by
  filter_upwards [essentialRange.ae_range_le μ F,
    essentialRange.ae_range_le μ (fun z => (F z).adjoint)] with z hz hza
  apply projection_intertwines
  · intro v _; exact hz ⟨v, rfl⟩
  · intro w _; exact hza ⟨w, rfl⟩
end Propagate

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
lemma maps_of_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) : ∀ v ∈ V, A v ∈ W := by
  intro v hv
  apply W.starProjection_eq_self_iff.mp
  have h := congrArg (fun B : E →L[ℂ] H => B v) hA
  simpa only [comp_apply, V.starProjection_eq_self_iff.mpr hv] using h

lemma adjoint_intertwines (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) :
    V.starProjection ∘L A.adjoint = A.adjoint ∘L W.starProjection := by
  have h := congrArg adjoint hA
  simpa only [adjoint_comp, (isSelfAdjoint_starProjection V).adjoint_eq,
    (isSelfAdjoint_starProjection W).adjoint_eq] using h.symm

lemma inf_intertwines (A : E →L[ℂ] H)
    (V₁ V₂ : Submodule ℂ E) (W₁ W₂ : Submodule ℂ H)
    [V₁.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    [W₁.HasOrthogonalProjection] [W₂.HasOrthogonalProjection]
    [(V₁ ⊓ V₂).HasOrthogonalProjection] [(W₁ ⊓ W₂).HasOrthogonalProjection]
    (h1 : W₁.starProjection ∘L A = A ∘L V₁.starProjection)
    (h2 : W₂.starProjection ∘L A = A ∘L V₂.starProjection) :
    (W₁ ⊓ W₂).starProjection ∘L A = A ∘L (V₁ ⊓ V₂).starProjection := by
  apply projection_intertwines
  · intro v hv
    exact ⟨maps_of_intertwines A V₁ W₁ h1 v hv.1, maps_of_intertwines A V₂ W₂ h2 v hv.2⟩
  · intro w hw
    exact ⟨maps_of_intertwines A.adjoint W₁ V₁ (adjoint_intertwines A V₁ W₁ h1) w hw.1,
      maps_of_intertwines A.adjoint W₂ V₂ (adjoint_intertwines A V₂ W₂ h2) w hw.2⟩
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compress (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] : V →L[ℂ] W :=
  W.orthogonalProjectionOnto ∘L A ∘L V.subtypeL

lemma compress_adjoint (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [CompleteSpace V] [CompleteSpace W] :
    (compress A V W).adjoint = compress A.adjoint W V := by
  simp only [compress, adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, comp_assoc]

omit [CompleteSpace E] [CompleteSpace H] in
lemma compress_apply (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) (v : V) :
    (compress A V W v : H) = A v := by
  change W.starProjection (A v) = A v
  simpa only [comp_apply, V.starProjection_mem_subspace_eq_self] using
    congrArg (fun B : E →L[ℂ] H => B v) hA

omit [CompleteSpace E] [CompleteSpace H] in
lemma compress_onto (A : E →L[ℂ] H) (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : W.starProjection ∘L A = A ∘L V.starProjection) (v : E) :
    compress A V W (V.orthogonalProjectionOnto v) = W.orthogonalProjectionOnto (A v) := by
  change W.orthogonalProjectionOnto (A (V.starProjection v)) = _
  rw [← show W.starProjection (A v) = A (V.starProjection v) from
    congrArg (fun B : E →L[ℂ] H => B v) hA]
  exact Submodule.orthogonalProjectionOnto_starProjection_of_le le_rfl _

lemma compressed_total_range (μ : Measure X) (F : X → E →L[ℂ] H)
    (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hW : W ≤ essentialRange μ F)
    (hF : ∀ᵐ x ∂μ, W.starProjection ∘L F x = F x ∘L V.starProjection) :
    HasEssentialTotalRange μ (fun x => compress (F x) V W) := by
  intro C hC hCF
  have h : essentialRange μ F ≤ C.comap W.orthogonalProjectionOnto.toLinearMap := by
    apply essentialRange.le_of_ae_range μ F _ (hC.preimage W.orthogonalProjectionOnto.continuous)
    filter_upwards [hF, hCF] with x hx hcx
    rintro w ⟨v, rfl⟩
    change W.orthogonalProjectionOnto (F x v) ∈ C
    rw [← compress_onto (F x) V W hx v]
    exact hcx ⟨_, rfl⟩
  apply top_unique
  intro w _
  have hw := h (hW w.property)
  change W.orthogonalProjectionOnto (w : H) ∈ C at hw
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hw
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

omit [MeasurableSpace D] [SFinite μD] in
lemma rectangle_column_intertwines
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G) (hK : VectorMeasurable K)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    ∀ᵐ a ∂μC, (essentialRange μX F).starProjection ∘L K a =
      K a ∘L (essentialRange μY G).starProjection := by
  apply essentialRange.ae_intertwining μC μX μY K F G
  · have hp := ((hK.comap measurable_fst).comp (hG.comap measurable_snd)).measurableSet_range_le
      (essentialRange μX F) (essentialRange.isClosed μX F)
    rw [← hcy.map_eq]
    apply (ae_map_iff hcy.measurable.aemeasurable
      (show MeasurableSet {p : C × Y | LinearMap.range (K p.1 ∘L G p.2).toLinearMap ≤ essentialRange μX F} from hp)).mpr
    filter_upwards [h1, hx.quasiMeasurePreserving.ae (essentialRange.ae_range_le μX F)] with ω he hr
    rw [← he]
    rintro v ⟨w, rfl⟩
    exact hr ⟨N (d ω) w, rfl⟩
  · have hp := ((hK.adjoint.comap measurable_fst).comp (hF.comap measurable_snd)).measurableSet_range_le
      (essentialRange μY G) (essentialRange.isClosed μY G)
    rw [← hcx.map_eq]
    apply (ae_map_iff hcx.measurable.aemeasurable
      (show MeasurableSet {p : C × X | LinearMap.range ((K p.1).adjoint ∘L F p.2).toLinearMap ≤ essentialRange μY G} from hp)).mpr
    filter_upwards [h2, hy.quasiMeasurePreserving.ae (essentialRange.ae_range_le μY G)] with ω he hr
    have hea := congrArg adjoint he
    simp only [adjoint_comp, adjoint_adjoint] at hea
    rw [hea]
    rintro v ⟨w, rfl⟩
    exact hr ⟨(N (d ω)).adjoint w, rfl⟩

lemma rectangle_all_intertwines
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
    (∀ᵐ a ∂μC, (essentialRange μX F).starProjection ∘L K a =
      K a ∘L (essentialRange μY G).starProjection) ∧
    (∀ᵐ a ∂μD, (essentialRange μX (fun a => (F a).adjoint)).starProjection ∘L N a =
      N a ∘L (essentialRange μY (fun a => (G a).adjoint)).starProjection) ∧
    (∀ᵐ a ∂μX, (essentialRange μC K).starProjection ∘L F a =
      F a ∘L (essentialRange μD N).starProjection) ∧
    (∀ᵐ a ∂μY, (essentialRange μC (fun a => (K a).adjoint)).starProjection ∘L G a =
      G a ∘L (essentialRange μD (fun a => (N a).adjoint)).starProjection) := by
  have h2a : ∀ᵐ ω ∂μ, (K (c ω)).adjoint ∘L F (x ω) =
      G (y ω) ∘L (N (d ω)).adjoint := by
    filter_upwards [h2] with ω hω
    simpa only [adjoint_comp, adjoint_adjoint] using congrArg adjoint hω
  refine ⟨rectangle_column_intertwines hx hy hcy hcx hF hG hK h1 h2, ?_, ?_, ?_⟩
  · apply rectangle_column_intertwines (F := fun a => (F a).adjoint)
      (G := fun a => (G a).adjoint) (K := N) (N := K) hx hy hdy hdx hF.adjoint hG.adjoint hN h2
    simpa only [adjoint_adjoint] using h1
  · apply rectangle_column_intertwines (F := K) (G := N) (K := F) (N := G) hc hd
      ((Measure.measurePreserving_swap (μ := μD) (ν := μX)).comp hdx)
      ((Measure.measurePreserving_swap (μ := μC) (ν := μX)).comp hcx) hK hN hF
      (h1.mono fun _ h => h.symm) h2a
  · apply rectangle_column_intertwines (F := fun a => (K a).adjoint)
      (G := fun a => (N a).adjoint) (K := G) (N := F) hc hd
      ((Measure.measurePreserving_swap (μ := μD) (ν := μY)).comp hdy)
      ((Measure.measurePreserving_swap (μ := μC) (ν := μY)).comp hcy) hK.adjoint hN.adjoint hG
      h2a (by simpa only [adjoint_adjoint] using h1.mono fun _ h => h.symm)
end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace J] in
lemma compress_comp (A : H →L[ℂ] J) (B : E →L[ℂ] H)
    (U : Submodule ℂ E) (V : Submodule ℂ H) (W : Submodule ℂ J)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hB : V.starProjection ∘L B = B ∘L U.starProjection) :
    compress A V W ∘L compress B U V = compress (A ∘L B) U W := by
  apply ContinuousLinearMap.ext
  intro u
  change W.orthogonalProjectionOnto (A (compress B U V u)) = _
  rw [compress_apply B U V hB]
  rfl

omit [CompleteSpace E] [CompleteSpace H] in
lemma VectorMeasurable.compress {F : X → E →L[ℂ] H} (hF : VectorMeasurable F)
    (V : Submodule ℂ E) (W : Submodule ℂ H)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    VectorMeasurable (fun x => compress (F x) V W) := by
  intro v
  exact W.orthogonalProjectionOnto.continuous.comp_stronglyMeasurable (hF v)

instance submodule_completeSpace_inf (V W : Submodule ℂ H)
    [CompleteSpace V] [CompleteSpace W] : CompleteSpace (V ⊓ W : Submodule ℂ H) :=
by
  have hV : IsClosed (V : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  have hW : IsClosed (W : Set H) := (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  exact (hV.inter hW).completeSpace_coe

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

local notation "V₁" => essentialRange μX F
local notation "V₂" => essentialRange μX (fun a => adjoint (F a))
local notation "V₃" => essentialRange μY G
local notation "V₄" => essentialRange μY (fun a => adjoint (G a))
local notation "W₁" => essentialRange μC K
local notation "W₂" => essentialRange μD N
local notation "W₃" => essentialRange μC (fun a => adjoint (K a))
local notation "W₄" => essentialRange μD (fun a => adjoint (N a))
local notation "D₁" => (V₁ ⊓ W₁)
local notation "D₂" => (V₂ ⊓ W₂)
local notation "D₃" => (V₃ ⊓ W₃)
local notation "D₄" => (V₄ ⊓ W₄)
local notation "FR" => (fun a => compress (F a) D₂ D₁)
local notation "GR" => (fun a => compress (G a) D₄ D₃)
local notation "KR" => (fun a => compress (K a) D₃ D₁)
local notation "NR" => (fun a => compress (N a) D₄ D₂)

lemma rectangle_active_intersections
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
    (∀ᵐ a ∂μX, (D₁).starProjection ∘L F a = F a ∘L (D₂).starProjection) ∧
    (∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection) ∧
    (∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection) ∧
    (∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection) := by
  obtain ⟨hK', hN', hF', hG'⟩ := rectangle_all_intertwines hx hy hc hd hcy hcx hdy hdx
    hF hG hK hN h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hF', essentialRange.own_intertwines μX F] with a ha hb
    exact inf_intertwines (F a) V₂ W₂ V₁ W₁ hb ha
  · filter_upwards [hG', essentialRange.own_intertwines μY G] with a ha hb
    exact inf_intertwines (G a) V₄ W₄ V₃ W₃ hb ha
  · filter_upwards [hK', essentialRange.own_intertwines μC K] with a ha hb
    exact inf_intertwines (K a) V₃ W₃ V₁ W₁ ha hb
  · filter_upwards [hN', essentialRange.own_intertwines μD N] with a ha hb
    exact inf_intertwines (N a) V₄ W₄ V₂ W₂ ha hb

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_rectangle
    (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hiG : ∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection)
    (hiK : ∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection)
    (hiN : ∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    (∀ᵐ ω ∂μ, FR (x ω) ∘L NR (d ω) = KR (c ω) ∘L GR (y ω)) ∧
    (∀ᵐ ω ∂μ, (FR (x ω)).adjoint ∘L KR (c ω) = NR (d ω) ∘L (GR (y ω)).adjoint) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hy.quasiMeasurePreserving.ae hiG, hd.quasiMeasurePreserving.ae hiN, h1]
      with ω hg hn he
    rw [compress_comp _ _ _ _ _ hn, compress_comp _ _ _ _ _ hg, he]
  · filter_upwards [hc.quasiMeasurePreserving.ae hiK, hy.quasiMeasurePreserving.ae hiG, h2]
      with ω hk hg he
    rw [compress_adjoint, compress_adjoint, compress_comp _ _ _ _ _ hk,
      compress_comp _ _ _ _ _ (adjoint_intertwines _ _ _ hg), he]

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_F
    (hiF : ∀ᵐ a ∂μX, (D₁).starProjection ∘L F a = F a ∘L (D₂).starProjection) :
    HasEssentialTotalRange μX FR ∧ HasEssentialTotalRange μX (fun a => (FR a).adjoint) := by
  refine ⟨compressed_total_range μX F D₂ D₁ inf_le_left hiF, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μX (fun a => adjoint (F a)) D₁ D₂ inf_le_left
      (hiF.mono fun a h => adjoint_intertwines (F a) D₂ D₁ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_G
    (hi : ∀ᵐ a ∂μY, (D₃).starProjection ∘L G a = G a ∘L (D₄).starProjection) :
    HasEssentialTotalRange μY GR ∧ HasEssentialTotalRange μY (fun a => (GR a).adjoint) := by
  refine ⟨compressed_total_range μY G D₄ D₃ inf_le_left hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μY (fun a => (G a).adjoint) D₃ D₄ inf_le_left
      (hi.mono fun a h => adjoint_intertwines (G a) D₄ D₃ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_K
    (hi : ∀ᵐ a ∂μC, (D₁).starProjection ∘L K a = K a ∘L (D₃).starProjection) :
    HasEssentialTotalRange μC KR ∧ HasEssentialTotalRange μC (fun a => (KR a).adjoint) := by
  refine ⟨compressed_total_range μC K D₃ D₁ inf_le_right hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μC (fun a => (K a).adjoint) D₁ D₃ inf_le_right
      (hi.mono fun a h => adjoint_intertwines (K a) D₃ D₁ h))

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂]
  [SecondCountableTopology H₃] [SecondCountableTopology H₄]
  [SFinite μX] [SFinite μY] [SFinite μC] [SFinite μD] in
lemma restricted_total_N
    (hi : ∀ᵐ a ∂μD, (D₂).starProjection ∘L N a = N a ∘L (D₄).starProjection) :
    HasEssentialTotalRange μD NR ∧ HasEssentialTotalRange μD (fun a => (NR a).adjoint) := by
  refine ⟨compressed_total_range μD N D₄ D₂ inf_le_right hi, ?_⟩
  simpa only [compress_adjoint] using
    (compressed_total_range μD (fun a => (N a).adjoint) D₂ D₄ inf_le_right
      (hi.mono fun a h => adjoint_intertwines (N a) D₄ D₂ h))

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
section Descent
variable {Ω X E H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SecondCountableTopology H]
  {μ : Measure Ω} {ν : Measure X} {f : Ω → X} {A B : X → E →L[ℂ] H}
lemma VectorMeasurable.ae_eq_of_map (hf : MeasurePreserving f μ ν)
    (hA : VectorMeasurable A) (hB : VectorMeasurable B)
    (h : ∀ᵐ ω ∂μ, A (f ω) = B (f ω)) : A =ᵐ[ν] B := by
  rw [← hf.map_eq]
  exact (ae_map_iff hf.measurable.aemeasurable (hA.measurableSet_eq hB)).mpr h
end Descent

variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma fixed_squares_of_rectangle
    (hcxd : MeasurePreserving (fun ω => (c ω, x ω, d ω)) μ (μC.prod (μX.prod μD)))
    (hcyd : MeasurePreserving (fun ω => (c ω, y ω, d ω)) μ (μC.prod (μY.prod μD)))
    (hxdy : MeasurePreserving (fun ω => (x ω, d ω, y ω)) μ (μX.prod (μD.prod μY)))
    (hxcy : MeasurePreserving (fun ω => (x ω, c ω, y ω)) μ (μX.prod (μC.prod μY)))
    (hFm : VectorMeasurable F) (hGm : VectorMeasurable G)
    (hKm : VectorMeasurable K) (hNm : VectorMeasurable N)
    (hF : HasEssentialTotalRange μX F)
    (hFa : HasEssentialTotalRange μX fun a => (F a).adjoint)
    (hG : HasEssentialTotalRange μY G)
    (hGa : HasEssentialTotalRange μY fun a => (G a).adjoint)
    (hK : HasEssentialTotalRange μC K)
    (hKa : HasEssentialTotalRange μC fun a => (K a).adjoint)
    (hN : HasEssentialTotalRange μD N)
    (hNa : HasEssentialTotalRange μD fun a => (N a).adjoint)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    HasFixedInjectiveSquares μX F ∧ HasFixedInjectiveSquares μY G ∧
      HasFixedInjectiveSquares μC K ∧ HasFixedInjectiveSquares μD N := by
  have hs := (h1.and h2).mono (fun ω h => rectangle_square_identities
    (F (x ω)) (G (y ω)) (K (c ω)) (N (d ω)) h.1 h.2)
  apply fixed_squares_of_product_identities μX μY μC μD F G K N hF hFa hG hGa hK hKa hN hNa
  · apply VectorMeasurable.ae_eq_of_map hcxd
      (((hKm.comp hKm.adjoint).comap measurable_fst).comp
        (hFm.comap measurable_snd.fst))
      ((hFm.comap measurable_snd.fst).comp
        ((hNm.comp hNm.adjoint).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.1
  · apply VectorMeasurable.ae_eq_of_map hcyd
      (((hKm.adjoint.comp hKm).comap measurable_fst).comp
        (hGm.comap measurable_snd.fst))
      ((hGm.comap measurable_snd.fst).comp
        ((hNm.adjoint.comp hNm).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.1
  · apply VectorMeasurable.ae_eq_of_map hxdy
      (((hFm.adjoint.comp hFm).comap measurable_fst).comp
        (hNm.comap measurable_snd.fst))
      ((hNm.comap measurable_snd.fst).comp
        ((hGm.adjoint.comp hGm).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.2.1
  · apply VectorMeasurable.ae_eq_of_map hxcy
      (((hFm.comp hFm.adjoint).comap measurable_fst).comp
        (hKm.comap measurable_snd.fst))
      ((hKm.comap measurable_snd.fst).comp
        ((hGm.comp hGm.adjoint).comap measurable_snd.snd))
    exact hs.mono fun _ h => h.2.2.2
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
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

local notation "V₁" => essentialRange μX F
local notation "V₂" => essentialRange μX (fun a => adjoint (F a))
local notation "V₃" => essentialRange μY G
local notation "V₄" => essentialRange μY (fun a => adjoint (G a))
local notation "W₁" => essentialRange μC K
local notation "W₂" => essentialRange μD N
local notation "W₃" => essentialRange μC (fun a => adjoint (K a))
local notation "W₄" => essentialRange μD (fun a => adjoint (N a))
local notation "D₁" => (V₁ ⊓ W₁)
local notation "D₂" => (V₂ ⊓ W₂)
local notation "D₃" => (V₃ ⊓ W₃)
local notation "D₄" => (V₄ ⊓ W₄)
local notation "FR" => (fun a => compress (F a) D₂ D₁)
local notation "GR" => (fun a => compress (G a) D₄ D₃)
local notation "KR" => (fun a => compress (K a) D₃ D₁)
local notation "NR" => (fun a => compress (N a) D₄ D₂)

theorem restricted_fixed_squares
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω, y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω, x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω, y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω, x ω)) μ (μD.prod μX))
    (hcxd : MeasurePreserving (fun ω => (c ω, x ω, d ω)) μ (μC.prod (μX.prod μD)))
    (hcyd : MeasurePreserving (fun ω => (c ω, y ω, d ω)) μ (μC.prod (μY.prod μD)))
    (hxdy : MeasurePreserving (fun ω => (x ω, d ω, y ω)) μ (μX.prod (μD.prod μY)))
    (hxcy : MeasurePreserving (fun ω => (x ω, c ω, y ω)) μ (μX.prod (μC.prod μY)))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    HasFixedInjectiveSquares μX FR ∧ HasFixedInjectiveSquares μY GR ∧
      HasFixedInjectiveSquares μC KR ∧ HasFixedInjectiveSquares μD NR := by
  obtain ⟨hFi,hGi,hKi,hNi⟩ := rectangle_active_intersections hx hy hc hd hcy hcx hdy hdx
    hF hG hK hN h1 h2
  obtain ⟨hr1,hr2⟩ := restricted_rectangle hy hc hd hGi hKi hNi h1 h2
  obtain ⟨hFt,hFat⟩ := restricted_total_F hFi
  obtain ⟨hGt,hGat⟩ := restricted_total_G hGi
  obtain ⟨hKt,hKat⟩ := restricted_total_K hKi
  obtain ⟨hNt,hNat⟩ := restricted_total_N hNi
  exact fixed_squares_of_rectangle hcxd hcyd hxdy hxcy
    (hF.compress _ _) (hG.compress _ _) (hK.compress _ _) (hN.compress _ _)
    hFt hFat hGt hGat hKt hKat hNt hNat hr1 hr2
end

section
open MeasureTheory ContinuousLinearMap
variable {X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]
  (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
  (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
  (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)

def rectangleSpace₁ := essentialRange μX F ⊓ essentialRange μC K
def rectangleSpace₂ := essentialRange μX (fun x => (F x).adjoint) ⊓ essentialRange μD N
def rectangleSpace₃ := essentialRange μY G ⊓ essentialRange μC (fun c => (K c).adjoint)
def rectangleSpace₄ := essentialRange μY (fun y => (G y).adjoint) ⊓ essentialRange μD (fun d => (N d).adjoint)

instance : CompleteSpace (rectangleSpace₁ μX μC F K) := by unfold rectangleSpace₁; infer_instance
instance : CompleteSpace (rectangleSpace₂ μX μD F N) := by unfold rectangleSpace₂; infer_instance
instance : CompleteSpace (rectangleSpace₃ μY μC G K) := by unfold rectangleSpace₃; infer_instance
instance : CompleteSpace (rectangleSpace₄ μY μD G N) := by unfold rectangleSpace₄; infer_instance

def rectangleRestrictF (x : X) : rectangleSpace₂ μX μD F N →L[ℂ] rectangleSpace₁ μX μC F K :=
  compress (F x) _ _
def rectangleRestrictG (y : Y) : rectangleSpace₄ μY μD G N →L[ℂ] rectangleSpace₃ μY μC G K :=
  compress (G y) _ _
def rectangleRestrictK (c : C) : rectangleSpace₃ μY μC G K →L[ℂ] rectangleSpace₁ μX μC F K :=
  compress (K c) _ _
def rectangleRestrictN (d : D) : rectangleSpace₄ μY μD G N →L[ℂ] rectangleSpace₂ μX μD F N :=
  compress (N d) _ _
end

section

structure TriplePartition (I : Type*) [Fintype I] [DecidableEq I] where
  P : Finset I
  A : Finset I
  B : Finset I
  nonemptyP : P.Nonempty
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  disjointPA : Disjoint P A
  disjointPB : Disjoint P B
  disjointAB : Disjoint A B
  cover : P ∪ A ∪ B = Finset.univ
namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I] (s : TriplePartition I)
lemma properPA : s.P ∪ s.A ≠ Finset.univ := by
  intro h
  obtain ⟨b,hb⟩ := s.nonemptyB
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPB,s.disjointAB⟩)
    (h ▸ Finset.mem_univ b) hb
lemma properPB : s.P ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨a,ha⟩ := s.nonemptyA
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA,s.disjointAB.symm⟩)
    (h ▸ Finset.mem_univ a) ha
lemma properAB : s.A ∪ s.B ≠ Finset.univ := by
  intro h
  obtain ⟨p,hp⟩ := s.nonemptyP
  exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨s.disjointPA.symm,s.disjointPB.symm⟩)
    (h ▸ Finset.mem_univ p) hp
lemma properP : s.P ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properA : s.A ≠ Finset.univ := by
  intro h
  apply s.properPA
  simp [h]
lemma properB : s.B ≠ Finset.univ := by
  intro h
  apply s.properPB
  simp [h]
lemma card_eq : s.P.card + s.A.card + s.B.card = Fintype.card I := by
  rw [← Finset.card_union_of_disjoint s.disjointPA,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨s.disjointPB,s.disjointAB⟩),
    s.cover,Finset.card_univ]
lemma cardP : s.P.card + 2 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyA
  have := Finset.card_pos.mpr s.nonemptyB
  omega
lemma cardPA : s.P.card + s.A.card + 1 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyB
  omega
lemma cardPB : s.P.card + s.B.card + 1 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyA
  omega
end TriplePartition

open MeasureTheory
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  [SFinite ν] [SFinite ρ] [SFinite η]
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}
lemma MeasurePreserving.triple_swap_right
    (h : MeasurePreserving (fun ω => (x ω,y ω,z ω)) μ (ν.prod (ρ.prod η))) :
    MeasurePreserving (fun ω => (x ω,z ω,y ω)) μ (ν.prod (η.prod ρ)) := by
  exact ((MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ := ρ) (ν := η))).comp h
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_restricted_fixed_squares (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μX := cellLaw M rows.A cols.P n e
      let μY := cellLaw M rows.B cols.P n e
      let μC := cellLaw M rows.P cols.A n e
      let μD := cellLaw M rows.P cols.B n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      HasFixedInjectiveSquares μX (rectangleRestrictF μX μC μD F K N) ∧
      HasFixedInjectiveSquares μY (rectangleRestrictG μY μC μD G K N) ∧
      HasFixedInjectiveSquares μC (rectangleRestrictK μX μY μC F G K) ∧
      HasFixedInjectiveSquares μD (rectangleRestrictN μX μY μD F G N) := by
  filter_upwards [grouped_fibre_rectangle M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP rows.disjointPA rows.disjointPB rows.cardPA rows.cardPB rows.properPA rows.properPB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.cover cols.nonemptyA cols.nonemptyB n,
    grouped_product_triples M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.disjointPA rows.disjointPB rows.disjointAB rows.properPA rows.properPB rows.properAB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.properPA cols.properPB cols.properAB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.A cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.A cols.P rows.disjointPB rows.properPB n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.B cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.B cols.P rows.disjointPB rows.properPB n]
      with e hr ht hx hy hc hd hcx hcy hdx hdy
  dsimp only at *
  rcases ht with ⟨hcdx,hcdy,hxyc,hxyd⟩
  simp only [hx.map_eq,hy.map_eq,hc.map_eq,hd.map_eq] at hcdx hcdy hxyc hxyd
  exact restricted_fixed_squares hx hy hc hd
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
    (Rokhlin.MeasurePreserving.triple_swap_right hcdx)
    (Rokhlin.MeasurePreserving.triple_swap_right hcdy)
    (Rokhlin.MeasurePreserving.triple_swap_right hxyd)
    (Rokhlin.MeasurePreserving.triple_swap_right hxyc)
    (fibreRowEdge_measurable M _ _ _ _ _ _) (fibreRowEdge_measurable M _ _ _ _ _ _)
    (fibreColumnEdge_measurable M _ _ _ _ _ _) (fibreColumnEdge_measurable M _ _ _ _ _ _)
    (hr.mono fun _ h => h.1) (hr.mono fun _ h => h.2)
end ArrayObjects.Object.Rolled

section
open MeasureTheory ContinuousLinearMap
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}
omit [IsProbabilityMeasure μ] in
lemma rectangle_restricted_laws
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hcy : MeasurePreserving (fun ω => (c ω,y ω)) μ (μC.prod μY))
    (hcx : MeasurePreserving (fun ω => (c ω,x ω)) μ (μC.prod μX))
    (hdy : MeasurePreserving (fun ω => (d ω,y ω)) μ (μD.prod μY))
    (hdx : MeasurePreserving (fun ω => (d ω,x ω)) μ (μD.prod μX))
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    let FR := rectangleRestrictF μX μC μD F K N
    let GR := rectangleRestrictG μY μC μD G K N
    let KR := rectangleRestrictK μX μY μC F G K
    let NR := rectangleRestrictN μX μY μD F G N
    (∀ᵐ ω ∂μ, FR (x ω) ∘L NR (d ω) = KR (c ω) ∘L GR (y ω)) ∧
    (∀ᵐ ω ∂μ, (FR (x ω)).adjoint ∘L KR (c ω) = NR (d ω) ∘L (GR (y ω)).adjoint) := by
  obtain ⟨_,hGi,hKi,hNi⟩ := rectangle_active_intersections hx hy hc hd hcy hcx hdy hdx
    hF hG hK hN h1 h2
  exact restricted_rectangle hy hc hd hGi hKi hNi h1 h2
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_restricted_rectangle (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μX := cellLaw M rows.A cols.P n e
      let μY := cellLaw M rows.B cols.P n e
      let μC := cellLaw M rows.P cols.A n e
      let μD := cellLaw M rows.P cols.B n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      let FR := rectangleRestrictF μX μC μD F K N
      let GR := rectangleRestrictG μY μC μD G K N
      let KR := rectangleRestrictK μX μY μC F G K
      let NR := rectangleRestrictN μX μY μD F G N
      (∀ᵐ ω ∂M.ownKernel (n+2) e,
        FR (cells M rows.A cols.P n ω) ∘L NR (cells M rows.P cols.B n ω) =
        KR (cells M rows.P cols.A n ω) ∘L GR (cells M rows.B cols.P n ω)) ∧
      (∀ᵐ ω ∂M.ownKernel (n+2) e,
        (FR (cells M rows.A cols.P n ω)).adjoint ∘L KR (cells M rows.P cols.A n ω) =
        NR (cells M rows.P cols.B n ω) ∘L (GR (cells M rows.B cols.P n ω)).adjoint) := by
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
  dsimp only at *
  exact rectangle_restricted_laws hx hy hc hd
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
    (fibreRowEdge_measurable M _ _ _ _ _ _) (fibreRowEdge_measurable M _ _ _ _ _ _)
    (fibreColumnEdge_measurable M _ _ _ _ _ _) (fibreColumnEdge_measurable M _ _ _ _ _ _)
    (hr.mono fun _ h => h.1) (hr.mono fun _ h => h.2)
end ArrayObjects.Object.Rolled

namespace StrongUnitary
open MeasureTheory Filter Topology
open scoped Topology
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

def code (U : E ≃ₗᵢ[ℂ] H) : ℕ → H := fun n => U (TopologicalSpace.denseSeq E n)

instance topology : TopologicalSpace (E ≃ₗᵢ[ℂ] H) :=
  .induced code inferInstance

lemma code_injective : Function.Injective (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) := by
  intro U V h
  apply DFunLike.ext'
  exact (TopologicalSpace.denseRange_denseSeq E).equalizer U.continuous V.continuous h

lemma code_embedding : IsEmbedding (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) :=
  ⟨⟨rfl⟩, code_injective⟩

instance t2 : T2Space (E ≃ₗᵢ[ℂ] H) := code_embedding.t2Space
instance metrizable : TopologicalSpace.MetrizableSpace (E ≃ₗᵢ[ℂ] H) := code_embedding.metrizableSpace
instance secondCountable [SecondCountableTopology H] : SecondCountableTopology (E ≃ₗᵢ[ℂ] H) :=
  code_embedding.secondCountableTopology
instance measurableSpace : MeasurableSpace (E ≃ₗᵢ[ℂ] H) := borel _
instance borelSpace : BorelSpace (E ≃ₗᵢ[ℂ] H) := ⟨rfl⟩

lemma continuous_eval : Continuous (fun p : (E ≃ₗᵢ[ℂ] H) × E => p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    (TopologicalSpace.denseRange_denseSeq E)
  · intro U; exact U.isometry.lipschitzWith
  · rintro _ ⟨n, rfl⟩
    exact (continuous_apply n).comp code_embedding.continuous

lemma continuous_apply (v : E) : Continuous (fun U : E ≃ₗᵢ[ℂ] H => U v) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)

lemma continuous_iff {X : Type*} [TopologicalSpace X] {f : X → E ≃ₗᵢ[ℂ] H} :
    Continuous f ↔ ∀ v, Continuous (fun x => f x v) := by
  constructor
  · intro h v; exact (continuous_apply v).comp h
  · intro h
    exact code_embedding.isInducing.continuous_iff.mpr (continuous_pi (fun n => h _))

lemma tendsto_iff {X : Type*} {l : Filter X} {f : X → E ≃ₗᵢ[ℂ] H} {U : E ≃ₗᵢ[ℂ] H} :
    Tendsto f l (𝓝 U) ↔ ∀ v, Tendsto (fun x => f x v) l (𝓝 (U v)) := by
  constructor
  · intro h v; exact ((continuous_apply v).tendsto U).comp h
  · intro h
    exact code_embedding.isInducing.tendsto_nhds_iff.mpr (tendsto_pi_nhds.mpr (fun n => h _))

lemma measurable_iff [SecondCountableTopology H] {X : Type*} [MeasurableSpace X]
    {f : X → E ≃ₗᵢ[ℂ] H} :
    Measurable f ↔ ∀ v, StronglyMeasurable (fun x => f x v) := by
  borelize H
  constructor
  · intro hf v
    exact ((continuous_apply v).measurable.comp hf).stronglyMeasurable
  · intro hf
    have hc : Measurable (code ∘ f) := Measurable.of_eval (fun n => (hf _).measurable)
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap f (borel _) ≤ _
    rw [show borel (E ≃ₗᵢ[ℂ] H) = MeasurableSpace.comap code (borel (ℕ → H)) from
      borel_comap]
    rw [MeasurableSpace.comap_comp]
    simpa only [← BorelSpace.measurable_eq (α := ℕ → H)] using hc.comap_le

lemma continuous_symm [SecondCountableTopology H] :
    Continuous (fun U : E ≃ₗᵢ[ℂ] H => U.symm) := by
  rw [_root_.continuous_iff_continuousAt]
  intro U
  apply tendsto_iff.mpr
  intro v
  rw [tendsto_iff_dist_tendsto_zero]
  have hh := ((continuous_apply (U.symm v)).tendsto U).dist (tendsto_const_nhds (x := v))
  have he (V : E ≃ₗᵢ[ℂ] H) : dist (V.symm v) (U.symm v) = dist (V (U.symm v)) v := by
    rw [← V.dist_map, V.apply_symm_apply, dist_comm]
  simp only [he, U.apply_symm_apply, dist_self] at hh ⊢
  exact hh

instance topologicalGroup : IsTopologicalGroup (E ≃ₗᵢ[ℂ] E) where
  continuous_mul := continuous_iff.mpr (fun v =>
    continuous_eval.comp (continuous_fst.prodMk ((continuous_apply v).comp continuous_snd)))
  continuous_inv := continuous_symm
end StrongUnitary

section
open MeasureTheory ContinuousLinearMap Filter Topology
open scoped InnerProductSpace Topology
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]

omit [CompleteSpace E] [CompleteSpace H] in
lemma unitary_measurable_of_dense (U : X → E ≃ₗᵢ[ℂ] H) (B : E →L[ℂ] E)
    (hB : DenseRange B) (hm : ∀ v, StronglyMeasurable (fun x => U x (B v))) :
    Measurable U := by
  apply StrongUnitary.measurable_iff.mpr
  intro v
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp (hB v)
  choose t hts using hs
  apply stronglyMeasurable_of_tendsto (f := fun n x => U x (B (t n))) atTop (fun n => hm _)
  apply tendsto_pi_nhds.mpr
  intro x
  simp_rw [hts]
  exact (U x).continuous.continuousAt.tendsto.comp ht

lemma HasFixedInjectiveSquares.exists_measurable_polar {μ : Measure X} [IsProbabilityMeasure μ]
    {F : X → E →L[ℂ] H} (hF : VectorMeasurable F)
    (hs : HasFixedInjectiveSquares μ F) :
    ∃ U : X → E ≃ₗᵢ[ℂ] H, Measurable U ∧
      ∀ᵐ x ∂μ, Function.Injective (F x) ∧ DenseRange (F x) ∧
        (U x : E →L[ℂ] H) ∘L operatorAbs (F x) = F x := by
  classical
  obtain ⟨P, Q, hPi, hQi, hP, hQ⟩ := hs
  obtain ⟨x₀, hx₀⟩ := (hP.and hQ).exists
  have hinj {x} (hx : (F x).adjoint ∘L F x = P) : Function.Injective (F x) := by
    apply (F x).adjoint_comp_self_injective_iff.mp
    change Function.Injective ((F x).adjoint ∘L F x)
    rwa [hx]
  have hden {x} (hx : F x ∘L (F x).adjoint = Q) : DenseRange (F x) := by
    apply (denseRange_iff_adjoint_injective _).mpr
    apply (F x).adjoint.adjoint_comp_self_injective_iff.mp
    change Function.Injective ((F x).adjoint.adjoint ∘L (F x).adjoint)
    simpa only [adjoint_adjoint, hx] using hQi
  let B := operatorAbs (F x₀)
  have hB : Function.Injective B := operatorAbs_injective _ (hinj hx₀.1)
  have hBd : DenseRange B := operatorAbs_denseRange _ (hinj hx₀.1)
  have hBa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg (operatorAbs_nonneg _)
  let s : Set X := {x | (F x).adjoint ∘L F x = P ∧ F x ∘L (F x).adjoint = Q}
  have hsmeas : MeasurableSet s :=
    (hF.adjoint.comp hF).measurableSet_eq (fun _ => stronglyMeasurable_const) |>.inter
      ((hF.comp hF.adjoint).measurableSet_eq (fun _ => stronglyMeasurable_const))
  obtain ⟨U₀, hU₀⟩ := exists_unitary_of_selfAdjoint_square (F x₀) B hBa hB
    (hden hx₀.2) (operatorAbs_sq _)
  have hex (x : s) : ∃ U : E ≃ₗᵢ[ℂ] H, ∀ v, U (B v) = F x v := by
    apply exists_unitary_of_selfAdjoint_square (F x) B hBa hB (hden x.property.2)
    rw [show B ∘L B = (F x₀).adjoint ∘L F x₀ from operatorAbs_sq _, hx₀.1, x.property.1]
  choose V hV using hex
  let U : X → E ≃ₗᵢ[ℂ] H := fun x => if hx : x ∈ s then V ⟨x, hx⟩ else U₀
  refine ⟨U, unitary_measurable_of_dense U B hBd (fun v => ?_), ?_⟩
  · have he : (fun x => U x (B v)) = s.piecewise (fun x => F x v) (fun _ => F x₀ v) := by
      funext x
      by_cases hx : x ∈ s
      · simp only [U, dite_eq_left hx, Set.piecewise_eq_of_mem s _ _ hx, hV]
      · simp only [U, dite_eq_right hx, Set.piecewise_eq_of_notMem s _ _ hx, hU₀]
    rw [he]
    exact (hF v).piecewise hsmeas stronglyMeasurable_const
  · filter_upwards [hP, hQ] with x hp hq
    refine ⟨hinj hp, hden hq, ?_⟩
    have hx : x ∈ s := ⟨hp, hq⟩
    have he : operatorAbs (F x) = B := by
      change operatorAbs (F x) = operatorAbs (F x₀)
      unfold operatorAbs
      rw [hp, hx₀.1]
    apply ContinuousLinearMap.ext
    intro v
    change U x (operatorAbs (F x) v) = F x v
    rw [he]
    simp only [U, dite_eq_left hx, hV]
end

section
open MeasureTheory ContinuousLinearMap
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]

structure MeasurablePolar (μ : Measure X) (F : X → E →L[ℂ] H) where
  unitary : X → E ≃ₗᵢ[ℂ] H
  measurable : Measurable unitary
  formula : ∀ᵐ x ∂μ, Function.Injective (F x) ∧ DenseRange (F x) ∧
    (unitary x : E →L[ℂ] H) ∘L operatorAbs (F x) = F x

lemma HasFixedInjectiveSquares.nonempty_polar {μ : Measure X} [IsProbabilityMeasure μ]
    {F : X → E →L[ℂ] H} (hs : HasFixedInjectiveSquares μ F) (hF : VectorMeasurable F) :
    Nonempty (MeasurablePolar μ F) := by
  obtain ⟨U,hU,h⟩ := hs.exists_measurable_polar hF
  exact ⟨⟨U,hU,h⟩⟩

variable {Ω Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

omit [SecondCountableTopology H₁] in

lemma MeasurablePolar.rectangle
    (a : MeasurablePolar μX F) (b : MeasurablePolar μY G)
    (p : MeasurablePolar μC K) (q : MeasurablePolar μD N)
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    ∀ᵐ ω ∂μ, (q.unitary (d ω)).trans (a.unitary (x ω)) =
      (b.unitary (y ω)).trans (p.unitary (c ω)) := by
  filter_upwards [hx.quasiMeasurePreserving.ae a.formula,hy.quasiMeasurePreserving.ae b.formula,
    hc.quasiMeasurePreserving.ae p.formula,hd.quasiMeasurePreserving.ae q.formula,h1,h2]
    with ω ha hb hp hq h1 h2
  have he := polar_rectangle (F (x ω)) (G (y ω)) (K (c ω)) (N (d ω)) h1 h2 hb.1 hq.1
    (a.unitary (x ω)) (b.unitary (y ω)) (p.unitary (c ω)) (q.unitary (d ω))
    ha.2.2 hb.2.2 hp.2.2 hq.2.2
  ext v
  exact congrArg (fun W : H₄ →L[ℂ] H₁ => W v) he
end

section
open MeasureTheory ContinuousLinearMap
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]

structure MeasurablePolarRectangle
    (μ : Measure Ω) (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
    (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
    (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)
    (x : Ω → X) (y : Ω → Y) (c : Ω → C) (d : Ω → D) where
  a : MeasurablePolar μX F
  b : MeasurablePolar μY G
  p : MeasurablePolar μC K
  q : MeasurablePolar μD N
  rectangle : ∀ᵐ ω ∂μ, (q.unitary (d ω)).trans (a.unitary (x ω)) =
    (b.unitary (y ω)).trans (p.unitary (c ω))

variable {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma exists_measurablePolarRectangle
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (sF : HasFixedInjectiveSquares μX F) (sG : HasFixedInjectiveSquares μY G)
    (sK : HasFixedInjectiveSquares μC K) (sN : HasFixedInjectiveSquares μD N)
    (h1 : ∀ᵐ ω ∂μ, F (x ω) ∘L N (d ω) = K (c ω) ∘L G (y ω))
    (h2 : ∀ᵐ ω ∂μ, (F (x ω)).adjoint ∘L K (c ω) = N (d ω) ∘L (G (y ω)).adjoint) :
    Nonempty (MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d) := by
  obtain ⟨a⟩ := sF.nonempty_polar hF
  obtain ⟨b⟩ := sG.nonempty_polar hG
  obtain ⟨p⟩ := sK.nonempty_polar hK
  obtain ⟨q⟩ := sN.nonempty_polar hN
  exact ⟨⟨a,b,p,q,a.rectangle b p q hx hy hc hd h1 h2⟩⟩
end

section
open MeasureTheory ContinuousLinearMap
variable {Ω X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]

variable {μ : Measure Ω} {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

lemma exists_restrictedPolarRectangle
    (hx : MeasurePreserving x μ μX) (hy : MeasurePreserving y μ μY)
    (hc : MeasurePreserving c μ μC) (hd : MeasurePreserving d μ μD)
    (hF : VectorMeasurable F) (hG : VectorMeasurable G)
    (hK : VectorMeasurable K) (hN : VectorMeasurable N)
    (hs : HasFixedInjectiveSquares μX (rectangleRestrictF μX μC μD F K N) ∧
      HasFixedInjectiveSquares μY (rectangleRestrictG μY μC μD G K N) ∧
      HasFixedInjectiveSquares μC (rectangleRestrictK μX μY μC F G K) ∧
      HasFixedInjectiveSquares μD (rectangleRestrictN μX μY μD F G N))
    (hr : (∀ᵐ ω ∂μ, (rectangleRestrictF μX μC μD F K N) (x ω) ∘L
        (rectangleRestrictN μX μY μD F G N) (d ω) =
        (rectangleRestrictK μX μY μC F G K) (c ω) ∘L (rectangleRestrictG μY μC μD G K N) (y ω)) ∧
      (∀ᵐ ω ∂μ, ((rectangleRestrictF μX μC μD F K N) (x ω)).adjoint ∘L
        (rectangleRestrictK μX μY μC F G K) (c ω) =
        (rectangleRestrictN μX μY μD F G N) (d ω) ∘L ((rectangleRestrictG μY μC μD G K N) (y ω)).adjoint)) :
    Nonempty (MeasurablePolarRectangle μ μX μY μC μD
      (rectangleRestrictF μX μC μD F K N) (rectangleRestrictG μY μC μD G K N)
      (rectangleRestrictK μX μY μC F G K) (rectangleRestrictN μX μY μD F G N) x y c d) := by
  exact exists_measurablePolarRectangle hx hy hc hd
    (hF.compress _ _) (hG.compress _ _) (hK.compress _ _) (hN.compress _ _)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hr.1 hr.2
end

namespace ArrayObjects.Object.Rolled

open ContinuousLinearMap MeasureTheory ProbabilityTheory
open scoped ENNReal

section GroupedPolarData
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def GroupedPolarData (rows cols : TriplePartition I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  let μX := cellLaw M rows.A cols.P n e
  let μY := cellLaw M rows.B cols.P n e
  let μC := cellLaw M rows.P cols.A n e
  let μD := cellLaw M rows.P cols.B n e
  let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
  let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
  let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
  let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
  MeasurablePolarRectangle (M.ownKernel (n+2) e) μX μY μC μD
    (rectangleRestrictF μX μC μD F K N) (rectangleRestrictG μY μC μD G K N)
    (rectangleRestrictK μX μY μC F G K) (rectangleRestrictN μX μY μD F G N)
    (cells M rows.A cols.P n) (cells M rows.B cols.P n)
    (cells M rows.P cols.A n) (cells M rows.P cols.B n)

theorem grouped_polar_data (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)), Nonempty (GroupedPolarData M rows cols n e) := by
  filter_upwards [grouped_restricted_fixed_squares M hM rows cols n,
    grouped_restricted_rectangle M hM rows cols n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n] with e hs hr hx hy hc hd
  have h := exists_restrictedPolarRectangle
    (F := fibreRowEdge M rows.A cols.P cols.A cols.B n e)
    (G := fibreRowEdge M rows.B cols.P cols.A cols.B n e)
    (K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e)
    (N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e) hx hy hc hd
    (fibreRowEdge_measurable M rows.A cols.P cols.A cols.B n e)
    (fibreRowEdge_measurable M rows.B cols.P cols.A cols.B n e)
    (fibreColumnEdge_measurable M rows.P rows.A rows.B cols.A n e)
    (fibreColumnEdge_measurable M rows.P rows.A rows.B cols.B n e) hs hr
  exact h
end GroupedPolarData


universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma pairPair_conditional (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hR : R ≠ Finset.univ) (n : ℕ) :
    HasCondDistrib (fun y => ((cells M A R n y,cells M B R n y),
      (cells M P S n y,cells M P D n y))) (groupData M P R n)
      ((columnPairKernel M P A B R n) ×ₖ (rowPairKernel M P R S D n)) (M.law (n+2)) := by
  let H : WholeGroupData M P ∅ n → GroupData M P R n ×
      ((S → P → Arr I M.Y n) × (D → P → Arr I M.Y n)) := fun q =>
    ((q.1.1,rowRestrict M P R n q.1.2),
      (rowRestrict M P S n q.1.2,rowRestrict M P D n q.1.2))
  have hH : Measurable H := by
    exact ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_rowRestrict M P R n).comp (measurable_snd.comp measurable_fst))).prodMk
        (((measurable_rowRestrict M P S n).comp (measurable_snd.comp measurable_fst)).prodMk
          ((measurable_rowRestrict M P D n).comp (measurable_snd.comp measurable_fst)))
  have hh := columnPair_conditional M hM P A B ∅ R hP (Finset.disjoint_empty_left R)
    (by simpa using hR) n
  have he : (columnPairKernel M P A B R n).comap (columnOwnData M P ∅ R n)
      (measurable_columnOwnData M P ∅ R n) =
      ((columnPairKernel M P A B R n).prodMkRight
        ((S → P → Arr I M.Y n) × (D → P → Arr I M.Y n))).comap H hH := by
    ext q : 1
    rfl
  rw [he] at hh
  have hx := hh.comp_right
  have hc : HasCondDistrib (fun y => (cells M P S n y,cells M P D n y))
      (groupData M P R n) (rowPairKernel M P R S D n) (M.law (n+2)) := by
    exact ⟨((measurable_groupData M P R n).prodMk
      ((measurable_cells M P S n).prodMk (measurable_cells M P D n))).aemeasurable,
      (compProd_map_condDistrib (μ := M.law (n+2)) (by fun_prop)
        ((measurable_cells M P S n).prodMk (measurable_cells M P D n)).aemeasurable).symm⟩
  have h := ConditionalFibres.chain hc hx
  rw [ConditionalScreens.compProd_prodMkRight] at h
  have h' := h.comp_left measurable_swap
  simpa only [Function.comp_def,Prod.swap_prod_mk,Kernel.map_prod_swap] using h'

lemma pairPair_fixed_conditional (hM : M.IsSaturated) (P A B R S D : Finset I)
    (hP : P.card + 2 ≤ Fintype.card I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      HasCondDistrib (fun y => ((cells M A R n y,cells M B R n y),
        (cells M P S n y,cells M P D n y))) (cells M P R n)
        (((columnPairKernel M P A B R n).sectR e) ×ₖ ((rowPairKernel M P R S D n).sectR e))
        (M.ownKernel (n+2) e) := by
  let : StandardBorelSpace (R → A → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (R → B → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (S → P → Arr I M.Y n) := inferInstance
  let : StandardBorelSpace (D → P → Arr I M.Y n) := inferInstance
  have h := ConditionalFibres.disintegrate (measurable_cells M P R n) (by fun_prop)
    (M.ownKernel_conditional (n+2)) (pairPair_conditional M hM P A B R S D hP hR n)
  filter_upwards [h] with e he
  have hk : ((columnPairKernel M P A B R n) ×ₖ (rowPairKernel M P R S D n)).sectR e =
      ((columnPairKernel M P A B R n).sectR e) ×ₖ ((rowPairKernel M P R S D n).sectR e) := by
    ext z : 1
    simp only [Kernel.sectR_apply, Kernel.prod_apply]
  rwa [hk] at he
end ArrayObjects.Object.Rolled

section

open MeasureTheory Filter
open scoped Topology ProbabilityTheory


section MeasureSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Y] [T2Space Z]

theorem mem_support_map_of_continuous {μ : Measure X} {f : X → Y}
    (hf : Continuous f) {x : X} (hx : x ∈ μ.support) :
    f x ∈ (μ.map f).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  rw [Measure.map_apply hf.measurable hU.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx (f ⁻¹' U)
    (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU))

omit [BorelSpace X] in

theorem eqOn_support_of_ae_eq {μ : Measure X} {f g : X → Z}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) :
    Set.EqOn f g μ.support :=
  Measure.support_subset_of_isClosed (isClosed_eq hf hg) h

omit [BorelSpace X] [BorelSpace Y] in

theorem eqOn_support_prod_of_ae_eq {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f g : X × Y → Z}
    (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ.prod ν] g) :
    ∀ x ∈ μ.support, ∀ y ∈ ν.support, f (x, y) = g (x, y) := by
  have h' : ∀ᵐ x ∂μ, ∀ y ∈ ν.support, f (x, y) = g (x, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
    exact eqOn_support_of_ae_eq (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id)) hx
  intro x hx y hy
  exact eqOn_support_of_ae_eq (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (h'.mono fun _ ht => ht y hy) hx

end MeasureSupport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

noncomputable def translateProbability (ρ : ProbabilityMeasure G) (u v : G) :
    ProbabilityMeasure G :=
  let _ : AEMeasurable (fun a => u * a * v⁻¹) (ρ : Measure G) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable.aemeasurable
  ρ.map (fun a => u * a * v⁻¹)

@[simp] theorem translateProbability_toMeasure (ρ : ProbabilityMeasure G) (u v : G) :
    (translateProbability ρ u v : Measure G) =
      (ρ : Measure G).map (fun a => u * a * v⁻¹) := rfl

theorem continuous_translateProbability [FirstCountableTopology G] (ρ : ProbabilityMeasure G) :
    Continuous (fun p : G × G => translateProbability ρ p.1 p.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hrepr : (fun p : G × G => ∫ a, f a ∂(translateProbability ρ p.1 p.2 : Measure G)) =
      (fun p : G × G => ∫ a, f (p.1 * a * p.2⁻¹) ∂(ρ : Measure G)) := by
    funext p
    rw [translateProbability_toMeasure]
    exact integral_map ((continuous_const.mul continuous_id).mul
      continuous_const).measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable
  rw [hrepr]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro p
    exact (f.continuous.comp ((continuous_const.mul continuous_id).mul
      continuous_const)).measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun a => f.norm_coe_le_norm _
  · exact integrable_const _
  · exact Eventually.of_forall fun a =>
      f.continuous.comp ((continuous_fst.mul continuous_const).mul continuous_snd.inv)

@[simp] theorem translateProbability_one_right_toMeasure
    (ρ : ProbabilityMeasure G) (u : G) :
    (translateProbability ρ u 1 : Measure G) = (ρ : Measure G).map (u * ·) := by
  simp [translateProbability_toMeasure]

theorem translateProbability_eq_on_support
    [FirstCountableTopology G] [HasOuterApproxClosed G]
    (ρ τ : ProbabilityMeasure G)
    (h : ∀ᵐ p ∂(τ : Measure G).prod τ,
      translateProbability ρ p.1 p.2 = ρ) :
    ∀ u ∈ (τ : Measure G).support, ∀ v ∈ (τ : Measure G).support,
      translateProbability ρ u v = ρ := by
  exact eqOn_support_prod_of_ae_eq (continuous_translateProbability ρ) continuous_const h

theorem map_mulLeft_inv_eq_of_eq (μ : Measure G) (u : G)
    (h : μ.map (u * ·) = μ) : μ.map (u⁻¹ * ·) = μ := by
  calc
    μ.map (u⁻¹ * ·) = (μ.map (u * ·)).map (u⁻¹ * ·) := by rw [h]
    _ = μ.map id := by
      rw [Measure.map_map (g := fun x => u⁻¹ * x) (f := fun x => u * x)
        (continuous_const.mul continuous_id).measurable
        (continuous_const.mul continuous_id).measurable]
      congr 1
      funext a
      simp
    _ = μ := Measure.map_id

theorem common_abelian_support_of_translated_laws
    [FirstCountableTopology G] [HasOuterApproxClosed G]
    (ρ τ : ProbabilityMeasure G)
    (hρ1 : (1 : G) ∈ (ρ : Measure G).support)
    (hτ1 : (1 : G) ∈ (τ : Measure G).support)
    (hρ : ∀ᵐ p ∂(τ : Measure G).prod τ,
      translateProbability ρ p.1 p.2 = ρ)
    (hτ : ∀ᵐ p ∂(ρ : Measure G).prod ρ,
      translateProbability τ p.1 p.2 = τ)
    (hcomm : ∀ u ∈ (ρ : Measure G).support,
      ∀ v ∈ (τ : Measure G).support, u * v = v * u) :
    ∃ H : Subgroup G, IsClosed (H : Set G) ∧
      (ρ : Measure G).support = H ∧ (τ : Measure G).support = H ∧
      (∀ u ∈ H, ∀ v ∈ H, u * v = v * u) ∧
      (∀ u ∈ H, (ρ : Measure G).map (u * ·) = ρ) := by
  have hρ' := translateProbability_eq_on_support ρ τ hρ
  have hτ' := translateProbability_eq_on_support τ ρ hτ
  have hleftρ : ∀ u ∈ (τ : Measure G).support,
      (ρ : Measure G).map (u * ·) = ρ := by
    intro u hu
    simpa using congrArg ProbabilityMeasure.toMeasure (hρ' u hu 1 hτ1)
  have hleftτ : ∀ u ∈ (ρ : Measure G).support,
      (τ : Measure G).map (u * ·) = τ := by
    intro u hu
    simpa using congrArg ProbabilityMeasure.toMeasure (hτ' u hu 1 hρ1)
  have hsub₁ : (τ : Measure G).support ⊆ (ρ : Measure G).support := by
    intro u hu
    have hm := mem_support_map_of_continuous (f := fun x => u * x)
      (continuous_const.mul continuous_id : Continuous (u * ·)) hρ1
    simpa [hleftρ u hu] using hm
  have hsub₂ : (ρ : Measure G).support ⊆ (τ : Measure G).support := by
    intro u hu
    have hm := mem_support_map_of_continuous (f := fun x => u * x)
      (continuous_const.mul continuous_id : Continuous (u * ·)) hτ1
    simpa [hleftτ u hu] using hm
  have heq : (τ : Measure G).support = (ρ : Measure G).support :=
    Set.Subset.antisymm hsub₁ hsub₂
  have hinv : ∀ u ∈ (ρ : Measure G).support,
      (ρ : Measure G).map (u * ·) = ρ := fun u hu => hleftρ u (hsub₂ hu)
  let H : Subgroup G :=
    { carrier := (ρ : Measure G).support
      one_mem' := hρ1
      mul_mem' := by
        intro u v hu hv
        have hm := mem_support_map_of_continuous (f := fun x => u * x)
          (continuous_const.mul continuous_id : Continuous (u * ·)) hv
        simpa [hinv u hu] using hm
      inv_mem' := by
        intro u hu
        have hm := mem_support_map_of_continuous (f := fun x => u⁻¹ * x)
          (continuous_const.mul continuous_id : Continuous (u⁻¹ * ·)) hρ1
        simpa [map_mulLeft_inv_eq_of_eq (ρ : Measure G) u (hinv u hu)] using hm }
  exact ⟨H, Measure.isClosed_support, rfl, heq,
    fun u hu v hv => hcomm u hu v (hsub₂ hv), hinv⟩

theorem normalized_rectangle_support
    [T2Space G] [SecondCountableTopology G]
    (μ ν : Measure (G × G)) [SFinite μ] [SFinite ν]
    (hμ1 : (1, 1) ∈ μ.support) (hν1 : (1, 1) ∈ ν.support)
    (hrect : ∀ᵐ p ∂μ.prod ν, p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    μ.map Prod.fst = μ.map Prod.snd ∧
    ν.map Prod.fst = ν.map Prod.snd ∧
    (1 : G) ∈ (μ.map Prod.fst).support ∧
    (1 : G) ∈ (ν.map Prod.fst).support ∧
    (∀ u ∈ (μ.map Prod.fst).support, ∀ v ∈ (ν.map Prod.fst).support,
      u * v = v * u) := by
  have hsup := eqOn_support_prod_of_ae_eq
    ((continuous_fst.fst).mul (continuous_snd.snd))
    ((continuous_snd.fst).mul (continuous_fst.snd)) hrect
  have hdiagμ : ∀ᵐ p ∂μ, p.1 = p.2 := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with p hp
    simpa using hsup p hp (1, 1) hν1
  have hdiagν : ∀ᵐ p ∂ν, p.1 = p.2 := by
    filter_upwards [Measure.support_mem_ae (μ := ν)] with p hp
    simpa using (hsup (1, 1) hμ1 p hp).symm
  refine ⟨Measure.map_congr hdiagμ, Measure.map_congr hdiagν,
    mem_support_map_of_continuous continuous_fst hμ1,
    mem_support_map_of_continuous continuous_fst hν1, ?_⟩
  have hcomm : ∀ᵐ p ∂(μ.map Prod.fst).prod (ν.map Prod.fst),
      p.1 * p.2 = p.2 * p.1 := by
    rw [Measure.map_prod_map μ ν measurable_fst measurable_fst]
    apply (ae_map_iff (measurable_fst.prodMap measurable_fst).aemeasurable
      (isClosed_eq (continuous_fst.mul continuous_snd)
        (continuous_snd.mul continuous_fst)).measurableSet).mpr
    have hmeas : MeasurableSet {p : (G × G) × (G × G) |
        p.1.1 * p.2.1 = p.2.1 * p.1.1} :=
      (isClosed_eq (continuous_fst.fst.mul continuous_snd.fst)
        (continuous_snd.fst.mul continuous_fst.fst)).measurableSet
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hrect, hdiagμ] with p hp hdp
    filter_upwards [hp, hdiagν] with q hpq hdq
    simpa only [hdp, hdq] using hpq
  exact eqOn_support_prod_of_ae_eq (continuous_fst.mul continuous_snd)
    (continuous_snd.mul continuous_fst) hcomm

theorem translated_law_of_rectangle (ρ : ProbabilityMeasure G)
    (μ : Measure (G × G)) (hf : μ.map Prod.fst = ρ) (hs : μ.map Prod.snd = ρ)
    (u v : G) (h : ∀ᵐ p ∂μ, p.1 * v = u * p.2) :
    translateProbability ρ u v = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [translateProbability_toMeasure]
  calc
    (ρ : Measure G).map (fun a => u * a * v⁻¹) =
        (μ.map Prod.snd).map (fun a => u * a * v⁻¹) := by rw [hs]
    _ = μ.map ((fun a => u * a * v⁻¹) ∘ Prod.snd) :=
      Measure.map_map (g := fun a => u * a * v⁻¹) (f := Prod.snd)
        ((continuous_const.mul continuous_id).mul continuous_const).measurable measurable_snd
    _ = μ.map Prod.fst := by
      apply Measure.map_congr
      filter_upwards [h] with p hp
      change u * p.2 * v⁻¹ = p.1
      rw [← hp]
      simp [mul_assoc]
    _ = ρ := hf

theorem ae_translated_law_of_rectangle [T2Space G] [SecondCountableTopology G]
    (ρ : ProbabilityMeasure G) (μ ν : Measure (G × G)) [SFinite μ] [SFinite ν]
    (hf : μ.map Prod.fst = ρ) (hs : μ.map Prod.snd = ρ)
    (h : ∀ᵐ p ∂μ.prod ν, p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∀ᵐ q ∂ν, translateProbability ρ q.1 q.2 = ρ := by
  have hmeas : MeasurableSet {p : (G × G) × (G × G) |
      p.1.1 * p.2.2 = p.2.1 * p.1.2} :=
    (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
      (continuous_snd.fst.mul continuous_fst.snd)).measurableSet
  have h' := (Measure.ae_ae_comm hmeas).mp (Measure.ae_ae_of_ae_prod h)
  filter_upwards [h'] with q hq
  exact translated_law_of_rectangle ρ μ hf hs q.1 q.2 hq

theorem ae_translated_law_of_kernel_rectangle
    [T2Space G] [SecondCountableTopology G] [HasOuterApproxClosed G]
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (μ ν : ProbabilityTheory.Kernel Z (G × G))
    [ProbabilityTheory.IsSFiniteKernel μ] [ProbabilityTheory.IsSFiniteKernel ν]
    (ρ : ProbabilityMeasure G)
    (h : ∀ᵐ z ∂σ,
      (μ z).map Prod.fst = ρ ∧ (μ z).map Prod.snd = ρ ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∀ᵐ q ∂ν ∘ₘ σ, translateProbability ρ q.1 q.2 = ρ := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_eq (continuous_translateProbability ρ) continuous_const).measurableSet
  filter_upwards [h] with z hz
  exact ae_translated_law_of_rectangle ρ (μ z) (ν z) hz.1 hz.2.1 hz.2.2

theorem normalized_polar_group_from_kernels
    [T2Space G] [SecondCountableTopology G] [HasOuterApproxClosed G]
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (μ ν : ProbabilityTheory.Kernel Z (G × G))
    [ProbabilityTheory.IsSFiniteKernel μ] [ProbabilityTheory.IsSFiniteKernel ν]
    (ρ τ : ProbabilityMeasure G)
    (h : ∀ᵐ z ∂σ,
      (μ z).map Prod.fst = ρ ∧ (μ z).map Prod.snd = ρ ∧
      (ν z).map Prod.fst = τ ∧ (ν z).map Prod.snd = τ ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.1.1 * p.2.2 = p.2.1 * p.1.2)
    (hμ : μ ∘ₘ σ = (ρ : Measure G).prod ρ)
    (hν : ν ∘ₘ σ = (τ : Measure G).prod τ)
    (z₀ : Z)
    (h₀ : (μ z₀).map Prod.fst = ρ ∧ (ν z₀).map Prod.fst = τ ∧
      (1, 1) ∈ (μ z₀).support ∧ (1, 1) ∈ (ν z₀).support ∧
      ∀ᵐ p ∂(μ z₀).prod (ν z₀), p.1.1 * p.2.2 = p.2.1 * p.1.2) :
    ∃ H : Subgroup G, IsClosed (H : Set G) ∧
      (ρ : Measure G).support = H ∧ (τ : Measure G).support = H ∧
      (∀ u ∈ H, ∀ v ∈ H, u * v = v * u) ∧
      (∀ u ∈ H, (ρ : Measure G).map (u * ·) = ρ) := by
  have hnormal := normalized_rectangle_support (μ z₀) (ν z₀)
    h₀.2.2.1 h₀.2.2.2.1 h₀.2.2.2.2
  rw [h₀.1, h₀.2.1] at hnormal
  have hρ : ∀ᵐ q ∂(τ : Measure G).prod τ,
      translateProbability ρ q.1 q.2 = ρ := by
    rw [← hν]
    apply ae_translated_law_of_kernel_rectangle σ μ ν ρ
    filter_upwards [h] with z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.2.2⟩
  have hτ : ∀ᵐ p ∂(ρ : Measure G).prod ρ,
      translateProbability τ p.1 p.2 = τ := by
    rw [← hμ]
    apply ae_translated_law_of_kernel_rectangle σ ν μ τ
    filter_upwards [h] with z hz
    refine ⟨hz.2.2.1, hz.2.2.2.1, ?_⟩
    have ht := (Measure.measurePreserving_swap (μ := ν z) (ν := μ z)).quasiMeasurePreserving.ae hz.2.2.2.2
    filter_upwards [ht] with p hp
    exact hp.symm
  exact common_abelian_support_of_translated_laws ρ τ
    hnormal.2.2.1 hnormal.2.2.2.1 hρ hτ hnormal.2.2.2.2

end

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

omit [SecondCountableTopology H₃] in
lemma continuous_trans : Continuous (fun p : (H₁ ≃ₗᵢ[ℂ] H₂) × (H₂ ≃ₗᵢ[ℂ] H₃) =>
    p.1.trans p.2) := by
  apply continuous_iff.mpr
  intro v
  exact continuous_eval.comp (continuous_snd.prodMk ((continuous_apply v).comp continuous_fst))

lemma support_rectangle (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hr : ∀ᵐ p ∂μ.prod ν, p.2.2.trans p.1.1 = p.1.2.trans p.2.1) :
    ∃ a₀ b₀ c₀ d₀, (a₀,b₀) ∈ μ.support ∧ (c₀,d₀) ∈ ν.support ∧
      d₀.trans a₀ = b₀.trans c₀ := by
  obtain ⟨⟨a₀,b₀⟩, hab⟩ := (show ∀ᵐ p ∂μ, p ∈ μ.support from Measure.support_mem_ae).exists
  obtain ⟨⟨c₀,d₀⟩, hcd⟩ := (show ∀ᵐ p ∂ν, p ∈ ν.support from Measure.support_mem_ae).exists
  refine ⟨a₀,b₀,c₀,d₀,hab,hcd,?_⟩
  exact eqOn_support_prod_of_ae_eq
    (continuous_trans.comp (continuous_snd.snd.prodMk continuous_fst.fst))
    (continuous_trans.comp (continuous_fst.snd.prodMk continuous_snd.fst)) hr
      (a₀,b₀) hab (c₀,d₀) hcd

def normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (a : H₂ ≃ₗᵢ[ℂ] H₁) : H₄ ≃ₗᵢ[ℂ] H₄ := d₀.trans (a.trans (d₀.trans a₀).symm)
def normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (b : H₄ ≃ₗᵢ[ℂ] H₃) : H₄ ≃ₗᵢ[ℂ] H₄ := b.trans b₀.symm
def normalizeC (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (c : H₃ ≃ₗᵢ[ℂ] H₁) : H₄ ≃ₗᵢ[ℂ] H₄ := b₀.trans (c.trans (d₀.trans a₀).symm)
def normalizeD (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) (d : H₄ ≃ₗᵢ[ℂ] H₂) : H₄ ≃ₗᵢ[ℂ] H₄ := d.trans d₀.symm

omit [SecondCountableTopology H₁] in
lemma continuous_normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeA a₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (d₀ v))
omit [SecondCountableTopology H₃] in
lemma continuous_normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) : Continuous (normalizeB b₀) := by
  apply continuous_iff.mpr
  intro v
  exact b₀.symm.continuous.comp (continuous_apply v)
omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] in
lemma continuous_normalizeC (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) :
    Continuous (normalizeC a₀ b₀ d₀) := by
  apply continuous_iff.mpr
  intro v
  exact (d₀.trans a₀).symm.continuous.comp (continuous_apply (b₀ v))
omit [SecondCountableTopology H₂] in
lemma continuous_normalizeD (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) : Continuous (normalizeD d₀) := by
  apply continuous_iff.mpr
  intro v
  exact d₀.symm.continuous.comp (continuous_apply v)

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] [SecondCountableTopology H₃] [SecondCountableTopology H₄] in
lemma normalized_rectangle (a₀ a : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ b : H₄ ≃ₗᵢ[ℂ] H₃)
    (c : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ d : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : d.trans a = b.trans c) :
    normalizeA a₀ d₀ a * normalizeD d₀ d = normalizeC a₀ b₀ d₀ c * normalizeB b₀ b := by
  ext v
  have hh := congrArg (fun L : H₄ ≃ₗᵢ[ℂ] H₁ => L v) hr
  simpa [normalizeA, normalizeB, normalizeC, normalizeD] using congrArg (d₀.trans a₀).symm hh

omit [SecondCountableTopology H₁] [SecondCountableTopology H₂] [SecondCountableTopology H₃] [SecondCountableTopology H₄] in
lemma normalized_reference (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃)
    (c₀ : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : d₀.trans a₀ = b₀.trans c₀) :
    normalizeA a₀ d₀ a₀ = 1 ∧ normalizeB b₀ b₀ = 1 ∧
    normalizeC a₀ b₀ d₀ c₀ = 1 ∧ normalizeD d₀ d₀ = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v; simp [normalizeA]
  · ext v; simp [normalizeB]
  · ext v
    change (d₀.trans a₀).symm ((b₀.trans c₀) v) = v
    rw [← hr]
    exact (d₀.trans a₀).symm_apply_apply v
  · ext v; simp [normalizeD]

end StrongUnitary

section
open MeasureTheory ProbabilityTheory
variable {Z X Y A B : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B]
  {f : X → A} {g : Y → B}
lemma map_pair_fst (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.fst = (μ.map Prod.fst).map f := by
  rw [Measure.map_map measurable_fst (hf.prodMap hg), Measure.map_map hf measurable_fst]
  rfl
lemma map_pair_snd (μ : Measure (X × Y)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map (Prod.map f g)).map Prod.snd = (μ.map Prod.snd).map g := by
  rw [Measure.map_map measurable_snd (hf.prodMap hg), Measure.map_map hg measurable_snd]
  rfl
lemma kernel_map_pair_fst (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.fst = ((κ z).map Prod.fst).map f := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_fst _ hf hg]
lemma kernel_map_pair_snd (κ : Kernel Z (X × Y)) (z : Z) (hf : Measurable f) (hg : Measurable g) :
    ((κ.map (Prod.map f g)) z).map Prod.snd = ((κ z).map Prod.snd).map g := by
  rw [Kernel.map_apply κ (hf.prodMap hg), map_pair_snd _ hf hg]

lemma kernel_map_pair_comp (σ : Measure Z) (κ : Kernel Z (X × Y)) (ν : Measure X) (ρ : Measure Y)
    [SFinite σ] [IsSFiniteKernel κ] [SFinite ν] [SFinite ρ]
    (hf : Measurable f) (hg : Measurable g) (hκ : κ ∘ₘ σ = ν.prod ρ) :
    (κ.map (Prod.map f g)) ∘ₘ σ = (ν.map f).prod (ρ.map g) := by
  rw [← Measure.map_comp _ _ (hf.prodMap hg), hκ, ← Measure.map_prod_map _ _ hf hg]

end

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {Z H₁ H₂ H₃ H₄ : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

lemma mapped_normalized_rectangle
    (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [SFinite μ] [SFinite ν]
    (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hr : ∀ᵐ p ∂μ.prod ν, p.2.2.trans p.1.1 = p.1.2.trans p.2.1) :
    ∀ᵐ p ∂(μ.map (Prod.map (normalizeA a₀ d₀) (normalizeB b₀))).prod
      (ν.map (Prod.map (normalizeC a₀ b₀ d₀) (normalizeD d₀))),
      p.1.1 * p.2.2 = p.2.1 * p.1.2 := by
  let fm := (continuous_normalizeA a₀ d₀).prodMap (continuous_normalizeB b₀)
  let gm := (continuous_normalizeC a₀ b₀ d₀).prodMap (continuous_normalizeD d₀)
  rw [Measure.map_prod_map _ _ fm.measurable gm.measurable]
  apply (ae_map_iff (fm.prodMap gm).measurable.aemeasurable
    (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
      (continuous_snd.fst.mul continuous_fst.snd)).measurableSet).mpr
  exact hr.mono fun p hp => normalized_rectangle a₀ p.1.1 b₀ p.1.2 p.2.1 d₀ p.2.2 hp

omit [SecondCountableTopology H₁] in
lemma normalized_supports
    (μ : Measure ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)))
    (ν : Measure ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂)))
    (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃)
    (c₀ : H₃ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (hab : (a₀,b₀) ∈ μ.support) (hcd : (c₀,d₀) ∈ ν.support)
    (hr : d₀.trans a₀ = b₀.trans c₀) :
    (1,1) ∈ (μ.map (Prod.map (normalizeA a₀ d₀) (normalizeB b₀))).support ∧
    (1,1) ∈ (ν.map (Prod.map (normalizeC a₀ b₀ d₀) (normalizeD d₀))).support := by
  have hh := normalized_reference a₀ b₀ c₀ d₀ hr
  constructor
  · have hm := mem_support_map_of_continuous
      ((continuous_normalizeA a₀ d₀).prodMap (continuous_normalizeB b₀)) hab
    simpa only [Prod.map_apply, hh.1, hh.2.1] using hm
  · have hm := mem_support_map_of_continuous
      ((continuous_normalizeC a₀ b₀ d₀).prodMap (continuous_normalizeD d₀)) hcd
    simpa only [Prod.map_apply, hh.2.2.1, hh.2.2.2] using hm


lemma polar_normalization (σ : Measure Z) [IsProbabilityMeasure σ]
    (μ : Kernel Z ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃))) [IsMarkovKernel μ]
    (ν : Kernel Z ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂))) [IsMarkovKernel ν]
    (ρa : ProbabilityMeasure (H₂ ≃ₗᵢ[ℂ] H₁)) (ρb : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₃))
    (ρc : ProbabilityMeasure (H₃ ≃ₗᵢ[ℂ] H₁)) (ρd : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₂))
    (h : ∀ᵐ z ∂σ, (μ z).map Prod.fst = ρa ∧ (μ z).map Prod.snd = ρb ∧
      (ν z).map Prod.fst = ρc ∧ (ν z).map Prod.snd = ρd ∧
      ∀ᵐ p ∂(μ z).prod (ν z), p.2.2.trans p.1.1 = p.1.2.trans p.2.1)
    (hμ : μ ∘ₘ σ = (ρa : Measure _).prod ρb)
    (hν : ν ∘ₘ σ = (ρc : Measure _).prod ρd) :
    ∃ (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
      (G : Subgroup (H₄ ≃ₗᵢ[ℂ] H₄)),
      IsClosed (G : Set (H₄ ≃ₗᵢ[ℂ] H₄)) ∧
      (ρa : Measure _).map (normalizeA a₀ d₀) = (ρb : Measure _).map (normalizeB b₀) ∧
      (ρc : Measure _).map (normalizeC a₀ b₀ d₀) = (ρd : Measure _).map (normalizeD d₀) ∧
      ((ρa : Measure _).map (normalizeA a₀ d₀)).support = G ∧
      ((ρc : Measure _).map (normalizeC a₀ b₀ d₀)).support = G ∧
      (∀ u ∈ G, ∀ v ∈ G, u * v = v * u) ∧
      (∀ u ∈ G, ((ρa : Measure _).map (normalizeA a₀ d₀)).map (u * ·) =
        (ρa : Measure _).map (normalizeA a₀ d₀)) := by
  obtain ⟨z₀,hz₀⟩ := h.exists
  obtain ⟨a₀,b₀,c₀,d₀,hab,hcd,hr⟩ := support_rectangle (μ z₀) (ν z₀) hz₀.2.2.2.2
  let fa := normalizeA a₀ d₀
  let fb := normalizeB b₀
  let fc := normalizeC a₀ b₀ d₀
  let fd := normalizeD d₀
  have hfa : Measurable fa := (continuous_normalizeA a₀ d₀).measurable
  have hfb : Measurable fb := (continuous_normalizeB b₀).measurable
  have hfc : Measurable fc := (continuous_normalizeC a₀ b₀ d₀).measurable
  have hfd : Measurable fd := (continuous_normalizeD d₀).measurable
  let κ := μ.map (Prod.map fa fb)
  let ξ := ν.map (Prod.map fc fd)
  let ρ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) := ρa.map fa
  let τ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) := ρc.map fc
  have hf : ∀ᵐ z ∂σ, (κ z).map Prod.fst = ρ ∧ (κ z).map Prod.snd = (ρb : Measure _).map fb ∧
      (ξ z).map Prod.fst = τ ∧ (ξ z).map Prod.snd = (ρd : Measure _).map fd := by
    filter_upwards [h] with z hz
    simp only [κ, ξ, kernel_map_pair_fst _ _ hfa hfb, kernel_map_pair_snd _ _ hfa hfb,
      kernel_map_pair_fst _ _ hfc hfd, kernel_map_pair_snd _ _ hfc hfd,
      hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1]
    exact ⟨rfl,trivial,rfl,trivial⟩
  have hrect : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1*p.2.2 = p.2.1*p.1.2 := by
    filter_upwards [h] with z hz
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact mapped_normalized_rectangle (μ z) (ν z) a₀ b₀ d₀ hz.2.2.2.2
  have h₀rect : ∀ᵐ p ∂(κ z₀).prod (ξ z₀), p.1.1*p.2.2 = p.2.1*p.1.2 := by
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact mapped_normalized_rectangle (μ z₀) (ν z₀) a₀ b₀ d₀ hz₀.2.2.2.2
  have h₀support : (1,1) ∈ (κ z₀).support ∧ (1,1) ∈ (ξ z₀).support := by
    dsimp [κ, ξ]
    rw [Kernel.map_apply _ (hfa.prodMap hfb), Kernel.map_apply _ (hfc.prodMap hfd)]
    exact normalized_supports (μ z₀) (ν z₀) a₀ b₀ c₀ d₀ hab hcd hr
  have h₀fa : (κ z₀).map Prod.fst = ρ := by
    rw [kernel_map_pair_fst _ _ hfa hfb, hz₀.1]; rfl
  have h₀fb : (κ z₀).map Prod.snd = (ρb : Measure _).map fb := by
    rw [kernel_map_pair_snd _ _ hfa hfb, hz₀.2.1]
  have h₀fc : (ξ z₀).map Prod.fst = τ := by
    rw [kernel_map_pair_fst _ _ hfc hfd, hz₀.2.2.1]; rfl
  have h₀fd : (ξ z₀).map Prod.snd = (ρd : Measure _).map fd := by
    rw [kernel_map_pair_snd _ _ hfc hfd, hz₀.2.2.2.1]
  have hn := normalized_rectangle_support (κ z₀) (ξ z₀) h₀support.1 h₀support.2 h₀rect
  have heρ : (ρ : Measure _) = (ρb : Measure _).map fb := h₀fa.symm.trans (hn.1.trans h₀fb)
  have heτ : (τ : Measure _) = (ρd : Measure _).map fd := h₀fc.symm.trans (hn.2.1.trans h₀fd)
  have hκ : κ ∘ₘ σ = (ρ : Measure _).prod ρ := by
    rw [kernel_map_pair_comp σ μ _ _ hfa hfb hμ, ←heρ]; rfl
  have hξ : ξ ∘ₘ σ = (τ : Measure _).prod τ := by
    rw [kernel_map_pair_comp σ ν _ _ hfc hfd hν, ←heτ]; rfl
  obtain ⟨G,hG,hρ,hτ,hcomm,hinv⟩ := normalized_polar_group_from_kernels σ κ ξ ρ τ
    (by filter_upwards [hf,hrect] with z hz hrz
        exact ⟨hz.1, hz.2.1.trans heρ.symm, hz.2.2.1, hz.2.2.2.trans heτ.symm, hrz⟩)
    hκ hξ z₀ ⟨h₀fa,h₀fc,h₀support.1,h₀support.2,h₀rect⟩
  exact ⟨a₀,b₀,d₀,G,hG,heρ,heτ,hρ,hτ,hcomm,hinv⟩
end StrongUnitary

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
variable {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace V]
  {μ : Measure Ω} [SFinite μ] {z : Ω → Z} {v : Ω → V}
  {κ : Kernel Z V} [IsSFiniteKernel κ]
lemma law_comp (h : HasCondDistrib v z κ μ) : κ ∘ₘ μ.map z = μ.map v := by
  rw [← Measure.snd_compProd, ← h.map_eq, Measure.snd_map_prodMk₀ h.aemeasurable_fst h.aemeasurable_snd]

lemma ae_kernel (h : HasCondDistrib v z κ μ) {p : V → Prop}
    (hp : MeasurableSet {v | p v}) (hv : ∀ᵐ ω ∂μ, p (v ω)) :
    ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun q => p q.2)
  rw [←h.map_eq]
  exact (ae_map_iff h.aemeasurable (hp.preimage measurable_snd)).mpr hv
end ConditionalFibres

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
variable {Ω Z X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {z : Ω → Z} {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
  (a : X → H₂ ≃ₗᵢ[ℂ] H₁) (b : Y → H₄ ≃ₗᵢ[ℂ] H₃)
  (p : C → H₃ ≃ₗᵢ[ℂ] H₁) (q : D → H₄ ≃ₗᵢ[ℂ] H₂)

lemma polar_pair_laws (ha : Measurable a) (hb : Measurable b)
    (hp : Measurable p) (hq : Measurable q)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (μX.prod μY))
    (hcd : MeasurePreserving (fun ω => (c ω,d ω)) μ (μC.prod μD))
    (hr : ∀ᵐ ω ∂μ, (q (d ω)).trans (a (x ω)) = (b (y ω)).trans (p (c ω))) :
    let α := κ.map (Prod.map a b)
    let β := ξ.map (Prod.map p q)
    (∀ᵐ v ∂μ.map z, (α v).map Prod.fst = μX.map a ∧ (α v).map Prod.snd = μY.map b ∧
      (β v).map Prod.fst = μC.map p ∧ (β v).map Prod.snd = μD.map q ∧
      ∀ᵐ w ∂(α v).prod (β v), w.2.2.trans w.1.1 = w.1.2.trans w.2.1) ∧
    α ∘ₘ μ.map z = (μX.map a).prod (μY.map b) ∧
    β ∘ₘ μ.map z = (μC.map p).prod (μD.map q) := by
  let R : ((H₂ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₃)) ×
      ((H₃ ≃ₗᵢ[ℂ] H₁) × (H₄ ≃ₗᵢ[ℂ] H₂)) → Prop :=
    fun w => w.2.2.trans w.1.1 = w.1.2.trans w.2.1
  have hmR : MeasurableSet {w | R w} :=
    (isClosed_eq (StrongUnitary.continuous_trans.comp (continuous_snd.snd.prodMk continuous_fst.fst))
      (StrongUnitary.continuous_trans.comp (continuous_fst.snd.prodMk continuous_snd.fst))).measurableSet
  have hr' := ConditionalFibres.ae_kernel hpair (hmR.preimage ((ha.prodMap hb).prodMap (hp.prodMap hq))) hr
  refine ⟨?_, kernel_map_pair_comp _ _ _ _ ha hb ((ConditionalFibres.law_comp hκ).trans hxy.map_eq),
    kernel_map_pair_comp _ _ _ _ hp hq ((ConditionalFibres.law_comp hξ).trans hcd.map_eq)⟩
  filter_upwards [hκm,hξm,hr'] with v hm hn hv
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [kernel_map_pair_fst _ _ ha hb,hm.1]
  · rw [kernel_map_pair_snd _ _ ha hb,hm.2]
  · rw [kernel_map_pair_fst _ _ hp hq,hn.1]
  · rw [kernel_map_pair_snd _ _ hp hq,hn.2]
  · rw [Kernel.map_apply _ (ha.prodMap hb),Kernel.map_apply _ (hp.prodMap hq),
      Measure.map_prod_map _ _ (ha.prodMap hb) (hp.prodMap hq)]
    apply (ae_map_iff ((ha.prodMap hb).prodMap (hp.prodMap hq)).aemeasurable hmR).mpr
    simpa only [Kernel.prod_apply] using hv
end

section

open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped InnerProductSpace ComplexOrder Topology BigOperators


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem isClosed_positive_operators :
    IsClosed {Q : H →L[ℂ] H | Q.IsPositive} := by
  simp only [ContinuousLinearMap.isPositive_iff_complex, Set.ofPred_forall, Set.ofPred_and]
  exact isClosed_iInter fun x =>
    (isClosed_eq (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (((ContinuousLinearMap.apply ℂ H x).continuous).inner
        continuous_const)))
      (((ContinuousLinearMap.apply ℂ H x).continuous).inner continuous_const)).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp
        (((ContinuousLinearMap.apply ℂ H x).continuous).inner continuous_const)))

omit [CompleteSpace H] in

theorem convex_positive_operators :
    Convex ℝ {Q : H →L[ℂ] H | Q.IsPositive} := by
  intro A hA B hB a b ha hb _
  change (a • A + b • B).IsPositive
  have hA' : ((a : ℂ) • A).IsPositive := hA.smul_of_nonneg (by exact_mod_cast ha)
  have hB' : ((b : ℂ) • B).IsPositive := hB.smul_of_nonneg (by exact_mod_cast hb)
  simpa only [Complex.coe_smul] using hA'.add hB'

section Integral
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem positive_compact_integral {F : X → H →L[ℂ] H}
    (hF : Integrable F μ) (hp : ∀ᵐ x ∂μ, (F x).IsPositive)
    (hc : ∀ᵐ x ∂μ, IsCompactOperator (F x)) :
    (∫ x, F x ∂μ).IsPositive ∧ IsCompactOperator (⇑(∫ x, F x ∂μ)) := by
  constructor
  · exact (convex_positive_operators (H := H)).integral_mem
      (isClosed_positive_operators (H := H)) hp hF
  · have hconv : Convex ℝ {Q : H →L[ℂ] H | IsCompactOperator Q} :=
      ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex
    exact hconv.integral_mem isClosed_setOfPred_isCompactOperator hc hF

theorem strict_positive_integral {F : X → H →L[ℂ] H}
    (hF : Integrable F μ)
    (hp : ∀ v : H, v ≠ 0 → ∀ᵐ x ∂μ, 0 < (inner ℂ v (F x v)).re) :
    ∀ v : H, v ≠ 0 → 0 < (inner ℂ v ((∫ x, F x ∂μ) v)).re := by
  intro v hv
  have hFi : Integrable (fun x => F x v) μ := (ContinuousLinearMap.apply ℂ H v).integrable_comp hF
  have hinner : Integrable (fun x => inner ℂ v (F x v)) μ :=
    (innerSL ℂ v).integrable_comp hFi
  have hreal : Integrable (fun x => (inner ℂ v (F x v)).re) μ := hinner.re
  rw [ContinuousLinearMap.integral_apply hF]
  have hi := (innerSL ℂ v).integral_comp_comm hFi
  change (∫ x, inner ℂ v (F x v) ∂μ) = inner ℂ v (∫ x, F x v ∂μ) at hi
  rw [← hi]
  change 0 < RCLike.re (∫ x, inner ℂ v (F x v) ∂μ)
  rw [← integral_re hinner]
  apply (integral_pos_iff_support_of_nonneg_ae ((hp v hv).mono fun _ h => h.le) hreal).2
  have : Function.support (fun x => (inner ℂ v (F x v)).re) =ᵐ[μ] Set.univ := by
    filter_upwards [hp v hv] with x hx
    apply propext
    change ((inner ℂ v (F x v)).re ≠ 0) ↔ True
    exact iff_of_true (ne_of_gt hx) trivial
  rw [measure_congr this, measure_univ]
  exact zero_lt_one

omit [CompleteSpace H] in

theorem injective_of_strict_positive (Q : H →L[ℂ] H)
    (hQ : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) : Function.Injective Q := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change Q v = 0 at hv
  by_contra hv'
  have := hQ v hv'
  simp [hv] at this

end Integral
section Conjugation

noncomputable def conjugateOperator (U : H ≃ₗᵢ[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  U.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] theorem conjugateOperator_apply (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) (v : H) :
    conjugateOperator U Q v = U (Q (U.symm v)) := rfl

omit [CompleteSpace H] in
@[simp] theorem conjugateOperator_mul (U V : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) :
    conjugateOperator (U * V) Q = conjugateOperator U (conjugateOperator V Q) := rfl

theorem conjugateOperator_positive (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : Q.IsPositive) : (conjugateOperator U Q).IsPositive := by
  have he : conjugateOperator U Q =
      (U : H →L[ℂ] H) ∘L Q ∘L (U : H →L[ℂ] H).adjoint := by
    ext v
    simp only [conjugateOperator_apply, LinearIsometryEquiv.adjoint_eq_symm,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [he]
  exact hQ.conj_adjoint (U : H →L[ℂ] H)

omit [CompleteSpace H] in
theorem conjugateOperator_compact (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : IsCompactOperator Q) : IsCompactOperator (conjugateOperator U Q) :=
  (hQ.comp_clm (U.symm : H →L[ℂ] H)).clm_comp (U : H →L[ℂ] H)

omit [CompleteSpace H] in
theorem conjugateOperator_strict_positive (U : H ≃ₗᵢ[ℂ] H) {Q : H →L[ℂ] H}
    (hQ : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (conjugateOperator U Q v)).re := by
  intro v hv
  have hUv : U.symm v ≠ 0 := by simpa using hv
  have hi := U.inner_map_map (U.symm v) (Q (U.symm v))
  simp only [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [conjugateOperator_apply, hi]
  exact hQ _ hUv

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem averaged_conjugates_commute (U : G →* (H ≃ₗᵢ[ℂ] H)) (Q : H →L[ℂ] H)
    (hm : ∀ g : G, Measurable (fun x : G => g * x))
    (hinv : ∀ g : G, Measure.map (fun x : G => g * x) μ = μ)
    (hF : Integrable (fun x => conjugateOperator (U x) Q) μ) (g : G) :
    (∫ x, conjugateOperator (U x) Q ∂μ) ∘L (U g : H →L[ℂ] H) =
      (U g : H →L[ℂ] H) ∘L (∫ x, conjugateOperator (U x) Q ∂μ) := by
  have hi : conjugateOperator (U g) (∫ x, conjugateOperator (U x) Q ∂μ) =
      ∫ x, conjugateOperator (U x) Q ∂μ := by
    rw [← (conjugateOperator (U g)).integral_comp_comm hF]
    simp_rw [← conjugateOperator_mul, ← map_mul]
    have hmeas : AEStronglyMeasurable (fun x => conjugateOperator (U x) Q)
        (Measure.map (fun x : G => g * x) μ) := by
      rw [hinv g]
      exact hF.aestronglyMeasurable
    rw [← integral_map (hm g).aemeasurable hmeas, hinv g]
  ext v
  have hv := congrArg (fun A : H →L[ℂ] H => A (U g v)) hi
  change (∫ x, conjugateOperator (U x) Q ∂μ) (U g v) =
    U g ((∫ x, conjugateOperator (U x) Q ∂μ) v)
  simpa only [conjugateOperator_apply, LinearIsometryEquiv.symm_apply_apply] using hv.symm

theorem averaged_positive_compact_injective
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (Q : H →L[ℂ] H)
    (hm : ∀ g : G, Measurable (fun x : G => g * x))
    (hinv : ∀ g : G, Measure.map (fun x : G => g * x) μ = μ)
    (hp : Q.IsPositive) (hc : IsCompactOperator Q)
    (hs : ∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re)
    (hF : Integrable (fun x => conjugateOperator (U x) Q) μ) :
    ∃ Q₀ : H →L[ℂ] H, Q₀.IsPositive ∧ IsCompactOperator Q₀ ∧ Function.Injective Q₀ ∧
      ∀ g : G, Q₀ ∘L (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) ∘L Q₀ := by
  let Q₀ : H →L[ℂ] H := ∫ x, conjugateOperator (U x) Q ∂μ
  have hpc := positive_compact_integral hF
    (Filter.Eventually.of_forall fun x => conjugateOperator_positive (U x) hp)
    (Filter.Eventually.of_forall fun x => conjugateOperator_compact (U x) hc)
  refine ⟨Q₀, hpc.1, hpc.2, ?_, averaged_conjugates_commute U Q hm hinv hF⟩
  apply injective_of_strict_positive
  exact strict_positive_integral hF fun v hv =>
    Filter.Eventually.of_forall fun x => conjugateOperator_strict_positive (U x) hs v hv

end Conjugation
section CompactSeed

noncomputable def quadraticFormCLM (v : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ H v)).restrictScalars ℝ)

omit [CompleteSpace H] in
@[simp] theorem quadraticFormCLM_apply (v : H) (Q : H →L[ℂ] H) :
    quadraticFormCLM v Q = (inner ℂ v (Q v)).re := rfl

omit [CompleteSpace H] in
theorem weighted_rankOne_quadratic (w v : H) (c : ℝ) :
    quadraticFormCLM v ((c : ℂ) • rankOne ℂ w w) =
      c * Complex.normSq (inner ℂ w v) := by
  simp only [quadraticFormCLM_apply, smul_apply, rankOne_apply,
    inner_smul_right]
  rw [← inner_conj_symm v w, Complex.mul_conj]
  simp

omit [CompleteSpace H] in
theorem compact_rankOne (v w : H) : IsCompactOperator (rankOne ℂ v w) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ w)).clm_comp
    (toSpanSingleton ℂ v)

theorem positive_compact_tsum {F : ℕ → H →L[ℂ] H} (hF : Summable F)
    (hp : ∀ n, (F n).IsPositive) (hc : ∀ n, IsCompactOperator (F n)) :
    (∑' n, F n).IsPositive ∧ IsCompactOperator (⇑(∑' n, F n)) := by
  constructor
  · exact (isClosed_positive_operators (H := H)).mem_of_tendsto hF.hasSum
      (Filter.Eventually.of_forall fun s => ContinuousLinearMap.isPositive_sum s fun n _ => hp n)
  · apply isCompactOperator_of_tendsto hF.hasSum
    exact Filter.Eventually.of_forall fun s =>
      (compactOperator (RingHom.id ℂ) H H).sum_mem fun n _ => hc n

omit [CompleteSpace H] in

theorem dense_sequence_inner_ne_zero {w : ℕ → H} (hw : DenseRange w)
    (v : H) (hv : v ≠ 0) : ∃ n, inner ℂ (w n) v ≠ 0 := by
  by_contra! hn
  have hclosed : IsClosed {x : H | inner ℂ x v = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : Set.range w ⊆ {x : H | inner ℂ x v = 0} := by
    rintro _ ⟨n, rfl⟩
    exact hn n
  have hall := hclosed.closure_subset_iff.mpr hsub
  rw [hw.closure_range] at hall
  exact hv (inner_self_eq_zero.mp (hall (Set.mem_univ v)))

omit [CompleteSpace H] in

theorem weighted_rankOne_tsum_strict {w : ℕ → H} (hw : DenseRange w)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hs : Summable (fun n => (c n : ℂ) • rankOne ℂ (w n) (w n))) :
    ∀ v : H, v ≠ 0 →
      0 < (inner ℂ v ((∑' n, (c n : ℂ) • rankOne ℂ (w n) (w n)) v)).re := by
  intro v hv
  obtain ⟨n, hn⟩ := dense_sequence_inner_ne_zero hw v hv
  change 0 < quadraticFormCLM v (∑' n, (c n : ℂ) • rankOne ℂ (w n) (w n))
  rw [(quadraticFormCLM v).map_tsum hs]
  have hsum := (quadraticFormCLM v).summable hs
  have hnonneg (m : ℕ) : 0 ≤ quadraticFormCLM v ((c m : ℂ) • rankOne ℂ (w m) (w m)) := by
    rw [weighted_rankOne_quadratic]
    exact mul_nonneg (hc m).le (Complex.normSq_nonneg _)
  have hpos : 0 < quadraticFormCLM v ((c n : ℂ) • rankOne ℂ (w n) (w n)) := by
    rw [weighted_rankOne_quadratic]
    exact mul_pos (hc n) (Complex.normSq_pos.mpr hn)
  exact hpos.trans_le (hsum.le_tsum n fun m _ => hnonneg m)

noncomputable def compactSeedWeight (w : ℕ → H) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖w n‖ ^ 2)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem compactSeedWeight_pos (w : ℕ → H) (n : ℕ) : 0 < compactSeedWeight w n := by
  unfold compactSeedWeight
  positivity

omit [CompleteSpace H] in
theorem compactSeedWeight_bound (w : ℕ → H) (n : ℕ) :
    ‖(compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_smul, norm_rankOne, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
    (compactSeedWeight_pos w n)]
  unfold compactSeedWeight
  rw [← sq, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖w n‖ ^ 2)).2
  have h : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

theorem exists_positive_compact_strict [TopologicalSpace.SeparableSpace H] :
    ∃ Q : H →L[ℂ] H, Q.IsPositive ∧ IsCompactOperator Q ∧
      (∀ v : H, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) := by
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq H
  let c := compactSeedWeight w
  have hs : Summable (fun n => (c n : ℂ) • rankOne ℂ (w n) (w n)) :=
    summable_geometric_two.of_norm_bounded (compactSeedWeight_bound w)
  have hpc := positive_compact_tsum hs
    (fun n => (isPositive_rankOne_self (w n)).smul_of_nonneg
      (by exact_mod_cast (compactSeedWeight_pos w n).le))
    (fun n => (compact_rankOne (w n) (w n)).smul (c n : ℂ))
  exact ⟨_, hpc.1, hpc.2, weighted_rankOne_tsum_strict hw c
    (compactSeedWeight_pos w) hs⟩

end CompactSeed

omit [CompleteSpace H] in

theorem conjugateOperator_rankOne (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    conjugateOperator U (rankOne ℂ v w) = rankOne ℂ (U v) (U w) := by
  ext x
  simp only [conjugateOperator_apply, rankOne_apply, map_smul]
  congr 1
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (U.inner_map_map w (U.symm x)).symm

theorem norm_conjugateOperator (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) :
    ‖conjugateOperator U Q‖ = ‖Q‖ :=
  StarAlgEquiv.norm_map U.conjStarAlgEquiv Q

noncomputable def compactSeed (w : ℕ → H) : H →L[ℂ] H :=
  ∑' n, (compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)

theorem compactSeed_summable (w : ℕ → H) :
    Summable (fun n => (compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)) :=
  summable_geometric_two.of_norm_bounded (compactSeedWeight_bound w)

theorem continuous_conjugate_compactSeed {G : Type*} [TopologicalSpace G]
    (U : G → H ≃ₗᵢ[ℂ] H) (hU : ∀ v, Continuous (fun g => U g v)) (w : ℕ → H) :
    Continuous (fun g => conjugateOperator (U g) (compactSeed w)) := by
  have he (g : G) : conjugateOperator (U g) (compactSeed w) =
      ∑' n, (compactSeedWeight w n : ℂ) • rankOne ℂ (U g (w n)) (U g (w n)) := by
    unfold compactSeed
    rw [(conjugateOperator (U g)).map_tsum (compactSeed_summable w)]
    simp only [map_smul, conjugateOperator_rankOne]
  simp_rw [he]
  refine continuous_tsum (u := fun n => (1 / 2 : ℝ) ^ n) (fun n => ?_)
    summable_geometric_two (fun n g => ?_)
  · simp only [rankOne_def]
    exact (((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
      ((innerSL ℂ).continuous.comp (hU (w n)))).clm_apply (hU (w n))).const_smul
        (compactSeedWeight w n : ℂ)
  ·
    rw [← conjugateOperator_rankOne, ← map_smul, norm_conjugateOperator]
    exact compactSeedWeight_bound w n

theorem compactSeed_properties {w : ℕ → H} (hw : DenseRange w) :
    (compactSeed w).IsPositive ∧ IsCompactOperator (compactSeed w) ∧
      ∀ v, v ≠ 0 → 0 < (inner ℂ v (compactSeed w v)).re := by
  have hs := compactSeed_summable w
  have hpc := positive_compact_tsum hs
    (fun n => (isPositive_rankOne_self (w n)).smul_of_nonneg
      (by exact_mod_cast (compactSeedWeight_pos w n).le))
    (fun n => (compact_rankOne (w n) (w n)).smul (compactSeedWeight w n : ℂ))
  exact ⟨hpc.1, hpc.2, weighted_rankOne_tsum_strict hw _ (compactSeedWeight_pos w) hs⟩

theorem exists_invariant_positive_compact
    [TopologicalSpace.SeparableSpace H] {G : Type*} [Group G]
    [TopologicalSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ v, Continuous (fun g => U g v))
    (hinv : ∀ g : G, Measure.map (fun x => g * x) μ = μ) :
    ∃ Q₀ : H →L[ℂ] H, Q₀.IsPositive ∧ IsCompactOperator Q₀ ∧ Function.Injective Q₀ ∧
      ∀ g : G, Q₀ ∘L (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) ∘L Q₀ := by
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq H
  obtain ⟨hp, hc, hs⟩ := compactSeed_properties hw
  apply averaged_positive_compact_injective (μ := μ) U (compactSeed w)
    (fun g => measurable_const.mul measurable_id) hinv hp hc hs
  exact Integrable.of_bound (continuous_conjugate_compactSeed U hU w).aestronglyMeasurable
    ‖compactSeed w‖ (Filter.Eventually.of_forall fun g => (norm_conjugateOperator (U g) _).le)

end

section
open Module.End ContinuousLinearMap
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma symmetric_joint_total (Q : H →L[ℂ] H) (S : J → H →L[ℂ] H)
    (hQ : Q.IsPositive) (hc : IsCompactOperator Q) (hi : Function.Injective Q)
    (hS : ∀ j, (S j).toLinearMap.IsSymmetric)
    (hQS : ∀ j, Commute Q (S j)) (hSS : ∀ i j, Commute (S i) (S j)) :
    (⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)).topologicalClosure = ⊤ := by
  let P := ⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)
  have hE (μ : ℂ) : eigenspace Q.toLinearMap μ ≤ P := by
    by_cases hμ : μ = 0
    · subst μ
      intro x hx
      have hx0 : Q x = Q 0 := by simpa [mem_eigenspace_iff] using hx
      exact hi hx0 ▸ P.zero_mem
    let E := eigenspace Q.toLinearMap μ
    let : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ
    have hInv (j) : ∀ x ∈ E, S j x ∈ E := by
      intro x hx
      apply mem_eigenspace_iff.mpr
      have hx := mem_eigenspace_iff.mp hx
      change Q x = μ • x at hx
      calc
        Q (S j x) = S j (Q x) := congrArg (fun A : H →L[ℂ] H => A x) (hQS j)
        _ = μ • S j x := by rw [hx, map_smul]
    let R : J → E →ₗ[ℂ] E := fun j => (S j).toLinearMap.restrict (hInv j)
    have hRs (j) : (R j).IsSymmetric := (hS j).restrict_invariant (hInv j)
    have hRc (i j) : Commute (R i) (R j) := by
      ext v
      exact congrArg (fun A : H →L[ℂ] H => A (v : H)) (hSS i j)
    have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hRs
      (fun i j _ => hRc i j)
    intro x hx
    have hx' : (⟨x,hx⟩ : E) ∈ ⨆ χ : J → ℂ, ⨅ j, eigenspace (R j) (χ j) := by
      rw [htop]; trivial
    change (⟨x,hx⟩ : E).val ∈ P
    apply Submodule.iSup_induction (motive := fun v : E => (v : H) ∈ P) _ hx'
    · intro χ v hv
      apply (le_iSup (fun χ : J → ℂ => ⨅ j, eigenspace (S j).toLinearMap (χ j)) χ)
      apply (Submodule.mem_iInf _).mpr
      intro j
      have hvj := mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv j)
      exact mem_eigenspace_iff.mpr (congrArg Subtype.val hvj)
    · exact P.zero_mem
    · intro v w hv hw
      exact P.add_mem hv hw
  have hQt : (⨆ μ, eigenspace Q.toLinearMap μ).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hQ.isSymmetric)
  apply top_unique
  rw [←hQt]
  exact Submodule.topologicalClosure_mono (iSup_le hE)

end

section
open Module.End ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryPart (A : H →L[ℂ] H) : Bool → selfAdjoint (H →L[ℂ] H)
  | false => realPart A
  | true => imaginaryPart A

lemma part_commute {A B : H →L[ℂ] H} (h : Commute A B) (hs : Commute (star A) B) (b : Bool) :
    Commute (unitaryPart A b : H →L[ℂ] H) B := by
  cases b
  · rw [unitaryPart, realPart_apply_coe]
    exact (h.add_left hs).smul_left _
  · rw [unitaryPart, imaginaryPart_apply_coe]
    exact ((h.sub_left hs).smul_left _).smul_left _

lemma parts_commute {A B : H →L[ℂ] H} (h : Commute A B) (hs : Commute (star A) B)
    (ht : Commute A (star B)) (hst : Commute (star A) (star B)) (b c : Bool) :
    Commute (unitaryPart A b : H →L[ℂ] H) (unitaryPart B c : H →L[ℂ] H) :=
  part_commute (part_commute h.symm ht.symm c).symm
    (part_commute hs.symm hst.symm c).symm b

omit [CompleteSpace H] in
lemma unitary_clm_commute {U V : H ≃ₗᵢ[ℂ] H} (h : Commute U V) :
    Commute (U : H →L[ℂ] H) (V : H →L[ℂ] H) := by
  ext x
  exact congrArg (fun W : H ≃ₗᵢ[ℂ] H => W x) h

lemma unitary_joint_total {G : Type*} [CommGroup G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (Q : H →L[ℂ] H) (hQ : Q.IsPositive) (hc : IsCompactOperator Q)
    (hi : Function.Injective Q)
    (hQU : ∀ g, Commute Q (U g : H →L[ℂ] H)) :
    (⨆ χ : G → ℂ, ⨅ g, eigenspace (U g).toLinearMap (χ g)).topologicalClosure = ⊤ := by
  let S : G × Bool → H →L[ℂ] H := fun p => unitaryPart (U p.1 : H →L[ℂ] H) p.2
  have hcomm (g h : G) : Commute (U g : H →L[ℂ] H) (U h : H →L[ℂ] H) :=
    unitary_clm_commute (by rw [Commute, SemiconjBy, ←map_mul, ←map_mul, mul_comm])
  have hstar (g : G) : star (U g : H →L[ℂ] H) = (U g⁻¹ : H →L[ℂ] H) := by
    simp only [LinearIsometryEquiv.star_eq_symm, map_inv]; rfl
  have hQS (p : G × Bool) : Commute Q (S p) := by
    apply Commute.symm
    apply part_commute (hQU p.1).symm
    rw [hstar]
    exact (hQU p.1⁻¹).symm
  have hSS (p q : G × Bool) : Commute (S p) (S q) := by
    apply parts_commute (hcomm p.1 q.1)
    · rw [hstar]; exact hcomm _ _
    · rw [hstar]; exact hcomm _ _
    · rw [hstar, hstar]; exact hcomm _ _
  have htotal := symmetric_joint_total Q S hQ hc hi
    (fun p => (unitaryPart (U p.1 : H →L[ℂ] H) p.2).property.isSymmetric) hQS hSS
  apply top_unique
  rw [←htotal]
  apply Submodule.topologicalClosure_mono
  apply iSup_le
  intro χ
  apply le_trans ?_ (le_iSup (fun ψ : G → ℂ => ⨅ g, eigenspace (U g).toLinearMap (ψ g))
    (fun g => χ (g,false) + Complex.I * χ (g,true)))
  intro v hv
  apply (Submodule.mem_iInf _).mpr
  intro g
  apply mem_eigenspace_iff.mpr
  have hr := mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv (g,false))
  have him := mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv (g,true))
  change (realPart (U g : H →L[ℂ] H) : H →L[ℂ] H) v = χ (g,false) • v at hr
  change (imaginaryPart (U g : H →L[ℂ] H) : H →L[ℂ] H) v = χ (g,true) • v at him
  have hid := congrArg (fun A : H →L[ℂ] H => A v)
    (realPart_add_I_smul_imaginaryPart (U g : H →L[ℂ] H))
  change (U g : H →L[ℂ] H) v = _
  simpa only [add_apply, smul_apply, hr, him,
    smul_smul, ←add_smul] using hid.symm

end

section
open Module.End ContinuousLinearMap
universe u v
variable {H : Type u} {J : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma orthogonal_total_basis (E : J → Submodule ℂ H) [∀ j, CompleteSpace (E j)]
    (ho : OrthogonalFamily ℂ (fun j => E j) (fun j => (E j).subtypeₗᵢ))
    (ht : (⨆ j, E j).topologicalClosure = ⊤) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (q : I → J), ∀ i, b i ∈ E (q i) := by
  choose W B hB using (fun j => exists_hilbertBasis ℂ (E j))
  let v : (Σ j, W j) → H := fun i => (B i.1 i.2 : H)
  have hv : Orthonormal ℂ v := ho.orthonormal_sigma_orthonormal (fun j => (B j).orthonormal)
  let P := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have hEP (j : J) : E j ≤ P := by
    let R := P.comap (E j).subtype
    have hR : IsClosed (R : Set (E j)) := (Submodule.isClosed_topologicalClosure (Submodule.span ℂ (Set.range v))).preimage
      continuous_subtype_val
    have hBR : Submodule.span ℂ (Set.range (B j)) ≤ R := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨j,i⟩,rfl⟩)
    have htop : (⊤ : Submodule ℂ (E j)) ≤ R := by
      rw [←(B j).dense_span]
      exact Submodule.topologicalClosure_minimal _ hBR hR
    intro x hx
    exact htop (show (⟨x,hx⟩ : E j) ∈ (⊤ : Submodule ℂ (E j)) from trivial)
  have hP : ⊤ ≤ P := by
    rw [←ht]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hEP)
      (Submodule.isClosed_topologicalClosure _)
  refine ⟨Σ j, W j, HilbertBasis.mk hv hP, Sigma.fst, ?_⟩
  intro i
  rw [HilbertBasis.coe_mk]
  exact (B i.1 i.2).property

lemma symmetric_joint_basis (S : J → H →L[ℂ] H)
    (hS : ∀ j, (S j).toLinearMap.IsSymmetric)
    (ht : (⨆ χ : J → ℂ, ⨅ j, eigenspace (S j).toLinearMap (χ j)).topologicalClosure = ⊤) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (χ : I → J → ℂ),
      ∀ i j, S j (b i) = χ i j • b i := by
  let E (χ : J → ℂ) := ⨅ j, eigenspace (S j).toLinearMap (χ j)
  have hclosed (χ : J → ℂ) : IsClosed (E χ : Set H) := by
    change IsClosed ((⨅ j, eigenspace (S j).toLinearMap (χ j) : Submodule ℂ H) : Set H)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun j => ContinuousLinearMap.isClosed_eigenspace (S j) (χ j)
  let (χ : J → ℂ) : CompleteSpace (E χ) := (hclosed χ).completeSpace_coe
  obtain ⟨I,b,χ,hb⟩ := orthogonal_total_basis E
    (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hS) ht
  refine ⟨I,b,χ,?_⟩
  intro i j
  exact mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp (hb i) j)

end

section
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

lemma hilbertBasis_countable (b : HilbertBasis I ℂ H) : Countable I := by
  classical
  let d := TopologicalSpace.denseSeq H
  let S (n : ℕ) := Function.support (fun i => b.repr (d n) i • b i)
  have hc (n) : (S n).Countable := (b.hasSum_repr (d n)).summable.countable_support
  have ht : (Set.univ : Set I) ⊆ ⋃ n, S n := by
    intro i _
    by_contra hi
    have hz (n : ℕ) : inner ℂ (b i) (d n) = 0 := by
      have hin : i ∉ S n := fun h => hi (Set.mem_iUnion.mpr ⟨n,h⟩)
      have he : b.repr (d n) i • b i = 0 := by simpa only [S, Function.mem_support, not_not] using hin
      have he' : b.repr (d n) i = 0 := (smul_eq_zero.mp he).resolve_right (b.orthonormal.ne_zero i)
      simpa only [b.repr_apply_apply] using he'
    have hz' : ∀ x : H, inner ℂ (b i) x = 0 := by
      exact congrFun ((TopologicalSpace.denseRange_denseSeq H).equalizer
        (continuous_const.inner continuous_id) continuous_const (funext hz))
    have hh := hz' (b i)
    exact b.orthonormal.ne_zero i (inner_self_eq_zero.mp hh)
  exact Set.countable_univ_iff.mp ((Set.countable_iUnion hc).mono ht)

end

section
open Module.End ContinuousLinearMap
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma unitary_joint_basis {G : Type v} [CommGroup G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (Q : H →L[ℂ] H) (hQ : Q.IsPositive) (hc : IsCompactOperator Q)
    (hi : Function.Injective Q) (hQU : ∀ g, Commute Q (U g : H →L[ℂ] H)) :
    ∃ (I : Type (max u v)) (b : HilbertBasis I ℂ H) (χ : I → G → ℂ),
      ∀ i g, U g (b i) = χ i g • b i := by
  let S : G × Bool → H →L[ℂ] H := fun p => unitaryPart (U p.1 : H →L[ℂ] H) p.2
  have hcomm (g h : G) : Commute (U g : H →L[ℂ] H) (U h : H →L[ℂ] H) :=
    unitary_clm_commute (by rw [Commute, SemiconjBy, ←map_mul, ←map_mul, mul_comm])
  have hstar (g : G) : star (U g : H →L[ℂ] H) = (U g⁻¹ : H →L[ℂ] H) := by
    simp only [LinearIsometryEquiv.star_eq_symm, map_inv]; rfl
  have hQS (p : G × Bool) : Commute Q (S p) := by
    apply Commute.symm
    apply part_commute (hQU p.1).symm
    rw [hstar]
    exact (hQU p.1⁻¹).symm
  have hSS (p q : G × Bool) : Commute (S p) (S q) := by
    apply parts_commute (hcomm p.1 q.1)
    · rw [hstar]; exact hcomm _ _
    · rw [hstar]; exact hcomm _ _
    · rw [hstar, hstar]; exact hcomm _ _
  have htotal := symmetric_joint_total Q S hQ hc hi
    (fun p => (unitaryPart (U p.1 : H →L[ℂ] H) p.2).property.isSymmetric) hQS hSS
  obtain ⟨I,b,χ,hb⟩ := symmetric_joint_basis S
    (fun p => (unitaryPart (U p.1 : H →L[ℂ] H) p.2).property.isSymmetric) htotal
  refine ⟨I,b,(fun i g => χ i (g,false) + Complex.I * χ i (g,true)),?_⟩
  intro i g
  have hr := hb i (g,false)
  have him := hb i (g,true)
  change (realPart (U g : H →L[ℂ] H) : H →L[ℂ] H) (b i) = χ i (g,false) • b i at hr
  change (imaginaryPart (U g : H →L[ℂ] H) : H →L[ℂ] H) (b i) = χ i (g,true) • b i at him
  have hid := congrArg (fun A : H →L[ℂ] H => A (b i))
    (realPart_add_I_smul_imaginaryPart (U g : H →L[ℂ] H))
  change (U g : H →L[ℂ] H) (b i) = _
  simpa only [add_apply, smul_apply, hr, him, smul_smul, ←add_smul] using hid.symm

end

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Group G]

lemma eigenvalue_norm_one (U : H ≃ₗᵢ[ℂ] H) {v : H} (hv : v ≠ 0)
    {χ : ℂ} (he : U v = χ • v) : ‖χ‖ = 1 := by
  have h := congrArg norm he
  rw [U.norm_map, norm_smul] at h
  exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) (h.symm.trans (one_mul _).symm))

lemma eigenvalue_mul (U : G →* (H ≃ₗᵢ[ℂ] H)) {v : H} (hv : v ≠ 0)
    (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) (g h : G) :
    χ (g*h) = χ g * χ h := by
  apply (smul_left_injective ℂ hv)
  change χ (g*h) • v = (χ g * χ h) • v
  rw [←he, map_mul]
  change U g (U h v) = _
  rw [he, map_smul, he, smul_smul, mul_comm]

def eigenCharacter (U : G →* (H ≃ₗᵢ[ℂ] H)) {v : H} (hv : v ≠ 0)
    (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) : G →* Circle where
  toFun g := ⟨χ g, by
    change χ g ∈ Metric.sphere 0 1
    simpa only [Metric.mem_sphere, dist_zero_right] using eigenvalue_norm_one (U g) hv (he g)⟩
  map_one' := by
    apply Subtype.ext
    change χ 1 = 1
    apply (smul_left_injective ℂ hv)
    change χ 1 • v = (1 : ℂ) • v
    rw [←he, map_one, one_smul]
    rfl
  map_mul' g h := Subtype.ext (eigenvalue_mul U hv χ he g h)

lemma continuous_eigenCharacter [TopologicalSpace G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ v, Continuous (fun g => U g v))
    {v : H} (hv : v ≠ 0) (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) :
    Continuous (eigenCharacter U hv χ he) := by
  apply Continuous.subtype_mk
  change Continuous χ
  have heq (g : G) : χ g = inner ℂ v (U g v) / inner ℂ v v := by
    rw [he, inner_smul_right, mul_div_cancel_right₀ _ (inner_self_eq_zero.not.mpr hv)]
  exact ((continuous_const.inner (hU v)).div_const _).congr (fun g => (heq g).symm)

end

section
open MeasureTheory
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

lemma subgroup_probability (G : Subgroup A) (hG : IsClosed (G : Set A))
    (μ : Measure A) [IsProbabilityMeasure μ] (hs : μ.support = (G : Set A))
    (hinv : ∀ g ∈ G, μ.map (g * ·) = μ) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧
      ν.map (fun g : G => (g : A)) = μ ∧
      ∀ g : G, ν.map (g * ·) = ν := by
  have he : MeasurableEmbedding (fun g : G => (g : A)) :=
    MeasurableEmbedding.subtype_coe hG.measurableSet
  have ha : ∀ᵐ a ∂μ, a ∈ Set.range (fun g : G => (g : A)) := by
    have hr : Set.range (fun g : G => (g : A)) = (G : Set A) := by
      ext a
      exact ⟨fun ⟨g,hg⟩ => hg ▸ g.property, fun ha => ⟨⟨a,ha⟩,rfl⟩⟩
    rw [hr, ←hs]
    exact Measure.support_mem_ae
  let ν := μ.comap (fun g : G => (g : A))
  have hn : IsProbabilityMeasure ν := isProbabilityMeasure_comap he.injective ha he.measurableSet_image'
  have hmap : ν.map (fun g : G => (g : A)) = μ := by
    change Measure.map _ (Measure.comap _ _) = _
    rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem ha]
  refine ⟨ν,hn,hmap,?_⟩
  intro g
  have hmg : Measurable (g * · : G → G) :=
    (continuous_const.mul continuous_id).measurable
  apply he.map_injective
  rw [Measure.map_map he.measurable hmg, hmap]
  change Measure.map (fun x : G => (g : A) * (x : A)) ν = μ
  have hcomp := Measure.map_map (μ := ν)
    (measurable_const.mul measurable_id : Measurable (fun x : A => (g : A) * x)) he.measurable
  exact hcomp.symm.trans ((congrArg (Measure.map (fun x : A => (g : A) * x)) hmap).trans
    (hinv g g.property))
end

namespace StrongUnitary
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]

lemma polar_spectral (G : Subgroup (H ≃ₗᵢ[ℂ] H)) (hG : IsClosed (G : Set (H ≃ₗᵢ[ℂ] H)))
    (μ : Measure (H ≃ₗᵢ[ℂ] H)) [IsProbabilityMeasure μ]
    (hs : μ.support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g*h = h*g)
    (hinv : ∀ g ∈ G, μ.map (g * ·) = μ) :
    ∃ (I : Type u) (_ : Countable I) (b : HilbertBasis I ℂ H)
      (γ : I → G →* Circle),
      (∀ i, Continuous (γ i)) ∧ ∀ i (g : G), (g : H ≃ₗᵢ[ℂ] H) (b i) = (γ i g : ℂ) • b i := by
  let : SecondCountableTopology G :=
    TopologicalSpace.Subtype.secondCountableTopology (G : Set (H ≃ₗᵢ[ℂ] H))
  let : CommGroup G := {
    (inferInstance : Group G) with
    mul_comm := fun g h => Subtype.ext (hcomm g g.property h h.property) }
  obtain ⟨ν,hn,hν,hiν⟩ := subgroup_probability G hG μ hs hinv
  let := hn
  let U : G →* (H ≃ₗᵢ[ℂ] H) := G.subtype
  have hUc (v : H) : Continuous (fun g : G => U g v) :=
    (continuous_apply v).comp continuous_subtype_val
  obtain ⟨Q,hQ,hQc,hQi,hQcU⟩ := exists_invariant_positive_compact ν U hUc hiν
  obtain ⟨I,b,χ,hb⟩ := unitary_joint_basis U Q hQ hQc hQi hQcU
  have hbne (i : I) : b i ≠ 0 := b.orthonormal.ne_zero i
  let γ (i : I) := eigenCharacter U (hbne i) (χ i) (hb i)
  refine ⟨I,hilbertBasis_countable b,b,γ,?_,?_⟩
  · intro i
    exact continuous_eigenCharacter U hUc (hbne i) (χ i) (hb i)
  · intro i g
    exact hb i g

end StrongUnitary

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
variable {Ω Z X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

def MeasurablePolarRectangle.HasHaarNormalization
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d) : Prop :=
  ∃ (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (S : Subgroup (H₄ ≃ₗᵢ[ℂ] H₄)),
    IsClosed (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) ∧
    (μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀) =
      (μY.map R.b.unitary).map (StrongUnitary.normalizeB b₀) ∧
    (μC.map R.p.unitary).map (StrongUnitary.normalizeC a₀ b₀ d₀) =
      (μD.map R.q.unitary).map (StrongUnitary.normalizeD d₀) ∧
    ((μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀)).support = S ∧
    ((μC.map R.p.unitary).map (StrongUnitary.normalizeC a₀ b₀ d₀)).support = S ∧
    (∀ u ∈ S, ∀ v ∈ S, u * v = v * u) ∧
    (∀ u ∈ S, ((μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀)).map (u * ·) =
      (μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀))

lemma MeasurablePolarRectangle.haar_normalization
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
    {z : Ω → Z} (hz : Measurable z)
    (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (μX.prod μY))
    (hcd : MeasurePreserving (fun ω => (c ω,d ω)) μ (μC.prod μD)) : R.HasHaarNormalization := by
  have : IsProbabilityMeasure (μ.map z) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hz.aemeasurable
  obtain ⟨h,hμ,hν⟩ := polar_pair_laws μX μY μC μD κ ξ
    R.a.unitary R.b.unitary R.p.unitary R.q.unitary R.a.measurable R.b.measurable
    R.p.measurable R.q.measurable hκ hξ hpair hκm hξm hxy hcd R.rectangle
  have := Kernel.IsMarkovKernel.map κ (R.a.measurable.prodMap R.b.measurable)
  have := Kernel.IsMarkovKernel.map ξ (R.p.measurable.prodMap R.q.measurable)
  exact StrongUnitary.polar_normalization (μ.map z)
    (κ.map (Prod.map R.a.unitary R.b.unitary)) (ξ.map (Prod.map R.p.unitary R.q.unitary))
    ⟨μX.map R.a.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.a.measurable.aemeasurable⟩
    ⟨μY.map R.b.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.b.measurable.aemeasurable⟩
    ⟨μC.map R.p.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.p.measurable.aemeasurable⟩
    ⟨μD.map R.q.unitary,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) R.q.measurable.aemeasurable⟩ h hμ hν
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_haar_normalization (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ R : GroupedPolarData M rows cols n e, R.HasHaarNormalization := by
  filter_upwards [pairPair_fixed_conditional M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP n,
    rowPair_fixed_conditional M rows.P cols.P cols.A cols.B n,
    columnPair_fixed_marginals M hM rows.P rows.A rows.B cols.P rows.cardP cols.properP
      rows.properA rows.properB rows.disjointPA rows.disjointPB rows.properPA rows.properPB n,
    rowPair_fixed_marginals M hM rows.P cols.P cols.A cols.B rows.properP
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.A rows.B cols.P cols.P rows.disjointAB rows.properAB n,
    cells_indep_columns_fibre M rows.P rows.P cols.A cols.B cols.disjointAB cols.properAB n]
      with e hpair hκ hξ hκm hξm hx hy hc hd hxy hcd
  intro R
  apply R.haar_normalization (measurable_cells M rows.P cols.P n)
    ((columnPairKernel M rows.P rows.A rows.B cols.P n).sectR e)
    ((rowPairKernel M rows.P cols.P cols.A cols.B n).sectR e) hκ hξ hpair
  · exact hκm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩
  · exact hξm.mono fun _ h => ⟨h.1.map_eq,h.2.map_eq⟩
  · refine ⟨hx.measurable.prodMk hy.measurable, ?_⟩
    rw [←hx.map_eq,←hy.map_eq]
    exact hxy.map_prod_eq_prod_map_map hx.measurable.aemeasurable hy.measurable.aemeasurable
  · refine ⟨hc.measurable.prodMk hd.measurable, ?_⟩
    rw [←hc.map_eq,←hd.map_eq]
    exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z}

lemma active_observation_eq (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ) (hz : MeasurePreserving z μ τ)
    (hobs : MeasurableSpace.comap y inferInstance = MeasurableSpace.comap z inferInstance) :
    (LinearMap.range (operator hx hy).toLinearMap).topologicalClosure =
      (LinearMap.range (operator hx hz).toLinearMap).topologicalClosure := by
  congr 1
  change LinearMap.range ((pull hx).adjoint.toLinearMap.comp (pull hy).toLinearMap) =
    LinearMap.range ((pull hx).adjoint.toLinearMap.comp (pull hz).toLinearMap)
  rw [LinearMap.range_comp, LinearMap.range_comp, pull_range hy, pull_range hz, hobs]

omit [MeasurableSpace Ω] in
lemma pair_comap_swap (a : Ω → Y) (b : Ω → Z) :
    MeasurableSpace.comap (fun ω => (a ω,b ω)) inferInstance =
      MeasurableSpace.comap (fun ω => (b ω,a ω)) inferInstance := by
  change ((inferInstance : MeasurableSpace Y).prod (inferInstance : MeasurableSpace Z)).comap _ =
    ((inferInstance : MeasurableSpace Z).prod (inferInstance : MeasurableSpace Y)).comap _
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_prodMk, sup_comm]
end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace essentialRange
variable {U H K : Type*} [MeasurableSpace U]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
lemma congr_ae {μ : Measure U} {F G : U → H →L[ℂ] K} (h : F =ᵐ[μ] G) :
    essentialRange μ F = essentialRange μ G := by
  unfold essentialRange
  congr 1
  ext v
  change (∀ᵐ u ∂μ, (F u).adjoint v = 0) ↔ (∀ᵐ u ∂μ, (G u).adjoint v = 0)
  exact Filter.eventually_congr (h.mono fun _ hh => by rw [hh])
end essentialRange
namespace JoiningOperator

section
variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
  (κ : Kernel U (X × Y)) (ν : Measure X) (ρ : Measure Y)

lemma swapped_marginals (u : U)
    (hx : MeasurePreserving Prod.fst (κ u) ν) (hy : MeasurePreserving Prod.snd (κ u) ρ) :
    MeasurePreserving Prod.fst ((κ.map Prod.swap) u) ρ ∧
    MeasurePreserving Prod.snd ((κ.map Prod.swap) u) ν := by
  rw [Kernel.map_apply _ measurable_swap]
  constructor
  · exact ⟨measurable_fst, by rw [Measure.map_map measurable_fst measurable_swap]; exact hy.map_eq⟩
  · exact ⟨measurable_snd, by rw [Measure.map_map measurable_snd measurable_swap]; exact hx.map_eq⟩

lemma family_swap (u : U)
    (hx : MeasurePreserving Prod.fst (κ u) ν) (hy : MeasurePreserving Prod.snd (κ u) ρ) :
    family (κ.map Prod.swap) ρ ν u = (family κ ν ρ u).adjoint := by
  have hs : MeasurePreserving Prod.swap (κ u) ((κ.map Prod.swap) u) :=
    ⟨measurable_swap, (Kernel.map_apply _ measurable_swap u).symm⟩
  obtain ⟨hx',hy'⟩ := swapped_marginals κ ν ρ u hx hy
  rw [family_eq _ _ _ _ hx' hy',family_eq _ _ _ _ hx hy,operator_adjoint]
  have h := operator_pullback (x := (Prod.fst : Y × X → Y))
    (y := (Prod.snd : Y × X → X)) (f := (Prod.swap : X × Y → Y × X)) hs hx' hy'
  exact h.symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
lemma active_eq_essentialRange_adjoint [SecondCountableTopology (Lp ℂ 2 ν)]
    (hu : Measurable u) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂μ.map u,
      MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    [IsMarkovKernel κ] :
    (LinearMap.range (operator hy ⟨hu.prodMk hx.measurable,rfl⟩).toLinearMap).topologicalClosure =
      essentialRange (μ.map u) (fun a => (family κ ν ρ a).adjoint) := by
  have : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have h := active_eq_essentialRange hu hy hx (hκ.comp_left measurable_swap)
    (hm.mono fun a ha => swapped_marginals κ ν ρ a ha.1 ha.2)
  exact h.trans (essentialRange.congr_ae (hm.mono fun a ha => family_swap κ ν ρ a ha.1 ha.2))
end

variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

lemma family_active_swap_conditioner [SecondCountableTopology (Lp ℂ 2 ρ)]
    [SecondCountableTopology (Lp ℂ 2 η)]
    {ξ : Kernel Y (X × U)} [IsMarkovKernel ξ]
    (hu : MeasurePreserving u μ η) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hmκ : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (hξ : HasCondDistrib (fun ω => (x ω,u ω)) y ξ μ)
    (hmξ : ∀ᵐ a ∂ρ, MeasurePreserving Prod.fst (ξ a) ν ∧ MeasurePreserving Prod.snd (ξ a) η) :
    essentialRange η (family κ ν ρ) = essentialRange ρ (family ξ ν η) := by
  have h₁ := active_eq_essentialRange hu.measurable hx hy hκ (hu.map_eq.symm ▸ hmκ)
  have h₂ := active_eq_essentialRange hy.measurable hx hu hξ (hy.map_eq.symm ▸ hmξ)
  rw [hu.map_eq] at h₁
  rw [hy.map_eq] at h₂
  exact h₁.symm.trans ((active_observation_eq hx _ _ (pair_comap_swap u y)).trans h₂)

lemma family_active_adjoint_reverse [SecondCountableTopology (Lp ℂ 2 ν)]
    {ξ : Kernel U (Y × X)} [IsMarkovKernel ξ]
    (hu : MeasurePreserving u μ η) (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hmκ : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (hξ : HasCondDistrib (fun ω => (y ω,x ω)) u ξ μ)
    (hmξ : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (ξ a) ρ ∧ MeasurePreserving Prod.snd (ξ a) ν) :
    essentialRange η (fun a => (family κ ν ρ a).adjoint) = essentialRange η (family ξ ρ ν) := by
  have h₁ := active_eq_essentialRange_adjoint κ ν ρ hu.measurable hx hy hκ (hu.map_eq.symm ▸ hmκ)
  have h₂ := active_eq_essentialRange hu.measurable hy hx hξ (hu.map_eq.symm ▸ hmξ)
  rw [hu.map_eq] at h₁ h₂
  exact h₁.symm.trans h₂

end JoiningOperator
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal


section
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

def rowActive (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  essentialRange (cellLaw M A S n e) (fibreRowEdge M A S R D n e)

def columnActive (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  essentialRange (cellLaw M A R n e) (fibreColumnEdge M A P B R n e)

def commonActive (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :=
  rowActive M P R S D n e ⊓ columnActive M P A B R n e

instance (A R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (rowActive M A R S D n e) := by unfold rowActive; infer_instance
instance (P A B R : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (columnActive M P A B R n e) := by unfold columnActive; infer_instance
instance (P A B R S D : Finset I) (n : ℕ) (e : Arr I M.U (n+2)) :
    CompleteSpace (commonActive M P A B R S D n e) := by
  exact (IsClosed.inter (essentialRange.isClosed (cellLaw M P S n e) (fibreRowEdge M P S R D n e))
    (essentialRange.isClosed (cellLaw M A R n e) (fibreColumnEdge M A P B R n e))).completeSpace_coe

lemma rowActive_swap (hM : M.IsSaturated) (A : Finset I) (hA : A ≠ Finset.univ)
    (cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      rowActive M A cols.P cols.A cols.B n e = rowActive M A cols.P cols.B cols.A n e := by
  filter_upwards [cells_fibre_marginal M hM A cols.A hA n,
    cells_fibre_marginal M hM A cols.P hA n,
    cells_fibre_marginal M hM A cols.B hA n,
    rowPair_fixed_conditional M A cols.A cols.P cols.B n,
    rowPair_fixed_conditional M A cols.B cols.P cols.A n,
    rowPair_fixed_marginals M hM A cols.A cols.P cols.B hA
      cols.disjointPA.symm cols.disjointAB (by simpa [Finset.union_comm] using cols.properPA) cols.properAB n,
    rowPair_fixed_marginals M hM A cols.B cols.P cols.A hA
      cols.disjointPB.symm cols.disjointAB.symm
      (by simpa [Finset.union_comm] using cols.properPB)
      (by simpa [Finset.union_comm] using cols.properAB) n] with e hs hr ht hκ hξ hmκ hmξ
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  unfold rowActive
  rw [fibreRowEdge_eq,fibreRowEdge_eq]
  exact JoiningOperator.family_active_swap_conditioner hs hr ht hκ hmκ hξ hmξ

lemma rowActive_adjoint (hM : M.IsSaturated) (A : Finset I) (hA : A ≠ Finset.univ)
    (cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      essentialRange (cellLaw M A cols.P n e) (fun r => (fibreRowEdge M A cols.P cols.A cols.B n e r).adjoint) =
        rowActive M A cols.B cols.P cols.A n e := by
  filter_upwards [cells_fibre_marginal M hM A cols.P hA n,
    cells_fibre_marginal M hM A cols.A hA n,
    cells_fibre_marginal M hM A cols.B hA n,
    rowPair_fixed_conditional M A cols.P cols.A cols.B n,
    rowPair_fixed_conditional M A cols.P cols.B cols.A n,
    rowPair_fixed_marginals M hM A cols.P cols.A cols.B hA
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n,
    rowPair_fixed_marginals M hM A cols.P cols.B cols.A hA
      cols.disjointPB cols.disjointPA cols.properPB cols.properPA n] with e hr hs ht hκ hξ hmκ hmξ
  rw [hr.map_eq] at hmκ hmξ
  unfold rowActive
  rw [fibreRowEdge_eq,fibreRowEdge_eq]
  exact JoiningOperator.family_active_adjoint_reverse hr hs ht hκ hmκ hξ hmξ

lemma columnActive_swap (hM : M.IsSaturated) (rows : TriplePartition I)
    (R : Finset I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      columnActive M rows.P rows.A rows.B R n e = columnActive M rows.P rows.B rows.A R n e := by
  filter_upwards [cells_fibre_marginal M hM rows.A R rows.properA n,
    cells_fibre_marginal M hM rows.P R rows.properP n,
    cells_fibre_marginal M hM rows.B R rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyB; omega) hR n,
    columnPair_fixed_conditional M hM rows.B rows.P rows.A R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyA; omega) hR n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyB; omega) hR rows.properP rows.properB
      rows.disjointPA.symm rows.disjointAB (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n,
    columnPair_fixed_marginals M hM rows.B rows.P rows.A R (by
      have := rows.card_eq; have := Finset.card_pos.mpr rows.nonemptyP
      have := Finset.card_pos.mpr rows.nonemptyA; omega) hR rows.properP rows.properA
      rows.disjointPB.symm rows.disjointAB.symm
      (by simpa [Finset.union_comm] using rows.properPB)
      (by simpa [Finset.union_comm] using rows.properAB) n] with e hs hr ht hκ hξ hmκ hmξ
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  unfold columnActive
  rw [fibreColumnEdge_eq,fibreColumnEdge_eq]
  exact JoiningOperator.family_active_swap_conditioner hs hr ht hκ hmκ hξ hmξ

lemma columnActive_adjoint (hM : M.IsSaturated) (rows : TriplePartition I)
    (R : Finset I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      essentialRange (cellLaw M rows.P R n e) (fun r => (fibreColumnEdge M rows.P rows.A rows.B R n e r).adjoint) =
        columnActive M rows.B rows.P rows.A R n e := by
  filter_upwards [cells_fibre_marginal M hM rows.P R rows.properP n,
    cells_fibre_marginal M hM rows.A R rows.properA n,
    cells_fibre_marginal M hM rows.B R rows.properB n,
    columnPair_fixed_conditional M hM rows.P rows.A rows.B R rows.cardP hR n,
    columnPair_fixed_conditional M hM rows.P rows.B rows.A R rows.cardP hR n,
    columnPair_fixed_marginals M hM rows.P rows.A rows.B R rows.cardP hR rows.properA rows.properB
      rows.disjointPA rows.disjointPB rows.properPA rows.properPB n,
    columnPair_fixed_marginals M hM rows.P rows.B rows.A R rows.cardP hR rows.properB rows.properA
      rows.disjointPB rows.disjointPA rows.properPB rows.properPA n] with e hr hs ht hκ hξ hmκ hmξ
  rw [hr.map_eq] at hmκ hmξ
  unfold columnActive
  rw [fibreColumnEdge_eq,fibreColumnEdge_eq]
  exact JoiningOperator.family_active_adjoint_reverse hr hs ht hκ hmκ hξ hmξ
end
section

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_rectangle_spaces (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μX := cellLaw M rows.A cols.P n e
      let μY := cellLaw M rows.B cols.P n e
      let μC := cellLaw M rows.P cols.A n e
      let μD := cellLaw M rows.P cols.B n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      rectangleSpace₁ μX μC F K = commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e ∧
      rectangleSpace₂ μX μD F N = commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e ∧
      rectangleSpace₃ μY μC G K = commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e ∧
      rectangleSpace₄ μY μD G N = commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e := by
  filter_upwards [rowActive_adjoint M hM rows.A rows.properA cols n,
    rowActive_adjoint M hM rows.B rows.properB cols n,
    columnActive_adjoint M hM rows cols.A cols.properA n,
    columnActive_adjoint M hM rows cols.B cols.properB n] with e hF hG hK hN
  dsimp only
  refine ⟨rfl,?_,?_,?_⟩
  · unfold rectangleSpace₂ commonActive
    rw [hF]
    rfl
  · unfold rectangleSpace₃ commonActive
    rw [hK]
    rfl
  · unfold rectangleSpace₄ commonActive
    rw [hG,hN]

end

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_active_intersections (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let D₁ := commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e
      let D₂ := commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e
      let D₃ := commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e
      let D₄ := commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      (∀ᵐ r ∂cellLaw M rows.A cols.P n e, D₁.starProjection ∘L F r = F r ∘L D₂.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.B cols.P n e, D₃.starProjection ∘L G r = G r ∘L D₄.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.P cols.A n e, D₁.starProjection ∘L K r = K r ∘L D₃.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.P cols.B n e, D₂.starProjection ∘L N r = N r ∘L D₄.starProjection) := by
  filter_upwards [grouped_fibre_rectangle M hM rows.P rows.A rows.B cols.P cols.A cols.B
      rows.cardP rows.disjointPA rows.disjointPB rows.cardPA rows.cardPB rows.properPA rows.properPB
      cols.disjointPA cols.disjointPB cols.disjointAB cols.cover cols.nonemptyA cols.nonemptyB n,
    rowActive_adjoint M hM rows.A rows.properA cols n,
    rowActive_adjoint M hM rows.B rows.properB cols n,
    columnActive_adjoint M hM rows cols.A cols.properA n,
    columnActive_adjoint M hM rows cols.B cols.properB n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.A cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.A cols.P rows.disjointPB rows.properPB n,
    cells_indep_rows_fibre M hM rows.P rows.A cols.B cols.P rows.disjointPA rows.properPA n,
    cells_indep_rows_fibre M hM rows.P rows.B cols.B cols.P rows.disjointPB rows.properPB n]
      with e hr hra hrb hca hcb hx hy hc hd hcx hcy hdx hdy
  dsimp only at *
  have h := rectangle_active_intersections
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
  dsimp only [rowActive,columnActive] at hra hrb hca hcb
  simpa only [commonActive,rowActive,columnActive,hra,hrb,hca,hcb] using h

end ArrayObjects.Object.Rolled

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev swapPA (s : TriplePartition I) : TriplePartition I where
  P := s.A
  A := s.P
  B := s.B
  nonemptyP := s.nonemptyA
  nonemptyA := s.nonemptyP
  nonemptyB := s.nonemptyB
  disjointPA := s.disjointPA.symm
  disjointPB := s.disjointAB
  disjointAB := s.disjointPB
  cover := by simpa only [Finset.union_comm s.A s.P] using s.cover

abbrev swapAB (s : TriplePartition I) : TriplePartition I where
  P := s.P
  A := s.B
  B := s.A
  nonemptyP := s.nonemptyP
  nonemptyA := s.nonemptyB
  nonemptyB := s.nonemptyA
  disjointPA := s.disjointPB
  disjointPB := s.disjointPA
  disjointAB := s.disjointAB.symm
  cover := by simpa only [Finset.union_assoc,Finset.union_comm s.B s.A] using s.cover

abbrev swapPB (s : TriplePartition I) : TriplePartition I where
  P := s.B
  A := s.A
  B := s.P
  nonemptyP := s.nonemptyB
  nonemptyA := s.nonemptyA
  nonemptyB := s.nonemptyP
  disjointPA := s.disjointAB.symm
  disjointPB := s.disjointPB.symm
  disjointAB := s.disjointPA.symm
  cover := by simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using s.cover
end TriplePartition

end Rokhlin

end

end OAI
