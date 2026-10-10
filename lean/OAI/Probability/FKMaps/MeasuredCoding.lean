import OAI.Probability.FKMaps.CornerMass

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT
attribute [local instance] Classical.propDecidable

/-- Equal-Lebesgue-mass time cells. The endpoint one is assigned to the last
cell; this retains a total, surjective coding without changing any mass. -/
def timeCell (N : ℕ) (hN : 0<N) (t : unitInterval) : Fin N :=
  ⟨min ⌊(N:ℝ)*t⌋₊ (N-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

lemma timeCell_measurable (N : ℕ) (hN : 0<N) : Measurable (timeCell N hN) := by
  apply measurable_to_countable
  intro t
  have he : timeCell N hN ⁻¹' {timeCell N hN t}=
      {s : unitInterval | min ⌊(N:ℝ)*s⌋₊ (N-1)=(timeCell N hN t).val} := by
    ext s
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq,Fin.ext_iff,timeCell]
  rw [he]
  exact measurableSet_eq_fun ((Nat.measurable_floor.comp
    (measurable_const.mul measurable_subtype_coe)).min measurable_const) measurable_const

lemma timeCell_of_lt_one (N : ℕ) (hN : 0<N) (t : unitInterval) (ht : (t:ℝ)<1) :
    (timeCell N hN t).val=⌊(N:ℝ)*t⌋₊ := by
  dsimp [timeCell]
  apply min_eq_left
  have hf : ⌊(N:ℝ)*t⌋₊<N := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) t.property.1)).mpr (by
    have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
    nlinarith)
  omega

lemma timeCell_eq_iff (N : ℕ) (hN : 0<N) (t : unitInterval) (ht : (t:ℝ)<1) (i : Fin N) :
    timeCell N hN t=i ↔ (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ) := by
  rw [Fin.ext_iff,timeCell_of_lt_one N hN t ht,Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) t.property.1)]
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  rw [div_le_iff₀ hp,lt_div_iff₀ hp]
  rw [mul_comm (t:ℝ)]

lemma cell_volume (N : ℕ) (hN : 0<N) (i : Fin N) :
    (volume : Measure unitInterval) {t | (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)}=
      ENNReal.ofReal (1/(N:ℝ)) := by
  rw [volume_set_coe_def,comap_subtype_coe_apply measurableSet_Icc]
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hi : (i.val+1:ℝ)≤N := by exact_mod_cast i.isLt
  have he : Subtype.val '' {t : unitInterval | (i.val:ℝ)/(N:ℝ)≤t ∧
      (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)}=Ico ((i.val:ℝ)/(N:ℝ)) ((i.val+1:ℝ)/(N:ℝ)) := by
    ext t
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro ht
      refine ⟨⟨t,?_⟩,ht,rfl⟩
      constructor
      · exact (div_nonneg (Nat.cast_nonneg _) hp.le).trans ht.1
      · exact ht.2.le.trans ((div_le_one hp).mpr hi)
  rw [he,Real.volume_Ico]
  congr 1
  field_simp
  ring

lemma timeCell_mass (N : ℕ) (hN : 0<N) (i : Fin N) :
    ((volume : Measure unitInterval).map (timeCell N hN)) {i}=ENNReal.ofReal (1/(N:ℝ)) := by
  rw [Measure.map_apply (timeCell_measurable N hN) (measurableSet_singleton i)]
  have he : timeCell N hN ⁻¹' {i}=ᵐ[volume]
      {t : unitInterval | (i.val:ℝ)/(N:ℝ)≤t ∧ (t:ℝ)<(i.val+1:ℝ)/(N:ℝ)} := by
    have hne : ∀ᵐ t : unitInterval ∂volume,t≠1 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with t ht
    have ht' : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))
    exact propext (timeCell_eq_iff N hN t ht' i)
  rw [measure_congr he,cell_volume N hN i]

lemma timeCell_map (N : ℕ) (hN : 0<N) :
    (volume : Measure unitInterval).map (timeCell N hN)=
      ∑ i : Fin N,ENNReal.ofReal (1/(N:ℝ)) • Measure.dirac i := by
  apply Measure.ext_of_singleton
  intro i
  rw [timeCell_mass N hN i]
  simp [Measure.finsetSum_apply,Pi.single_apply]

lemma timeCell_surjective (N : ℕ) (hN : 0<N) : Function.Surjective (timeCell N hN) := by
  intro i
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let t : unitInterval := ⟨(i.val:ℝ)/(N:ℝ),by constructor;positivity;exact (div_le_one hp).mpr (by exact_mod_cast i.isLt.le)⟩
  refine ⟨t,(timeCell_eq_iff N hN t (by dsimp [t];exact (div_lt_one hp).mpr (by exact_mod_cast i.isLt)) i).mpr ⟨le_rfl,?_⟩⟩
  dsimp [t]
  exact (div_lt_div_iff_of_pos_right hp).mpr (by linarith)

lemma timeCell_mono (N : ℕ) (hN : 0<N) : Monotone (timeCell N hN) := by
  intro s t hst
  change min ⌊(N:ℝ)*s⌋₊ (N-1) ≤ min ⌊(N:ℝ)*t⌋₊ (N-1)
  exact min_le_min (Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))) le_rfl

lemma timeCell_bounds (N : ℕ) (hN : 0<N) (t : unitInterval) :
    ((timeCell N hN t).val:ℝ)/(N:ℝ)≤t ∧
      (t:ℝ)≤((timeCell N hN t).val+1:ℝ)/(N:ℝ) := by
  by_cases ht : (t:ℝ)<1
  · have hh := (timeCell_eq_iff N hN t ht (timeCell N hN t)).mp rfl
    exact ⟨hh.1,hh.2.le⟩
  · have ht : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    have he : (timeCell N hN 1).val=N-1 := by simp [timeCell]
    rw [he]
    have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
    have he' : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    constructor
    · exact (div_le_one hn).mpr (by linarith)
    · change (1:ℝ)≤_
      rw [he',div_self hn.ne']

/-- The positive preorder point lies inside its equal-mass time cell. -/
def cellPoint (N : ℕ) (hN : 0<N) (i : Fin N) : unitInterval :=
  ⟨(i.val+1:ℝ)/(N+1:ℝ),by constructor;positivity;apply (div_le_one (by positivity)).mpr;exact_mod_cast Nat.add_le_add_right i.isLt.le 1⟩

lemma cellPoint_bounds (N : ℕ) (hN : 0<N) (i : Fin N) :
    (i.val:ℝ)/N≤cellPoint N hN i ∧
      (cellPoint N hN i:ℝ)≤(i.val+1:ℝ)/N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hi : (i.val:ℝ)≤N := by exact_mod_cast i.isLt.le
  change _≤(i.val+1:ℝ)/(N+1:ℝ) ∧ (i.val+1:ℝ)/(N+1:ℝ)≤_
  constructor
  · apply (div_le_div_iff₀ hn (by positivity)).mpr
    nlinarith
  · apply div_le_div_of_nonneg_left (by positivity) hn
    linarith

lemma cellPoint_close (N : ℕ) (hN : 0<N) (t : unitInterval) :
    dist (cellPoint N hN (timeCell N hN t)) t≤1/(N:ℝ) := by
  have ht := timeCell_bounds N hN t
  have hp := cellPoint_bounds N hN (timeCell N hN t)
  have he : (((timeCell N hN t).val:ℝ)+1)/(N:ℝ)-((timeCell N hN t).val:ℝ)/(N:ℝ)=1/(N:ℝ) := by ring
  rw [Subtype.dist_eq,Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith

lemma cellPoint_mono (N : ℕ) (hN : 0<N) : Monotone (cellPoint N hN) := by
  intro i j hij
  change (i.val+1:ℝ)/(N+1:ℝ)≤(j.val+1:ℝ)/(N+1:ℝ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- The exact degree-mass coding, using every nonroot preorder pole. -/
def timeVertex (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length) (s : unitInterval) : FKCRT.Vertex M :=
  t.nonrootVertex M e (FKCRT.timeCell t.word.length ht s)

lemma timeVertex_measurable (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length) :
    @Measurable _ _ inferInstance ⊤ (t.timeVertex M e ht) := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  exact (measurable_of_finite (t.nonrootVertex M e)).comp (FKCRT.timeCell_measurable _ ht)

lemma timeVertex_surjective (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    Function.Surjective (t.timeVertex M e ht) :=
  (t.nonrootVertex_surjective M e hp).comp (FKCRT.timeCell_surjective _ ht)

/-- No asymptotic replacement of the degree measure is needed. -/
theorem timeVertex_mass (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (hlen : t.word.length=2*(n+1)) :
    @Measure.map _ _ inferInstance ⊤ (t.timeVertex M e ht) volume=FKCRT.degreeMass M := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  change (volume : Measure unitInterval).map ((t.nonrootVertex M e) ∘ FKCRT.timeCell t.word.length ht)=_
  rw [← Measure.map_map (measurable_of_finite (t.nonrootVertex M e))
    (FKCRT.timeCell_measurable _ ht),FKCRT.timeCell_map]
  rw [Measure.map_finset_sum' (measurable_of_finite (t.nonrootVertex M e)).aemeasurable]
  simp only [Measure.map_smul _ (measurable_of_finite (t.nonrootVertex M e)).aemeasurable,
    Measure.map_dirac' (measurable_of_finite (t.nonrootVertex M e))]
  rw [← Finset.smul_sum,t.nonroot_dirac_eq M e hp]
  rw [FKCRT.degreeMass,← Finset.smul_sum]
  congr 1
  rw [hlen]
  norm_num

lemma realized_distance_of (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) (a b : t.Dart) :
    ((FKCRT.graph M Set.univ).dist (orbit (FKCRT.rotation M) (e a))
      (orbit (FKCRT.rotation M) (e b)):ℝ)=t.realDistance a b := by
  have hh := dartGraph_embedding_edist e e.injective hp he a b
  rw [FKCRT.dartGraph_eq_spanning] at hh
  change (FKCRT.graph M Set.univ).edist _ _=t.matching.distance a b at hh
  change (FKCRT.graph M Set.univ).edist (orbit (FKCRT.rotation M) (e a))
    (orbit (FKCRT.rotation M) (e b))=t.matching.distance a b at hh
  rw [t.distance_eq_nat a b] at hh
  have hr : (FKCRT.graph M Set.univ).Reachable
      (orbit (FKCRT.rotation M) (e a)) (orbit (FKCRT.rotation M) (e b)) := by
    apply SimpleGraph.edist_ne_top_iff_reachable.mp
    rw [hh]
    exact ENat.natCast_ne_top _
  rw [← SimpleGraph.Reachable.coe_dist_eq_edist hr] at hh
  dsimp only [realDistance]
  exact_mod_cast hh

/-- Direct measured common-coding comparison of the actual finite map with
any continuous excursion metric, with no unmeasured-GH substitution. -/
theorem ghp_from_time_distortion (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (hlen : t.word.length=2*(n+1)) (f : C(unitInterval,ℝ))
    {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε)
    (hd : ∀ s u,|scale*((FKCRT.graph M Set.univ).dist (t.timeVertex M e ht s)
        (t.timeVertex M e ht u):ℝ)-FKCRT.excursionDist f s u|≤2*ε) :
    FKCRT.ghpEDist (FKCRT.mapSpace scale M) (FKCRT.treeSpace f)≤ENNReal.ofReal ε := by
  apply FKCRT.ghpEDist_le_of_coding (FKCRT.mapSpace_valid hs M)
    (FKCRT.treeSpace_valid f.continuous) (volume : Measure unitInterval)
    (t.timeVertex M e ht) (FKCRT.treeProjection f)
    (t.timeVertex_measurable M e ht) (FKCRT.treeProjection_measurable f)
    (t.timeVertex_surjective M e ht hp) (FKCRT.treeProjection_surjective f)
    (t.timeVertex_mass M e ht hp hlen) rfl hε
  intro s u
  change |scale*((FKCRT.graph M Set.univ).dist _ _:ℝ)-
    FKCRT.excursionDist f (FKCRT.treeProjection f s).out (FKCRT.treeProjection f u).out|≤_
  rw [FKCRT.excursionDist_out f.continuous]
  exact hd s u

end FKCRT.Inventory.CoreTree
end


noncomputable section
open Set
namespace FKCRT
attribute [local instance] Classical.propDecidable

lemma cellPoint_interval_near (N : ℕ) (hN : 0<N) (s t : unitInterval) (hst : s ≤ t)
    (i : Fin N) (hsi : timeCell N hN s ≤  i) (hit : i ≤  timeCell N hN t) :
    ∃ u∈uIcc s t,dist (cellPoint N hN i) u ≤ 1/(N:ℝ) := by
  let p := cellPoint N hN i
  by_cases hs : p<s
  · refine ⟨s,left_mem_uIcc,?_⟩
    have hh := cellPoint_close N hN s
    have ho := cellPoint_mono N hN hsi
    change (cellPoint N hN (timeCell N hN s):ℝ) ≤ (p:ℝ) at ho
    rw [Subtype.dist_eq,Real.dist_eq] at hh ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr (show (p:ℝ) ≤ s from hs.le))]
    have hh' := (abs_le.mp hh).1
    linarith
  · by_cases ht : t<p
    · refine ⟨t,right_mem_uIcc,?_⟩
      have hh := cellPoint_close N hN t
      have ho := cellPoint_mono N hN hit
      change (p:ℝ) ≤ (cellPoint N hN (timeCell N hN t):ℝ) at ho
      rw [Subtype.dist_eq,Real.dist_eq] at hh ⊢
      rw [abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ p from ht.le))]
      have hh' := (abs_le.mp hh).2
      linarith
    · refine ⟨p,?_,?_⟩
      · rw [uIcc_of_le hst]
        exact ⟨le_of_not_gt hs,le_of_not_gt ht⟩
      · change dist p p ≤ _
        rw [dist_self]
        positivity

lemma sampled_minimum_error (N : ℕ) (hN : 0<N) (f : C(unitInterval,ℝ))
    {η : ℝ} (hmod : ∀ s t,dist s t ≤ 1/(N:ℝ) → |f s-f t| ≤ η)
    (s t : unitInterval) (hst : s ≤ t) (m : Fin N)
    (hsm : timeCell N hN s ≤  m) (hmt : m ≤  timeCell N hN t)
    (hm : ∀ i,timeCell N hN s ≤  i → i ≤  timeCell N hN t →
      f (cellPoint N hN m) ≤ f (cellPoint N hN i)) :
    |f (cellPoint N hN m)-sInf (f '' uIcc s t)| ≤ η := by
  obtain ⟨u,hu,hdu⟩ := cellPoint_interval_near N hN s t hst m hsm hmt
  have hi := csInf_le (interval_image_bddBelow f.continuous s t) (mem_image_of_mem f hu)
  have hmdu := abs_le.mp (hmod _ _ hdu)
  have hl : f (cellPoint N hN m)-η ≤ sInf (f '' uIcc s t) := by
    apply le_csInf (nonempty_uIcc.image f)
    rintro _ ⟨r,hr,rfl⟩
    rw [uIcc_of_le hst] at hr
    have hmr := hm (timeCell N hN r) (timeCell_mono N hN hr.1) (timeCell_mono N hN hr.2)
    have hclose := abs_le.mp (hmod _ _ (cellPoint_close N hN r))
    linarith
  apply abs_le.mpr
  constructor <;> linarith

/-- Discrete positive preorder samples and their exact equal-mass coding
approximate the continuous interval-minimum metric with its own modulus. -/
theorem sampled_excursion_error (N : ℕ) (hN : 0<N) (f : C(unitInterval,ℝ))
    {η : ℝ} (hmod : ∀ s t,dist s t ≤ 1/(N:ℝ) → |f s-f t| ≤ η)
    (s t : unitInterval) (hst : s ≤ t) (m : Fin N)
    (hsm : timeCell N hN s ≤  m) (hmt : m ≤  timeCell N hN t)
    (hm : ∀ i,timeCell N hN s ≤  i → i ≤  timeCell N hN t →
      f (cellPoint N hN m) ≤ f (cellPoint N hN i)) :
    |(f (cellPoint N hN (timeCell N hN s))+f (cellPoint N hN (timeCell N hN t))-
      2*f (cellPoint N hN m))-excursionDist f s t| ≤ 4*η := by
  have h₁ := abs_le.mp (hmod _ _ (cellPoint_close N hN s))
  have h₂ := abs_le.mp (hmod _ _ (cellPoint_close N hN t))
  have h₃ := abs_le.mp (sampled_minimum_error N hN f hmod s t hst m hsm hmt hm)
  dsimp only [excursionDist]
  apply abs_le.mpr
  constructor <;> linarith

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma wordNodeEquiv_val (t : CoreTree) (v : t.Node) : (t.wordNodeEquiv v).val=t.nodeIndex v := rfl
lemma nodeIndex_wordNodeEquiv_symm (t : CoreTree) (i : Fin (t.word.length+1)) :
    t.nodeIndex (t.wordNodeEquiv.symm i)=i.val := by
  exact congrArg Fin.val (t.wordNodeEquiv.apply_symm_apply i)

/-- Same-code positive mesh, with the omitted root still present at time zero. -/
def nodePoint (t : CoreTree) (v : t.Node) : unitInterval :=
  ⟨((t.wordNodeEquiv v).val:ℝ)/(t.word.length+1:ℝ),by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast (t.wordNodeEquiv v).isLt.le⟩

lemma nodePoint_nonroot (t : CoreTree) (ht : 0<t.word.length) (i : Fin t.word.length) :
    t.nodePoint (t.wordNodeEquiv.symm i.succ)=FKCRT.cellPoint t.word.length ht i := by
  apply Subtype.ext
  simp only [nodePoint,t.wordNodeEquiv.apply_symm_apply,Fin.val_succ,FKCRT.cellPoint,Nat.cast_add,Nat.cast_one]

lemma normalized_pole_comparison (t : CoreTree) (v w m : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b)
    (hm₁ : t.nodeIndex v ≤ t.nodeIndex m) (hm₂ : t.nodeIndex m ≤ t.nodeIndex w)
    (f : t.Node → ℝ) {scale ε : ℝ} (hs : 0<scale)
    (herr : ∀ u,|scale*(t.routeLength u:ℝ)-f u| ≤ ε)
    (hmin : ∀ u,t.nodeIndex v ≤ t.nodeIndex u → t.nodeIndex u ≤ t.nodeIndex w → f m ≤ f u) :
    |scale*t.realDistance a b-(f v+f w-2*f m)| ≤ 4*scale*(t.maxDegree:ℝ)+4*ε := by
  have he : ∀ u,|(t.routeLength u:ℝ)-(1/scale)*f u| ≤ ε/scale := by
    intro u
    have heq : (t.routeLength u:ℝ)-(1/scale)*f u=(scale*(t.routeLength u:ℝ)-f u)/scale := by
      field_simp
    rw [heq,abs_div,abs_of_pos hs]
    exact div_le_div_of_nonneg_right (herr u) hs.le
  have hh := t.pole_walk_comparison v w m a b ha hb hm₁ hm₂ f
    (α := 1/scale) (ε := ε/scale) (by positivity) he hmin
  calc
    |scale*t.realDistance a b-(f v+f w-2*f m)|=
        |scale*(t.realDistance a b-(1/scale)*(f v+f w-2*f m))| := by
      congr 1
      field_simp
    _=scale*|t.realDistance a b-(1/scale)*(f v+f w-2*f m)| := by rw [abs_mul,abs_of_pos hs]
    _ ≤ scale*(4*(t.maxDegree:ℝ)+4*(ε/scale)) := mul_le_mul_of_nonneg_left hh hs.le
    _=4*scale*(t.maxDegree:ℝ)+4*ε := by field_simp

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma exists_positive_index (t : CoreTree) (v : t.Node) (hv : 0<t.nodeIndex v) :
    ∃ i : Fin t.word.length,t.wordNodeEquiv.symm i.succ=v := by
  have hb := (t.wordNodeEquiv v).isLt
  rw [wordNodeEquiv_val] at hb
  let i : Fin t.word.length := ⟨t.nodeIndex v-1,by omega⟩
  refine ⟨i,t.wordNodeEquiv.symm_apply_eq.mpr ?_⟩
  apply Fin.ext
  change t.nodeIndex v-1+1=t.nodeIndex v
  omega

lemma time_distortion_ordered (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : C(unitInterval,ℝ)) {scale ε η : ℝ} (hs : 0<scale)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (s u : unitInterval) (hsu : s ≤ u) :
    |scale*((FKCRT.graph M Set.univ).dist (t.timeVertex M e ht s)
      (t.timeVertex M e ht u):ℝ)-FKCRT.excursionDist f s u| ≤
        4*scale*(t.maxDegree:ℝ)+4*ε+4*η := by
  let i := FKCRT.timeCell t.word.length ht s
  let j := FKCRT.timeCell t.word.length ht u
  have hij : i ≤ j := FKCRT.timeCell_mono _ ht hsu
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image (Finset.Icc i j)
    (fun k => f (FKCRT.cellPoint t.word.length ht k)) ⟨i,Finset.mem_Icc.mpr ⟨le_rfl,hij⟩⟩
  have hki := (Finset.mem_Icc.mp hk).1
  have hkj := (Finset.mem_Icc.mp hk).2
  let v := t.wordNodeEquiv.symm i.succ
  let w := t.wordNodeEquiv.symm j.succ
  let m := t.wordNodeEquiv.symm k.succ
  have hv : t.nodeIndex v=i.val+1 := t.nodeIndex_wordNodeEquiv_symm i.succ
  have hw : t.nodeIndex w=j.val+1 := t.nodeIndex_wordNodeEquiv_symm j.succ
  have hm : t.nodeIndex m=k.val+1 := t.nodeIndex_wordNodeEquiv_symm k.succ
  have hvm : t.nodeIndex v ≤ t.nodeIndex m := by rw [hv,hm];omega
  have hmw : t.nodeIndex m ≤ t.nodeIndex w := by rw [hm,hw];omega
  have hn : t≠leaf := by intro h;subst t;simp [word] at ht
  obtain ⟨a,ha⟩ := t.pole_some_of_ne_leaf hn v
  obtain ⟨b,hb⟩ := t.pole_some_of_ne_leaf hn w
  have hm' : ∀ z,t.nodeIndex v ≤ t.nodeIndex z → t.nodeIndex z ≤ t.nodeIndex w →
      f (t.nodePoint m) ≤ f (t.nodePoint z) := by
    intro z hz₁ hz₂
    obtain ⟨r,hr⟩ := t.exists_positive_index z (by omega)
    subst z
    rw [t.nodePoint_nonroot ht k,t.nodePoint_nonroot ht r]
    apply hmin r
    rw [Finset.mem_Icc]
    simp only [v,w,t.nodeIndex_wordNodeEquiv_symm,Fin.val_succ] at hz₁ hz₂
    constructor <;> omega
  have hd := t.normalized_pole_comparison v w m a b ha hb hvm hmw
    (fun z => f (t.nodePoint z)) hs herr hm'
  have hgrid := FKCRT.sampled_excursion_error t.word.length ht f hmod s u hsu k hki hkj
    (fun r hr₁ hr₂ => hmin r (Finset.mem_Icc.mpr ⟨hr₁,hr₂⟩))
  have hvp : t.nodePoint v=FKCRT.cellPoint t.word.length ht i := t.nodePoint_nonroot ht i
  have hwp : t.nodePoint w=FKCRT.cellPoint t.word.length ht j := t.nodePoint_nonroot ht j
  have hmp : t.nodePoint m=FKCRT.cellPoint t.word.length ht k := t.nodePoint_nonroot ht k
  simp only [hvp,hwp,hmp] at hd
  change |scale*((FKCRT.graph M Set.univ).dist (t.realizedPole M e v)
    (t.realizedPole M e w):ℝ)-FKCRT.excursionDist f s u| ≤ _
  rw [t.realizedPole_some M e v a ha,t.realizedPole_some M e w b hb,
    t.realized_distance_of M e he hp a b]
  exact (abs_sub_le _ _ _).trans (add_le_add hd hgrid)

/-- Uniform measured-space distortion from actual marked ancestral error,
actual largest core, and the modulus of the chosen continuous path. -/
theorem time_distortion (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : C(unitInterval,ℝ)) {scale ε η : ℝ} (hs : 0<scale)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (s u : unitInterval) :
    |scale*((FKCRT.graph M Set.univ).dist (t.timeVertex M e ht s)
      (t.timeVertex M e ht u):ℝ)-FKCRT.excursionDist f s u| ≤
        4*scale*(t.maxDegree:ℝ)+4*ε+4*η := by
  rcases le_total s u with h | h
  · exact t.time_distortion_ordered M e ht he hp f hs herr hmod s u h
  · rw [SimpleGraph.dist_comm,FKCRT.excursionDist_comm]
    exact t.time_distortion_ordered M e ht he hp f hs herr hmod u s h

/-- The measured comparison is oriented from the fixed continuous-tree
space, precisely as required in the continuity tests. -/
theorem ghp_tree_map_bound (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length)
    (he : ∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d))
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (hlen : t.word.length=2*(n+1)) (f : C(unitInterval,ℝ))
    {scale ε η δ : ℝ} (hs : 0<scale) (hδ : 0<δ)
    (herr : ∀ v,|scale*(t.routeLength v:ℝ)-f (t.nodePoint v)| ≤ ε)
    (hmod : ∀ s u,dist s u ≤ 1/(t.word.length:ℝ) → |f s-f u| ≤ η)
    (hsmall : 4*scale*(t.maxDegree:ℝ)+4*ε+4*η ≤ 2*δ) :
    FKCRT.ghpEDist (FKCRT.treeSpace f) (FKCRT.mapSpace scale M) ≤ ENNReal.ofReal δ := by
  apply FKCRT.ghpEDist_le_of_coding (FKCRT.treeSpace_valid f.continuous)
    (FKCRT.mapSpace_valid hs M) (volume : Measure unitInterval)
    (FKCRT.treeProjection f) (t.timeVertex M e ht)
    (FKCRT.treeProjection_measurable f) (t.timeVertex_measurable M e ht)
    (FKCRT.treeProjection_surjective f) (t.timeVertex_surjective M e ht hp)
    rfl (t.timeVertex_mass M e ht hp hlen) hδ
  intro s u
  change |FKCRT.excursionDist f (FKCRT.treeProjection f s).out (FKCRT.treeProjection f u).out-
    scale*((FKCRT.graph M Set.univ).dist _ _:ℝ)| ≤ _
  rw [FKCRT.excursionDist_out f.continuous,abs_sub_comm]
  exact (t.time_distortion M e ht he hp f hs herr hmod s u).trans hsmall

end FKCRT.Inventory.CoreTree
end

end OAI
