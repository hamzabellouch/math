import OAI.Combinatorics.HalvingLines.BoundaryTokens

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Boundary
open scoped Topology unitInterval

lemma isOpenMap_encode : IsOpenMap encode := by
  have h : IsOpenMap unitInterval.sigmoid :=
    Topology.isEmbedding_sigmoid.isInducing.isOpenMap (by rw [unitInterval.range_sigmoid]; exact isOpen_Ioo)
  exact h.prodMap h

lemma isOpen_square (a b : ℝ) : IsOpen {x : Point | InSquare a b x} := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)))

lemma continuous_dot (ν : Point) : Continuous (dot ν) := by
  exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

noncomputable def awayStrips (t θ : ℝ) (c : Fin 3 → ℝ) : Set Point :=
  {x | InSquare (-2) 2 x ∧ ∀ j, 18*θ < |dot (rawNormal t) x-c j|}

lemma isOpen_awayStrips (t θ : ℝ) (c : Fin 3 → ℝ) : IsOpen (awayStrips t θ c) := by
  have he : awayStrips t θ c={x : Point | InSquare (-2) 2 x} ∩ ⋂ j : Fin 3, {x | 18*θ < |dot (rawNormal t) x-c j|} := by
    ext x; simp [awayStrips]
  rw [he]
  apply (isOpen_square (-2) 2).inter
  exact isOpen_iInter_of_finite (fun j : Fin 3 => isOpen_lt continuous_const ((continuous_dot _).sub continuous_const).abs)

lemma awayStrips_stable {ts θs : ℕ → ℝ} {cs : ℕ → Fin 3 → ℝ}
    {t θ : ℝ} {c : Fin 3 → ℝ}
    (ht : Tendsto ts atTop (𝓝 t)) (hθ : Tendsto θs atTop (𝓝 θ))
    (hc : Tendsto cs atTop (𝓝 c)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop, awayStrips t (θ+ε) c ⊆ awayStrips (ts n) (θs n) (cs n) := by
  have ht' := (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr ht).abs)).2 ε (by simpa using hε)
  have hθ' := (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr hθ).abs)).2 (ε/2) (by simpa using half_pos hε)
  have hc' : ∀ᶠ n in atTop, ∀ j, |cs n j-c j|<ε := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr (tendsto_pi_nhds.mp hc j)).abs)).2 ε (by simpa using hε)
  filter_upwards [ht',hθ',hc'] with n hn hnθ hnc x hx
  refine ⟨hx.1,fun j => ?_⟩
  have h1 : |x.1|≤2 := abs_le.mpr ⟨hx.1.1.le,hx.1.2.1.le⟩
  have h2 : |x.2|≤2 := abs_le.mpr ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩
  have hdiff : |dot (rawNormal (ts n)) x-dot (rawNormal t) x|≤4*|ts n-t| := by
    have he : dot (rawNormal (ts n)) x-dot (rawNormal t) x=-(ts n-t)*(x.1+x.2) := by dsimp [dot,rawNormal]; ring
    rw [he,abs_mul,abs_neg]
    have hh : |x.1+x.2|≤4 := (abs_add_le _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (ts n-t))]
  have htotal : |(dot (rawNormal (ts n)) x-cs n j)-(dot (rawNormal t) x-c j)|<5*ε := by
    have he : (dot (rawNormal (ts n)) x-cs n j)-(dot (rawNormal t) x-c j)=
        (dot (rawNormal (ts n)) x-dot (rawNormal t) x)-(cs n j-c j) := by ring
    rw [he]
    have hh := abs_sub (dot (rawNormal (ts n)) x-dot (rawNormal t) x) (cs n j-c j)
    have hncj := hnc j
    linarith
  have hh := abs_abs_sub_abs_le_abs_sub (dot (rawNormal (ts n)) x-cs n j) (dot (rawNormal t) x-c j)
  have hh' := (abs_le.mp hh).1
  have hlow := hx.2 j
  have hup := (abs_lt.mp hnθ).2
  linarith

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Boundary Limits
open scoped Topology unitInterval ENNReal

lemma awayStrips_antitone (t : ℝ) (c : Fin 3 → ℝ) : Antitone (fun θ => awayStrips t θ c) := by
  intro θ θ' hθ x hx
  exact ⟨hx.1,fun j => (mul_le_mul_of_nonneg_left hθ (by norm_num)).trans_lt (hx.2 j)⟩

lemma awayStrips_iUnion (t θ : ℝ) (c : Fin 3 → ℝ) :
    (⋃ m : ℕ, awayStrips t (θ+1/((m:ℝ)+1)) c)=awayStrips t θ c := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    exact awayStrips_antitone t c (le_add_of_nonneg_right (by positivity)) hm
  · intro x hx
    have hh : ∀ᶠ m : ℕ in atTop, ∀ j, 18*(θ+1/((m:ℝ)+1)) < |dot (rawNormal t) x-c j| := by
      apply Filter.eventually_all.mpr
      intro j
      have hl : Tendsto (fun m : ℕ => 18*(θ+1/((m:ℝ)+1))) atTop (𝓝 (18*θ)) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_add θ |>.const_mul 18
      exact hl.eventually (eventually_lt_nhds (hx.2 j))
    obtain ⟨m,hm⟩ := hh.exists
    exact mem_iUnion.mpr ⟨m,hx.1,hm⟩

lemma moving_strips_limit {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {ts θs bs : ℕ → ℝ} {cs : ℕ → Fin 3 → ℝ} {t θ b : ℝ} {c : Fin 3 → ℝ}
    (ht : Tendsto ts atTop (𝓝 t)) (hθ : Tendsto θs atTop (𝓝 θ))
    (hc : Tendsto cs atTop (𝓝 c)) (hb : Tendsto bs atTop (𝓝 b))
    (hfinite : ∀ᶠ n in atTop,
      (μs n (Prod.snd ⁻¹' (encode '' awayStrips (ts n) (θs n) (cs n))):ℝ) ≤ 2*bs n) :
    (μ (Prod.snd ⁻¹' (encode '' awayStrips t θ c)):ℝ) ≤ 2*b := by
  let O (m : ℕ) : Set (X × Cube) := Prod.snd ⁻¹' (encode '' awayStrips t (θ+1/((m:ℝ)+1)) c)
  have hO (m : ℕ) : IsOpen (O m) :=
    (isOpenMap_encode _ (isOpen_awayStrips ..)).preimage continuous_snd
  have hbound (m : ℕ) : (μ (O m):ℝ) ≤ 2*b := by
    apply open_le_of_eventually_le hμ (hO m) (hb.const_mul 2)
    have he := awayStrips_stable ht hθ hc (show 0<1/((m:ℝ)+1) by positivity)
    filter_upwards [he,hfinite] with n hn hnf
    exact (show (μs n (O m):ℝ) ≤ μs n (Prod.snd ⁻¹' (encode '' awayStrips (ts n) (θs n) (cs n))) from
      NNReal.coe_le_coe.mpr ((μs n).apply_mono (preimage_mono (image_mono hn)))).trans hnf
  have hmono : Monotone O := by
    intro m n hmn
    apply preimage_mono
    apply image_mono
    apply awayStrips_antitone
    have hm : (0:ℝ) < m+1 := by positivity
    have hn : (0:ℝ) < n+1 := by positivity
    have hmn' : (m:ℝ)+1 ≤ n+1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact add_le_add_right ((one_div_le_one_div hn hm).mpr hmn') θ
  have hunion : (⋃ m, O m)=Prod.snd ⁻¹' (encode '' awayStrips t θ c) := by
    rw [← awayStrips_iUnion t θ c,image_iUnion,preimage_iUnion]
  have hbound' (m : ℕ) : (μ : Measure (X × Cube)) (O m) ≤ ENNReal.ofReal (2*b) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hbound m)
  have he : (μ : Measure (X × Cube)) (Prod.snd ⁻¹' (encode '' awayStrips t θ c)) ≤ ENNReal.ofReal (2*b) := by
    rw [← hunion,hmono.measure_iUnion]
    exact iSup_le hbound'
  have hb0 : 0≤2*b := (NNReal.coe_nonneg (μ (O 0))).trans (hbound 0)
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal] at he
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp he

end PlanarHalving.Spatial
namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory Boundary Limits
open scoped Topology unitInterval ENNReal

lemma limiting_activity_bound {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : FiniteMeasure (X × Cube)) (H : Set (X × Cube)) (_hH : MeasurableSet H)
    (hν : (ν : Measure (X × Cube))≤μ)
    (hpos : ∀ z∈H, ‖decode z.2‖≤1 ∧ encode (decode z.2)=z.2)
    {C d t θ b : ℝ} (hC : 0≤C) (hd : 1<d) (hθ : 0≤θ) (hb : 0≤b)
    (c : Fin 3 → ℝ)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r →
      ((μ : Measure (X × Cube)).restrict H).map (decode ∘ Prod.snd) (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (haway : (ν (Prod.snd ⁻¹' (encode '' awayStrips t θ c)):ℝ)≤2*b) :
    (ν H:ℝ)≤2*b+3*(13*C*(1+3^d)*36^(d-1))*θ^(d-1) := by
  let ψ : X × Cube → Point := decode ∘ Prod.snd
  let β := ((μ : Measure (X × Cube)).restrict H).map ψ
  let D : Fin 3 → Set Point := fun j => closedBall (0:Point) 1 ∩ {x | |dot (rawNormal t) x-c j|≤18*θ}
  let A : Fin 3 → Set (X × Cube) := fun j => ψ ⁻¹' D j ∩ H
  let O : Set (X × Cube) := Prod.snd ⁻¹' (encode '' awayStrips t θ c)
  have hD (j : Fin 3) : MeasurableSet (D j) := measurableSet_closedBall.inter
    (isClosed_le (((continuous_dot _).sub continuous_const).abs) continuous_const).measurableSet
  have hψ : Measurable ψ := measurable_decode.comp measurable_snd
  have hsub : H ⊆ O ∪ ⋃ j : Fin 3, A j := by
    intro z hz
    have hp := hpos z hz
    by_cases hstrip : ∃ j, |dot (rawNormal t) (ψ z)-c j|≤18*θ
    · obtain ⟨j,hj⟩ := hstrip
      refine Or.inr (mem_iUnion.mpr ⟨j,⟨?_,hj⟩,hz⟩)
      simpa only [mem_closedBall,dist_zero_right,ψ,Function.comp_apply] using hp.1
    · apply Or.inl
      refine ⟨ψ z,⟨?_,fun j => lt_of_not_ge (fun hj => hstrip ⟨j,hj⟩)⟩,hp.2⟩
      have hx := (norm_fst_le (ψ z)).trans hp.1
      have hy := (norm_snd_le (ψ z)).trans hp.1
      rw [Real.norm_eq_abs] at hx hy
      have hx' := abs_le.mp hx
      have hy' := abs_le.mp hy
      change -2<(ψ z).1 ∧ (ψ z).1<2 ∧ -2<(ψ z).2 ∧ (ψ z).2<2
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
  have hA (j : Fin 3) : (μ : Measure (X × Cube)) (A j)=β (D j) := by
    rw [Measure.map_apply hψ (hD j),Measure.restrict_apply ((hD j).preimage hψ)]
  have hstrip (j : Fin 3) : (ν : Measure (X × Cube)) (A j)≤
      ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
    exact (hν (A j)).trans ((hA j) ▸ raw_strip_bound β hC hd hbound t (c j) hθ)
  have haway' : (ν : Measure (X × Cube)) O≤ENNReal.ofReal (2*b) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal haway
  have htotal : (ν : Measure (X × Cube)) H≤
      ENNReal.ofReal (2*b+3*(13*C*(1+3^d)*36^(d-1))*θ^(d-1)) := by
    calc
      _ ≤ (ν : Measure (X × Cube)) (O ∪ ⋃ j : Fin 3, A j) := measure_mono hsub
      _ ≤ (ν : Measure (X × Cube)) O + (ν : Measure (X × Cube)) (⋃ j : Fin 3, A j) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2*b)+∑ j : Fin 3, ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
        apply add_le_add haway'
        exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum (fun j _ => hstrip j))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast 3,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htotal

end PlanarHalving.Spatial

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def batchRange (R s m : ℕ) : Finset (Fin R) :=
  Finset.univ.filter fun i => s ≤ i.val ∧ i.val < s+m

lemma sum_batchRange {M : Type*} [AddCommMonoid M] {R s m : ℕ} (h : s+m≤R) (w : Fin R → M) :
    ∑ i∈batchRange R s m, w i=∑ i : Fin m, w ⟨s+i.val,by omega⟩ := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => (⟨s+i.val,by omega⟩ : Fin R))
  · intro i _
    simp only [batchRange,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor <;> omega
  · intro i _ j _ hij
    have hh := congrArg Fin.val hij
    apply Fin.ext
    simpa using hh
  · intro i hi
    obtain ⟨hil,hir⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-s,by omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    simp only
    omega
  · intro i _; rfl

lemma sum_disjoint_ranges {ι : Type*} (F : Finset ι) {R : ℕ} (s m : ι → ℕ)
    (hd : Set.PairwiseDisjoint (↑F:Set ι) (fun j => batchRange R (s j) (m j)))
    (w : Fin R → ℝ) (hw : ∀ i, 0≤w i) :
    ∑ j∈F, ∑ i∈batchRange R (s j) (m j), w i ≤ ∑ i : Fin R, w i := by
  classical
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)

lemma parameter_telescope {R : ℕ} (t : Fin (R+1) → ℝ) :
    ∑ i : Fin R, (t i.succ-t i.castSucc)=t (Fin.last R)-t 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ t
  have h₂ := Fin.sum_univ_castSucc t
  linarith

lemma parameter_range_sum {R s m : ℕ} (h : s+m≤R) (t : Fin (R+1) → ℝ) :
    ∑ i∈batchRange R s m, (t i.succ-t i.castSucc)=
      t ⟨s+m,by omega⟩-t ⟨s,by omega⟩ := by
  rw [sum_batchRange h]
  convert parameter_telescope (fun i : Fin (m+1) => t ⟨s+i.val,by omega⟩) using 1 <;> simp [Nat.add_assoc]

lemma parameter_budget {ι : Type*} (F : Finset ι) {R : ℕ} (s m : ι → ℕ)
    (hd : Set.PairwiseDisjoint (↑F:Set ι) (fun j => batchRange R (s j) (m j)))
    (t : Fin (R+1) → ℝ) (ht : Monotone t) (htI : ∀ i,t i∈Icc (0:ℝ) 1) :
    ∑ j∈F, ∑ i∈batchRange R (s j) (m j), (t i.succ-t i.castSucc) ≤ 1 := by
  have hh := sum_disjoint_ranges F s m hd (fun i => t i.succ-t i.castSucc)
    (fun i => sub_nonneg.mpr (ht (by simp [Fin.le_def])))
  rw [parameter_telescope] at hh
  have hlo := (htI 0).1
  have hhi := (htI (Fin.last R)).2
  linarith

end PlanarHalving.Boundary

namespace PlanarHalving.TimeWindows
open Set

lemma cuts_of_subset (R : ℕ) [NeZero R] {J K : Window} (h : carrier J⊆carrier K) :
    start R K ≤ start R J ∧ stop R J ≤ stop R K := by
  obtain ⟨hl,hu⟩ := endpoints_of_subset h
  exact ⟨cut_mono _ hl,cut_mono _ hu⟩

lemma relative_end_le (R : ℕ) [NeZero R] {J K : Window} (h : carrier J⊆carrier K) :
    start R J-start R K+length R J≤length R K := by
  have hcut := cuts_of_subset R h
  have hJ := start_add_length R J
  have hK := start_add_length R K
  omega

end PlanarHalving.TimeWindows
namespace PlanarHalving.Batches
open Set TimeWindows
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_eq_of_marks (S T : @System n R k a P) (h : S.marks=T.marks) :
    S.vertices=T.vertices := by
  classical
  unfold System.vertices System.edges System.loss System.gain
  rw [h]

lemma System.relative_vertices (S : @System n R k a P) [NeZero R]
    {K J : Window} (h : carrier J⊆carrier K) :
    ((S.timeWindow K).window (start R J-start R K) (length R J) (relative_end_le R h)).vertices=
      (S.timeWindow J).vertices := by
  apply System.vertices_eq_of_marks
  funext i
  dsimp [System.timeWindow,System.window]
  congr 1
  apply Fin.ext
  simp only
  have hc := (cuts_of_subset R h).1
  omega

end PlanarHalving.Batches

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology unitInterval PiCountable

abbrev CompactParams := Icc (0:ℝ) 4 × I × I × (Fin 3 → Icc (-4:ℝ) 4)

lemma params_subsequence {J : Type*} [Countable J] (p : ℕ → J → CompactParams) :
    ∃ (φ : ℕ → ℕ) (b t θ : J → ℝ) (c : J → Fin 3 → ℝ), StrictMono φ ∧
      (∀ j, b j∈Icc (0:ℝ) 4 ∧ t j∈Icc (0:ℝ) 1 ∧ θ j∈Icc (0:ℝ) 1 ∧
        ∀ i, c j i∈Icc (-4:ℝ) 4) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).1.val) atTop (𝓝 (b j))) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).2.1.val) atTop (𝓝 (t j))) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).2.2.1.val) atTop (𝓝 (θ j))) ∧
      (∀ j, Tendsto (fun n i => ((p (φ n) j).2.2.2 i).val) atTop (𝓝 (c j))) := by
  obtain ⟨q,φ,hφ,hq⟩ := CompactSpace.tendsto_subseq p
  refine ⟨φ,fun j => (q j).1.val,fun j => (q j).2.1.val,fun j => (q j).2.2.1.val,
    fun j i => ((q j).2.2.2 i).val,hφ,?_,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(q j).1.property,(q j).2.1.property,(q j).2.2.1.property,
      fun i => ((q j).2.2.2 i).property⟩
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).fst_nhds
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).snd_nhds.fst_nhds
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).snd_nhds.snd_nhds.fst_nhds
  · intro j
    apply tendsto_pi_nhds.mpr
    intro i
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hq j).snd_nhds.snd_nhds.snd_nhds i)

lemma finite_budget_limit {J : Type*} (F : Finset J) (f : ℕ → J → ℝ) (g : J → ℝ) {B : ℝ}
    (h : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j)))
    (hf : ∀ᶠ n in atTop, ∑ j∈F, f n j ≤ B) : ∑ j∈F, g j≤B := by
  apply le_of_tendsto (tendsto_finsetSum F (fun j _ => h j)) hf

end PlanarHalving.Boundary

namespace PlanarHalving.Batches
open Set Boundary
open scoped Classical
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_changes (S : @System n R k a P) {v : Fin n} (hv : v∈S.vertices) :
    ∃ i j : Fin (R+1), ¬(v∈S.marks i ↔ v∈S.marks j) := by
  classical
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,hb,_⟩ := (S.mem_edges e).mp he
    obtain ⟨hl,hr⟩ := Finset.mem_sdiff.mp hb
    exact ⟨b.castSucc,b.succ,fun h => hr (h.mp hl)⟩
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,_,hb⟩ := (S.mem_edges e).mp he
    obtain ⟨hl,hr⟩ := Finset.mem_sdiff.mp hb
    exact ⟨b.castSucc,b.succ,fun h => hr (h.mpr hl)⟩

lemma System.tokenState_image (S : @System n R k a P) [NeZero a]
    (j : Fin a) (i : Fin (R+1)) :
    Finset.univ.image (fun u : ↥(S.marks 0) => (S.tokenState j i u : Fin n))=S.marks i := by
  classical
  ext v
  constructor
  · rintro hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    exact (S.tokenState j i u).property
  · intro hv
    exact Finset.mem_image.mpr ⟨(S.tokenState j i).symm ⟨v,hv⟩,Finset.mem_univ _,
      congrArg Subtype.val ((S.tokenState j i).apply_symm_apply _)⟩

noncomputable def System.boundaryCount (S : @System n R k a P) [NeZero a]
    (p : Fin n → Point) (j : Fin a) (i : Fin R) : ℕ :=
  (Finset.univ.filter fun u : ↥(S.marks 0) =>
    ¬(InSquare (-2) 2 (p (S.tokenState j i.castSucc u)) ↔
      InSquare (-2) 2 (p (S.tokenState j i.succ u)))).card

lemma System.boundary_budget (S : @System n R k a P) [NeZero a]
    (p : Fin n → Point) (j : Fin a)
    (h1 : ∀ u, Monotone (fun i => (p (S.tokenState j i u)).1))
    (h2 : ∀ u, Monotone (fun i => (p (S.tokenState j i u)).2)) :
    ∑ i : Fin R, S.boundaryCount p j i ≤ 4*n := by
  have hh := square_token_budget (fun i u => p (S.tokenState j i u)) h1 h2 (-2) 2
  apply hh.trans
  rw [Fintype.card_coe]
  exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ (S.marks 0))

lemma System.window_boundary (S : @System n R k a P) [NeZero a]
    (E : Point ≃L[ℝ] Point) {A B l u : ℝ} (hA : 0<A) (hB : 0<B) (hlu : l<u)
    (h1 : E (1,0)=A • (1,l)) (h2 : E (0,1)=B • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r)
    (j : Fin a) (s m : ℕ) (hsm : s+m ≤ R) :
    let T := fun i : Fin (R+1) => frameParameter A B l u (S.slope i)
    let i₀ : Fin (R+1) := ⟨s,by omega⟩
    let i₁ : Fin (R+1) := ⟨s+m,by omega⟩
    ∃ c : Fin 3 → ℝ, (∀ h, c h∈Icc (-4:ℝ) 4) ∧
      (((S.window s m hsm).vertices.filter fun v =>
        InSquare (-2) 2 (physical E o r (P v)) ∧
          ∀ h, 18*(T i₁-T i₀) < |dot (rawNormal (T i₀)) (physical E o r (P v))-c h|).card) ≤
        2*∑ i : Fin m, S.boundaryCount (fun v => physical E o r (P v)) j ⟨s+i.val,by omega⟩ := by
  classical
  dsimp only
  obtain ⟨c,hc⟩ := actual_transformed_cuts S E hA hB hlu h1 h2 hspan o hr
  let idx : Fin (m+1) → Fin (R+1) := fun i => ⟨s+i.val,by omega⟩
  let f : Fin (m+1) → ↥(S.marks 0) → Fin n := fun i t => S.tokenState j (idx i) t
  have hf : ∀ i, Function.Injective (f i) := fun i => Subtype.val_injective.comp (S.tokenState j (idx i)).injective
  have himg (i : Fin (m+1)) (v : Fin n) : v∈Finset.univ.image (f i) ↔ v∈S.marks (idx i) := by
    constructor
    · intro hv
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
      exact (S.tokenState j (idx i) u).property
    · intro hv
      exact Finset.mem_image.mpr ⟨(S.tokenState j (idx i)).symm ⟨v,hv⟩,Finset.mem_univ _,
        congrArg Subtype.val ((S.tokenState j (idx i)).apply_symm_apply _)⟩
  have ht : Monotone (fun i : Fin (m+1) => frameParameter A B l u (S.slope (idx i))) := by
    intro v w hvw
    apply frameParameter_monotone hA hB hlu (hspan _) (hspan _)
    apply S.increasing.monotone
    simp only [idx,Fin.le_def]
    exact Nat.add_le_add_left hvw s
  have htI (i : Fin (m+1)) : frameParameter A B l u (S.slope (idx i))∈Icc (0:ℝ) 1 :=
    frameParameter_mem hA hB hlu (hspan _)
  have hh := finite_raw_bound (fun v => physical E o r (P v)) f hf
    (S.window s m hsm).vertices (fun i => frameParameter A B l u (S.slope (idx i))) (fun i => c (idx i)) ht htI
    (by
      intro i v
      simpa only [Finset.mem_image,Finset.mem_univ,true_and] using (himg i v).trans (hc (idx i) v))
    (by
      intro v hv
      obtain ⟨i,j,hij⟩ := (S.window s m hsm).vertices_changes hv
      refine ⟨i,j,?_⟩
      intro he
      apply hij
      have hi := himg i v
      have hj := himg j v
      simp only [Finset.mem_image,Finset.mem_univ,true_and] at he hi hj
      exact hi.symm.trans (he.trans hj))
  obtain ⟨d,hd,hbound⟩ := hh
  refine ⟨d,hd,?_⟩
  have hsum : (∑ i : Fin m, (Finset.univ.filter fun u : ↥(S.marks 0) =>
      ¬(InSquare (-2) 2 (physical E o r (P (f i.castSucc u))) ↔
        InSquare (-2) 2 (physical E o r (P (f i.succ u))))).card)=
      ∑ i : Fin m, S.boundaryCount (fun v => physical E o r (P v)) j ⟨s+i.val,by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [hsum] at hbound
  convert hbound using 1; congr 1

end PlanarHalving.Batches

namespace PlanarHalving.TimeWindows
open Set Boundary
open scoped Classical
abbrev Subwindow (K : Window) := {J : Window // carrier J ⊆ carrier K}

lemma relative_range_disjoint (R : ℕ) [NeZero R] {K : Window} (J H : Subwindow K)
    (h : Disjoint (carrier J.val) (carrier H.val)) :
    Disjoint (batchRange (length R K) (start R J.val-start R K) (length R J.val))
      (batchRange (length R K) (start R H.val-start R K) (length R H.val)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hJ := (cuts_of_subset R J.property).1
  have hH := (cuts_of_subset R H.property).1
  have hK := start_add_length R K
  have hK' := stop_le R K
  have heJ := start_add_length R J.val
  have heH := start_add_length R H.val
  let b : Fin R := ⟨start R K+i.val,by omega⟩
  have hbJ : time R b∈carrier J.val := by
    apply (mem_carrier_iff R J.val b).mpr
    dsimp [b]
    constructor <;> omega
  have hbH : time R b∈carrier H.val := by
    apply (mem_carrier_iff R H.val b).mpr
    dsimp [b]
    constructor <;> omega
  exact Set.disjoint_left.mp h hbJ hbH

end PlanarHalving.TimeWindows

end OAI
