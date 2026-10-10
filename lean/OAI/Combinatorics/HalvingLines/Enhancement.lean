import OAI.Combinatorics.HalvingLines.MassEstimates

namespace OAI

open Filter Topology

namespace PlanarHalving.Enhancement
open RankLimits Batches TimeWindows Limits Spatial MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

abbrev Space := Labels × Cube
noncomputable def label (F : Configuration) (ψ : Point → Point) (p : Point) : Space :=
  (F.label p,encode (ψ p))
noncomputable def points (F : Configuration) (ψ : Point → Point) : FiniteMeasure Space :=
  weightedAtoms (F.n:ℝ≥0)⁻¹ (fun v => label F ψ (F.point v))
noncomputable def vertices (F : Configuration) (ψ : Point → Point) (J : Window) : FiniteMeasure Space :=
  (F.system.timeWindow J).vertexMeasure (fun v => label F ψ (F.point v))
noncomputable def edges (F : Configuration) (ψ : Point → Point) (J : Window) : FiniteMeasure Space :=
  (F.system.timeWindow J).endpointMeasure (fun v => label F ψ (F.point v)) ((F.R:ℝ≥0)*F.a^2)

lemma points_map (F : Configuration) (ψ : Point → Point) : (points F ψ).map Prod.fst=F.points := by
  rw [points,map_weightedAtoms _ _ measurable_fst]
  rfl
lemma vertices_map (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J).map Prod.fst=F.vertices J := by
  rw [vertices,System.vertexMeasure,map_weightedAtoms _ _ measurable_fst]
  rfl
lemma edges_map (F : Configuration) (ψ : Point → Point) (J : Window) :
    (edges F ψ J).map Prod.fst=F.edgeWindow J := by
  rw [F.edgeWindow_eq,edges,System.endpointMeasure,map_weightedAtoms _ _ measurable_fst]
  rfl

lemma points_mass (F : Configuration) (ψ : Point → Point) : (points F ψ).mass=1 := by
  rw [points,mass_weightedAtoms,Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne F.n))
lemma vertices_mass (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J).mass=(F.vertices J).mass := by
  simp only [vertices,Configuration.vertices,System.vertexMeasure,mass_weightedAtoms]
lemma edges_mass (F : Configuration) (ψ : Point → Point) (J : Window) :
    (edges F ψ J).mass=(F.edgeWindow J).mass := by
  rw [F.edgeWindow_eq,edges]
  simp only [System.endpointMeasure,mass_weightedAtoms]

inductive Index where
  | point
  | vertex (J : Window)
  | edge (J : Window)
  deriving Countable

noncomputable def measures (F : Configuration) (ψ : Point → Point) : Index → FiniteMeasure Space
  | .point => points F ψ
  | .vertex J => vertices F ψ J
  | .edge J => edges F ψ J
noncomputable def old (L : Data) : Index → FiniteMeasure Labels
  | .point => L.points
  | .vertex J => L.vertices J
  | .edge J => L.edgeWindow J

lemma measures_mass_le (F : Configuration) (ψ : Point → Point) (i : Index) :
    (measures F ψ i).mass≤1 := by
  cases i with
  | point => exact (points_mass F ψ).le
  | vertex J => exact (vertices_mass F ψ J).le.trans (F.vertices_mass_le J)
  | edge J =>
    change (edges F ψ J).mass≤1
    rw [edges_mass]
    exact (FiniteMeasure.mass_map_le (μ := F.timeRestrict J)
      measurable_fst.aemeasurable).trans (F.timeRestrict_mass_le J)

theorem subsequence {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (ψ : ℕ → Point → Point) :
    ∃ (φ : ℕ → ℕ) (M : Index → FiniteMeasure Space), StrictMono φ ∧
      (∀ i, Tendsto (fun n => measures (F (φ n)) (ψ (φ n)) i) atTop (𝓝 (M i))) ∧
      ∀ i, (M i).map Prod.fst=old L i := by
  obtain ⟨φ,M,hφ,hM⟩ := finiteMeasure_subsequence_dependent (X:=fun _ : Index => Space)
    (fun n i => measures (F n) (ψ n) i) (fun _ => 1) (fun n i => measures_mass_le (F n) (ψ n) i)
  refine ⟨φ,M,hφ,hM,?_⟩
  intro i
  have hm := (FiniteMeasure.continuous_map continuous_fst).tendsto (M i) |>.comp (hM i)
  apply tendsto_nhds_unique hm
  cases i with
  | point =>
    change Tendsto (fun n => (points (F (φ n)) (ψ (φ n))).map Prod.fst) atTop (𝓝 L.points)
    simp_rw [points_map]
    exact hF.points.comp hφ.tendsto_atTop
  | vertex J =>
    change Tendsto (fun n => (vertices (F (φ n)) (ψ (φ n)) J).map Prod.fst) atTop (𝓝 (L.vertices J))
    simp_rw [vertices_map]
    exact (hF.vertices J).comp hφ.tendsto_atTop
  | edge J =>
    change Tendsto (fun n => (edges (F (φ n)) (ψ (φ n)) J).map Prod.fst) atTop (𝓝 (L.edgeWindow J))
    simp_rw [edges_map]
    exact (hF.edgeWindow J).comp hφ.tendsto_atTop

lemma vertices_le_points (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J : Measure Space)≤(points F ψ : Measure Space) := by
  apply Measure.le_iff.mpr
  intro U hU
  have he : (vertices F ψ J U:ℝ)≤(points F ψ U:ℝ) := by
    rw [vertices,System.vertexMeasure_apply _ _ hU,points,weightedAtoms_apply_finset _ _ hU]
    simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp he))

lemma local_cubic {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i)))
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 /
      (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 /
      (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {U : Set Space} (hU : MeasurableSet U) :
    (M (.edge J) U:ℝ)^3≤C*((M (.vertex J)).mass:ℝ)^3*(M (.vertex J) U:ℝ) := by
  have hm := NNReal.continuous_coe.tendsto _ |>.comp
    (FiniteMeasure.continuous_mass.tendsto _ |>.comp (hM (.vertex J)))
  apply cubed_bound_limit (hM (.vertex J)) (hM (.edge J))
    (mul_nonneg hC (pow_nonneg (NNReal.coe_nonneg _) _)) ((hm.pow 3).const_mul C) herror
  · intro n V hV
    have hR : 0<((F n).R:ℝ≥0) := Nat.cast_pos.mpr (F n).R_pos
    have ha : 0<((F n).a:ℝ≥0) := Nat.cast_pos.mpr (F n).a_pos
    have hh := ((F n).system.timeWindow J).atomic_cubed_bound (F n).generic
      (fun v => label (F n) (ψ n) ((F n).point v)) (show 0<((F n).R:ℝ≥0)*(F n).a^2 by positivity) hV
    change (edges (F n) (ψ n) J V:ℝ)^3≤_
    apply hh.trans
    apply add_le_add
    · dsimp only [Function.comp_apply]
      push_cast
      rw [show ((measures (F n) (ψ n) (.vertex J)).mass:ℝ)=
        (((F n).system.timeWindow J).vertices.card:ℝ)/(F n).n from by
          change ((vertices (F n) (ψ n) J).mass:ℝ)=_
          rw [vertices_mass,(F n).vertices_mass_ratio]]
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      exact mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (by positivity) _)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 3
      exact_mod_cast (show ((F n).system.timeWindow J).vertices.card≤(F n).n by
        simpa only [Fintype.card_fin] using ((F n).system.timeWindow J).vertices.card_le_univ)
  · exact hU

end PlanarHalving.Enhancement

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma support_lift_restrict {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HereditarilyLindelofSpace X]
    (μ ρ : Measure X) (hac : ρ ≪ μ) (A : Set X) :
    ρ.restrict (A∩μ.support)=ρ.restrict A := by
  apply Measure.restrict_congr_set
  filter_upwards [hac.ae_le μ.support_mem_ae] with x hx
  exact propext ⟨fun h => h.1,fun ha => ⟨ha,hx⟩⟩

lemma support_lift_disk {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (X × Cube)) (G : Set X) (hG : MeasurableSet G)
    (π : X → Point) (hπ : Measurable π) (l : (π '' G) → Point)
    {m : ℕ} {c : ℝ} (hc : 0<c)
    (hdensity : (((μ.map Prod.fst).restrict G).map π)≤(m:ℝ≥0∞) • volume)
    (hgraph : ∀ z∈μ.support, ∀ hz : z.1∈G, z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩))
    (hl : ∀ p, ‖l p‖≤1)
    (hsep : ∀ p p' : (π '' G), c*dist (p:Point) p'^((17:ℝ)/16)≤dist (l p) (l p')) :
    let H := Prod.fst ⁻¹' G ∩ μ.support
    let β := (μ.restrict H).map (decode ∘ Prod.snd)
    MeasurableSet H ∧
      (∀ z∈H, ‖decode z.2‖≤1) ∧
      ∃ C : ℝ, 0≤C ∧ ∀ x : Point, ∀ r : ℝ, 0<r →
        β (closedBall x r)≤ENNReal.ofReal (C*r^((32:ℝ)/17)) := by
  dsimp only
  let H := Prod.fst ⁻¹' G ∩ μ.support
  have hH : MeasurableSet H := (hG.preimage measurable_fst).inter μ.isClosed_support.measurableSet
  have hmap : ((μ.restrict (Prod.fst ⁻¹' G)).map (π∘Prod.fst))=
      ((μ.map Prod.fst).restrict G).map π := by
    rw [Measure.restrict_map measurable_fst hG,Measure.map_map hπ measurable_fst]
  have hd : (μ.restrict H).map (π∘Prod.fst)≤(m:ℝ≥0∞) • volume :=
    (Measure.map_mono (Measure.restrict_mono_set μ inter_subset_left) (hπ.comp measurable_fst)).trans
      (hmap ▸ hdensity)
  have hg (z : X × Cube) (hz : z∈H) : decode z.2=l ⟨π z.1,mem_image_of_mem π hz.1⟩ := by
    rw [hgraph z hz.2 hz.1,decode_encode]
  refine ⟨hH,fun z hz => by rw [hg z hz]; exact hl _,
    (m:ℝ)*(4*(2/c)^((32:ℝ)/17)),by positivity,?_⟩
  intro x r hr
  have hh := disk_bound_of_inverse_holder μ H hH (π∘Prod.fst) (decode∘Prod.snd)
    (hπ.comp measurable_fst) (measurable_decode.comp measurable_snd)
    hc (by norm_num : (0:ℝ)<17/16) hd (by
      intro z hz w hw
      simpa only [Function.comp_apply,hg z hz,hg w hw] using
        hsep ⟨π z.1,mem_image_of_mem π hz.1⟩ ⟨π w.1,mem_image_of_mem π hw.1⟩) x hr
  convert hh using 1
  norm_num only [show (2:ℝ)/(17/16)=32/17 by norm_num,
      ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (by positivity : 0≤(4:ℝ)*(2/c)^((32:ℝ)/17)),mul_assoc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Metric Boundary

lemma unit_sqNorm_coordinate_bounds {v : Point} (hv : sqNorm v=1) :
    |v.1|≤1 ∧ |v.2|≤1 := by
  dsimp [sqNorm] at hv
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs]; nlinarith [sq_nonneg v.2]
  · apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs]; nlinarith [sq_nonneg v.1]

lemma unit_sqNorm_norm {v : Point} (hv : sqNorm v=1) : ‖v‖≤1 := by
  rw [Prod.norm_def]
  exact max_le (unit_sqNorm_coordinate_bounds hv).1 (unit_sqNorm_coordinate_bounds hv).2

lemma transverse_decomposition {ν : Point} (hν : sqNorm ν=1) (w : Point) :
    w=(dot (-ν.2,ν.1) w) • (-ν.2,ν.1)+(dot ν w) • ν := by
  dsimp [sqNorm] at hν
  ext <;> dsimp [dot] <;> nlinarith [congrArg (fun t : ℝ => t*w.1) hν,
    congrArg (fun t : ℝ => t*w.2) hν]

lemma bounded_strip_cover (ν : Point) (hν : sqNorm ν=1) (c : ℝ)
    {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    ∃ (S : Finset ℤ) (a : ℤ → Point), (S.card:ℝ)≤13/r ∧
      closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r} ⊆
        ⋃ j∈S, closedBall (a j) (3*r) := by
  classical
  let A : Set Point := closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r}
  by_cases hA : A.Nonempty
  swap
  · refine ⟨∅,fun _ => 0,by simp; positivity,?_⟩
    intro x hx
    exact (hA ⟨x,hx⟩).elim
  obtain ⟨a,ha⟩ := hA
  let v : Point := (-ν.2,ν.1)
  have hv : sqNorm v=1 := by dsimp [v,sqNorm]; simpa only [sqNorm,neg_sq,add_comm] using hν
  have hnν := unit_sqNorm_norm hν
  have hnv := unit_sqNorm_norm hv
  let k : ℤ := ⌈4/r⌉+1
  let S : Finset ℤ := Finset.Icc (-k) k
  have hkpos : 0≤k := by
    have hh := Int.le_ceil (4/r)
    have : (0:ℝ)≤(k:ℝ) := by dsimp [k]; push_cast; linarith [div_pos (by norm_num : (0:ℝ)<4) hr]
    exact_mod_cast this
  have hkbound : (k:ℝ)≤4/r+2 := by
    have hh := Int.ceil_lt_add_one (4/r)
    dsimp [k]; push_cast; linarith
  have hcard : (S.card:ℝ)=2*(k:ℝ)+1 := by
    dsimp [S]
    rw [Int.card_Icc]
    rw [show ((k+1- -k).toNat:ℝ)=((k+1- -k):ℝ) by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0≤k+1- -k))]
    ring
  refine ⟨S,fun j => a+(r*(j:ℝ)) • v,?_,?_⟩
  · rw [hcard]
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right hkbound hr.le
    rw [add_mul,div_mul_cancel₀ _ hr.ne'] at hh
    nlinarith
  · intro x hx
    have hdiff : ‖x-a‖≤2 := by
      have hx' : ‖x‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
      have ha' : ‖a‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using ha.1
      exact (norm_sub_le _ _).trans (by linarith)
    let t : ℝ := dot v (x-a)
    let δ : ℝ := dot ν (x-a)
    have hδ : |δ|≤2*r := by
      have he : δ=(dot ν x-c)-(dot ν a-c) := by dsimp [δ,dot]; ring
      rw [he]
      have hx2 : |dot ν x-c|≤r := hx.2
      have ha2 : |dot ν a-c|≤r := ha.2
      exact (abs_sub _ _).trans (by linarith)
    have ht : |t|≤4 := by
      have h1 : |(x-a).1|≤2 := (le_max_left _ _).trans hdiff
      have h2 : |(x-a).2|≤2 := (le_max_right _ _).trans hdiff
      have hv' := unit_sqNorm_coordinate_bounds hv
      dsimp [t,dot]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul]
      have hh1 := mul_le_mul hv'.1 h1 (abs_nonneg _) zero_le_one
      have hh2 := mul_le_mul hv'.2 h2 (abs_nonneg _) zero_le_one
      dsimp only [Prod.fst_sub,Prod.snd_sub] at hh1 hh2
      linarith
    let j : ℤ := ⌊t/r⌋
    have hjlo : (j:ℝ)≤t/r := Int.floor_le _
    have hjhi : t/r<(j:ℝ)+1 := Int.lt_floor_add_one _
    have hceil : 4/r≤(⌈4/r⌉:ℤ) := Int.le_ceil _
    have htlo : -(4/r)≤t/r := by
      apply (le_div_iff₀ hr).mpr
      have ht' := (abs_le.mp ht).1
      rw [neg_mul,div_mul_cancel₀ _ hr.ne']
      exact ht'
    have hthi : t/r≤4/r := (div_le_div_iff_of_pos_right hr).mpr (abs_le.mp ht).2
    have hjmem : j∈S := by
      apply Finset.mem_Icc.mpr
      constructor
      · have : -(k:ℝ)≤(j:ℝ) := by dsimp [k]; push_cast; linarith
        exact_mod_cast this
      · have : (j:ℝ)≤(k:ℝ) := by dsimp [k]; push_cast; linarith
        exact_mod_cast this
    refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hjmem,?_⟩⟩
    have he : x-(a+(r*(j:ℝ)) • v)=(t-r*(j:ℝ)) • v+δ • ν := by
      have hw := transverse_decomposition hν (x-a)
      change x-a=t • v+δ • ν at hw
      calc
        x-(a+(r*(j:ℝ)) • v) = (x-a)-(r*(j:ℝ)) • v := by abel
        _ = _ := by rw [hw]; module
    rw [mem_closedBall,dist_eq_norm,he]
    have htr0 : 0≤t-r*(j:ℝ) := by
      have hh := (le_div_iff₀ hr).mp hjlo
      nlinarith
    have htr1 : t-r*(j:ℝ)≤r := by
      have hh := (div_lt_iff₀ hr).mp hjhi
      nlinarith
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg htr0]
    have hh1 := mul_le_mul htr1 hnv (norm_nonneg _) hr.le
    have hh2 := mul_le_mul hδ hnν (norm_nonneg _) (by positivity : 0≤2*r)
    linarith

open MeasureTheory Filter
open scoped ENNReal Topology
lemma strip_bound_of_disk (μ : Measure Point) {C d : ℝ} (_hC : 0≤C)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r → μ (closedBall x r)≤ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r}) ≤
      ENNReal.ofReal (13*C*3^d*r^(d-1)) := by
  obtain ⟨S,a,hcard,hcover⟩ := bounded_strip_cover ν hν c hr hr1
  have hcast : (S.card:ℝ≥0∞)≤ENNReal.ofReal (13/r) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc
    _ ≤ μ (⋃ j∈S,closedBall (a j) (3*r)) := measure_mono hcover
    _ ≤ ∑ j∈S,μ (closedBall (a j) (3*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j∈S,ENNReal.ofReal (C*(3*r)^d) := Finset.sum_le_sum (fun j _ => hbound (a j) (3*r) (by positivity))
    _ = (S.card:ℝ≥0∞)*ENNReal.ofReal (C*(3*r)^d) := by simp
    _ ≤ ENNReal.ofReal (13/r)*ENNReal.ofReal (C*(3*r)^d) := mul_le_mul' hcast le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) hr.le,Real.rpow_sub hr]
      simp only [Real.rpow_one]
      ring

lemma line_null_of_disk (μ : Measure Point) {C d : ℝ} (hC : 0≤C) (hd : 1<d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r → μ (closedBall x r)≤ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) :
    μ (closedBall (0:Point) 1 ∩ {x | dot ν x=c})=0 := by
  let a := μ (closedBall (0:Point) 1 ∩ {x | dot ν x=c})
  have hb : ∀ᶠ r in 𝓝[>] (0:ℝ), a≤ENNReal.ofReal (13*C*3^d*r^(d-1)) := by
    have hu : ∀ᶠ r in 𝓝[>] (0:ℝ), r<1 := (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hu] with r hr hr1
    have hr : (0:ℝ)<r := hr
    apply le_trans (b:=μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r})) ?_
      (strip_bound_of_disk μ hC hbound ν hν c hr hr1.le)
    apply measure_mono
    intro x hx
    have hxe : dot ν x=c := hx.2
    exact ⟨hx.1,show |dot ν x-c|≤r by simpa only [hxe,sub_self,abs_zero] using hr.le⟩
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (13*C*3^d*r^(d-1))) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun r : ℝ => r^(d-1)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      convert (Real.continuous_rpow_const (sub_nonneg.mpr hd.le)).tendsto (0:ℝ) using 1
      exact (Real.zero_rpow (sub_ne_zero.mpr hd.ne')).symm ▸ rfl
    have hh' : Tendsto (fun r : ℝ => r^(d-1)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      hh.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun r : ℝ => 13*C*3^d*r^(d-1)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hh'.const_mul (13*C*3^d)
    convert (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp hc using 1
    · rfl
    · rw [ENNReal.ofReal_zero]
  exact le_antisymm (ge_of_tendsto ht hb) zero_le

end PlanarHalving.Spatial

end OAI
