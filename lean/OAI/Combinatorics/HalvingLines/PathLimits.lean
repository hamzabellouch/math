import OAI.Combinatorics.HalvingLines.ChainDrawing

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.extension_vertex (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) : C.extension l u (C.point c).1 = (C.point c).2 := by
  induction c using Fin.induction with
  | zero =>
    apply le_antisymm (C.extension_below_vertex hsl 0)
    have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr false) (C.point 0).1
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (C.point 0).1
    linarith only [hh]
  | succ b ih =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · rw [← hb]
      exact ih
    · exact C.extension_edge hsl b hb (right_mem_segment ℝ _ _)

lemma ConvexPath.extension_left (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (hx : x ≤ (C.point 0).1) :
    C.extension l u x = (C.point 0).2 + l*(x-(C.point 0).1) := by
  apply le_antisymm
  · apply envelope_le
    intro i
    have hi := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) i (C.point 0).1
    change _ ≤ C.extension l u (C.point 0).1 at hi
    rw [C.extension_vertex hsl] at hi
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (C.extension_slopes hlu hsl i).1) (sub_nonpos.mpr hx)
    nlinarith only [hi,hm]
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr false) x
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) x
    linarith only [hh]

lemma ConvexPath.extension_right (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (hx : (C.point (Fin.last R)).1 ≤ x) :
    C.extension l u x = (C.point (Fin.last R)).2 + u*(x-(C.point (Fin.last R)).1) := by
  apply le_antisymm
  · apply envelope_le
    intro i
    have hi := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) i (C.point (Fin.last R)).1
    change _ ≤ C.extension l u (C.point (Fin.last R)).1 at hi
    rw [C.extension_vertex hsl] at hi
    have hm := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (C.extension_slopes hlu hsl i).2) (sub_nonneg.mpr hx)
    nlinarith only [hi,hm]
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr true) x
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) x
    linarith only [hh]

lemma finite_intermediate {R : ℕ} (f : Fin (R+1) → ℝ) {x : ℝ}
    (h₀ : f 0 ≤ x) (h₁ : x < f (Fin.last R)) :
    ∃ b : Fin R, f b.castSucc ≤ x ∧ x < f b.succ := by
  have haux : ∀ c : Fin (R+1), x < f c → ∃ b : Fin R, f b.castSucc ≤ x ∧ x < f b.succ := by
    intro c
    induction c using Fin.induction with
    | zero => exact fun h => (not_lt_of_ge h₀ h).elim
    | succ b ih =>
      intro h
      by_cases hb : f b.castSucc ≤ x
      · exact ⟨b,hb,h⟩
      · exact ih (lt_of_not_ge hb)
  exact haux (Fin.last R) h₁

lemma ConvexPath.extension_middle (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (h₀ : (C.point 0).1 ≤ x) (h₁ : x < (C.point (Fin.last R)).1) :
    ∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧
      (x,C.extension l u x) ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
  obtain ⟨b,hb₀,hb₁⟩ := finite_intermediate (fun c => (C.point c).1) h₀ h₁
  have hbx : (C.point b.castSucc).1 < (C.point b.succ).1 := hb₀.trans_lt hb₁
  have hb : C.point b.castSucc ≠ C.point b.succ := fun h => hbx.ne (congrArg Prod.fst h)
  let t := (x-(C.point b.castSucc).1)/((C.point b.succ).1-(C.point b.castSucc).1)
  have ht : t ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hb₀) (sub_nonneg.mpr hbx.le), ?_⟩
    exact (div_le_one (sub_pos.mpr hbx)).mpr (by linarith only [hb₁])
  let z : Point := (1-t) • C.point b.castSucc + t • C.point b.succ
  have hz : z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
    rw [segment_eq_image]
    exact ⟨t,ht,rfl⟩
  have hzx : z.1 = x := by
    dsimp [z,t]
    field_simp [ne_of_gt (sub_pos.mpr hbx)]
    ring
  have hzy := C.extension_edge hsl b hb hz
  rw [hzx] at hzy
  have he : (x,C.extension l u x) = z := Prod.ext hzx.symm hzy
  exact ⟨b,hb,he ▸ hz⟩

lemma ConvexPath.extension_cases (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {z : Point} (hz : C.extension l u z.1 = z.2) :
    (z.1 ≤ (C.point 0).1 ∧ z.2 = (C.point 0).2 + l*(z.1-(C.point 0).1)) ∨
    ((C.point (Fin.last R)).1 ≤ z.1 ∧ z.2 = (C.point (Fin.last R)).2 + u*(z.1-(C.point (Fin.last R)).1)) ∨
    (∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧ z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ)) := by
  by_cases hl : z.1 ≤ (C.point 0).1
  · exact Or.inl ⟨hl, hz.symm.trans (C.extension_left hlu hsl hl)⟩
  by_cases hu : (C.point (Fin.last R)).1 ≤ z.1
  · exact Or.inr (Or.inl ⟨hu,hz.symm.trans (C.extension_right hlu hsl hu)⟩)
  obtain ⟨b,hb,hz'⟩ := C.extension_middle hsl (le_of_not_ge hl) (lt_of_not_ge hu)
  rw [hz] at hz'
  exact Or.inr (Or.inr ⟨b,hb,hz'⟩)

end PlanarHalving.Batches
namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

theorem subsequence_of_asymptotic_continuity
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (G : Set X) (hG : G.Nonempty) (K : Set Y) (hK : IsCompact K)
    (hbounded : ∀ n p, p ∈ G → f n p ∈ K)
    (hcont : ∀ p ∈ G, ∀ ε > 0, ∃ r > 0,
      ∀ᶠ n in atTop, ∀ q, dist q p < r → dist (f n q) (f n p) ≤ ε) :
    ∃ (φ : ℕ → ℕ) (l : G → Y), StrictMono φ ∧
      (∀ p, l p ∈ K) ∧
      (∀ p : G, ∀ u : ℕ → X, Tendsto u atTop (𝓝 (p : X)) →
        Tendsto (fun n => f (φ n) (u n)) atTop (𝓝 (l p))) := by
  classical
  let : Nonempty G := hG.to_subtype
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq G
  let F : ℕ → ℕ → K := fun n j => ⟨f n (q j), hbounded n (q j) (q j).property⟩
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq F
  have hgrid (j : ℕ) : Tendsto (fun n => f (φ n) (q j)) atTop (𝓝 (g j : Y)) :=
    continuous_subtype_val.tendsto _ |>.comp ((tendsto_pi_nhds.mp hg) j)
  have hcauchy (p : G) : CauchySeq (fun n => f (φ n) p) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨r,hr,hrf⟩ := hcont p p.property (ε/4) (by positivity)
    obtain ⟨j,hj⟩ := hq.exists_dist_lt p hr
    have hj' : dist (q j : X) p < r := by simpa only [Subtype.dist_eq, dist_comm] using hj
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hφ.tendsto_atTop.eventually hrf)
    obtain ⟨N',hN'⟩ := Metric.cauchySeq_iff.mp (hgrid j).cauchySeq (ε/4) (by positivity)
    refine ⟨max N N',fun m hm n hn => ?_⟩
    have hm' := hN m (le_trans (le_max_left _ _) hm) (q j) hj'
    have hn' := hN n (le_trans (le_max_left _ _) hn) (q j) hj'
    have hmn := hN' m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    have htri := dist_triangle4 (f (φ m) p) (f (φ m) (q j)) (f (φ n) (q j)) (f (φ n) p)
    rw [dist_comm (f (φ m) p) (f (φ m) (q j))] at htri
    linarith only [htri,hm',hn',hmn,hε]
  choose l hl using fun p => cauchySeq_tendsto_of_complete (hcauchy p)
  refine ⟨φ,l,hφ,?_,?_⟩
  · intro p
    exact hK.isClosed.mem_of_tendsto (hl p) (Eventually.of_forall (fun n => hbounded (φ n) p p.property))
  · intro p u hu
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨r,hr,hrf⟩ := hcont p p.property (ε/3) (by positivity)
    have hu' : ∀ᶠ n in atTop, dist (u n) (p : X) < r := (Metric.tendsto_nhds.mp hu) r hr
    have hl' : ∀ᶠ n in atTop, dist (f (φ n) p) (l p) < ε/3 :=
      (Metric.tendsto_nhds.mp (hl p)) (ε/3) (by positivity)
    apply eventually_atTop.mp
    filter_upwards [hφ.tendsto_atTop.eventually hrf,hu',hl'] with n hn hnu hnl
    have hh := hn (u n) hnu
    have ht := dist_triangle (f (φ n) (u n)) (f (φ n) p) (l p)
    linarith only [hh,ht,hnl,hε]

lemma asymptotic_continuity_of_radial
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (G : Set X) (r e : ℕ → ℝ)
    (hr : ∀ j, 0 < r j) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ p ∈ G, ∀ j, ∀ᶠ n in atTop,
      ∀ q, dist q p < r j → dist (f n q) (f n p) ≤ e j) :
    ∀ p ∈ G, ∀ ε > 0, ∃ δ > 0,
      ∀ᶠ n in atTop, ∀ q, dist q p < δ → dist (f n q) (f n p) ≤ ε := by
  intro p hp ε hε
  obtain ⟨j,hj⟩ := ((tendsto_order.mp he).2 ε hε).exists
  refine ⟨r j,hr j,?_⟩
  filter_upwards [hb p hp j] with n hn q hq
  exact (hn q hq).trans hj.le

lemma lower_distance_of_limit
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {p q : X} {x y : Y} (hp : Tendsto (fun n => f (φ n) p) atTop (𝓝 x))
    (hq : Tendsto (fun n => f (φ n) q) atTop (𝓝 y))
    {a : ℝ} (ha : ∀ᶠ n in atTop, a ≤ dist (f n p) (f n q)) : a ≤ dist x y := by
  exact ge_of_tendsto (hp.dist hq) (hφ.tendsto_atTop.eventually ha)

end PlanarHalving.Spatial
namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma geometric_scale {q h d : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (_hh : 0 < h) (hd : 0 < d) (hdh : d ≤ h) :
    ∃ j : ℕ, 1 ≤ j ∧ h*q^j < d ∧ q*d ≤ h*q^j := by
  have ht : Tendsto (fun j : ℕ => h*q^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul h
  have hex : ∃ j : ℕ, h*q^j < d := ((tendsto_order.mp ht).2 d hd).exists
  let j := Nat.find hex
  have hj : h*q^j < d := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h
    simp only [h,pow_zero,mul_one] at hj
    exact (not_lt_of_ge hdh) hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  have hprev : d ≤ h*q^(j-1) := by
    exact le_of_not_gt (Nat.find_min hex (show j-1 < j by omega))
  refine ⟨j,hj1,hj,?_⟩
  have hp : q^j = q^(j-1)*q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  nlinarith only [mul_le_mul_of_nonneg_left hprev hq.le]

lemma geometric_lower_power {q h d s : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hd : 0 < d) (hdh : d ≤ h) (hs : 0 ≤ s) :
    ∃ j : ℕ, 1 ≤ j ∧ h*q^j < d ∧
      q^s * (q/h)^s * d^s ≤ (q^s)^(j+1) := by
  obtain ⟨j,hj,hjd,hdj⟩ := geometric_scale hq hq1 hh hd hdh
  refine ⟨j,hj,hjd,?_⟩
  have hdiv : q/h*d ≤ q^j := by
    have hv : q*d/h ≤ q^j := (div_le_iff₀ hh).mpr (by nlinarith only [hdj])
    convert hv using 1
    ring
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ q/h*d) hdiv hs
  rw [Real.mul_rpow (by positivity) hd.le] at hp
  rw [pow_succ, Real.rpow_pow_comm hq.le]
  have ht := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hq.le s)
  nlinarith only [ht]

lemma inverse_holder_of_radial_limits
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (G : Set X) (l : G → Y)
    (hl : ∀ p : G, Tendsto (fun n => f (φ n) p) atTop (𝓝 (l p)))
    {q h s : ℝ} (hq : 0 < q) (hq1 : q < 1) (hh : 0 < h) (hs : 0 < s)
    (hdiam : ∀ p p' : G, dist (p : X) p' ≤ h)
    (hlower : ∀ p : G, ∀ j : ℕ, 1 ≤ j → ∀ᶠ n in atTop,
      ∀ p' : G, h*q^j < dist (p : X) p' → (q^s)^(j+1) ≤ dist (f n p) (f n p')) :
    ∀ p p' : G, (q^s * (q/h)^s) * dist (p : X) p' ^ s ≤ dist (l p) (l p') := by
  intro p p'
  by_cases hpp : p = p'
  · subst p'
    simp [Real.zero_rpow hs.ne']
  · have hd : 0 < dist (p : X) p' := dist_pos.mpr (Subtype.coe_ne_coe.mpr hpp)
    obtain ⟨j,hj,hjd,hdj⟩ := geometric_lower_power hq hq1 hh hd (hdiam p p') hs.le
    apply hdj.trans
    apply lower_distance_of_limit f φ hφ (hl p) (hl p')
    filter_upwards [hlower p j hj] with n hn
    exact hn p' hjd

end PlanarHalving.Spatial
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal

theorem finiteMeasure_subsequence
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → ℕ → FiniteMeasure X) (C : ℕ → ℝ≥0)
    (hbound : ∀ n j, (μ n j).mass ≤ C j) :
    ∃ (φ : ℕ → ℕ) (ν : ℕ → FiniteMeasure X), StrictMono φ ∧
      ∀ j, Tendsto (fun n => μ (φ n) j) atTop (𝓝 (ν j)) := by
  let F : ℕ → ∀ j : ℕ, (Icc (0 : ℝ≥0) (C j)) × ProbabilityMeasure X :=
    fun n j => (⟨(μ n j).mass,zero_le,hbound n j⟩,(μ n j).normalize)
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq F
  refine ⟨φ,fun j => (g j).1.val • (g j).2.toFiniteMeasure,hφ,?_⟩
  intro j
  have hj := (tendsto_pi_nhds.mp hg) j
  have hm := continuous_subtype_val.tendsto _ |>.comp ((continuous_fst.tendsto (g j)).comp hj)
  have hn := (ProbabilityMeasure.toFiniteMeasure_isEmbedding X).continuous.tendsto _ |>.comp
    ((continuous_snd.tendsto (g j)).comp hj)
  have ht := hm.smul hn
  convert ht using 1
  funext n
  exact (μ (φ n) j).self_eq_mass_smul_normalize

end PlanarHalving.Limits

namespace PlanarHalving.RankCoordinates
open Set

lemma variation_le_two {f : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i ≤ n, 0 ≤ f i ∧ f i ≤ 1)
    (hqc : ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (f i) (f k) ≤ f j) :
    ∑ i ∈ Finset.range n, |f (i+1)-f i| ≤ 2 := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.range (n+1)).exists_max_image f (by simp)
  have hkn : k ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  have hleft : ∑ i ∈ Finset.range k, |f (i+1)-f i| = f k-f 0 := by
    rw [← Finset.sum_range_sub f k]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    apply abs_of_nonneg
    apply sub_nonneg.mpr
    have hq := hqc i (i+1) k (by omega) (by omega) hkn
    rw [min_eq_left (hmax i (by simp; omega))] at hq
    exact hq
  have hright : ∑ i ∈ Finset.Ico k n, |f (i+1)-f i| = f k-f n := by
    calc
      _ = - ∑ i ∈ Finset.Ico k n, (f (i+1)-f i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hki,hin⟩ := Finset.mem_Ico.mp hi
        apply abs_of_nonpos
        apply sub_nonpos.mpr
        have hq := hqc k i (i+1) hki (by omega) (by omega)
        rw [min_eq_right (hmax (i+1) (by simp; omega))] at hq
        exact hq
      _ = _ := by rw [Finset.sum_Ico_sub f hkn]; ring
  rw [← Finset.sum_range_add_sum_Ico (fun i => |f (i+1)-f i|) hkn,hleft,hright]
  have h0 := (hf 0 (Nat.zero_le n)).1
  have hn := (hf n le_rfl).1
  have hk1 := (hf k hkn).2
  linarith only [h0,hn,hk1]

lemma min_le_of_quasiconcave {f : ℝ → ℝ} (hf : QuasiconcaveOn ℝ univ f)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : min (f x) (f z) ≤ f y := by
  have hc := (hf (min (f x) (f z))).ordConnected
  have hx : x ∈ univ ∩ {u | min (f x) (f z) ≤ f u} := by
    refine ⟨mem_univ _,?_⟩
    change min (f x) (f z) ≤ f x
    exact min_le_left _ _
  have hz : z ∈ univ ∩ {u | min (f x) (f z) ≤ f u} := by
    refine ⟨mem_univ _,?_⟩
    change min (f x) (f z) ≤ f z
    exact min_le_right _ _
  exact (hc.out hx hz ⟨hxy,hyz⟩).2

lemma concave_cdf_variation {f F : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    (hF : Monotone F) (hFrange : ∀ x, F x ∈ Icc 0 1)
    (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n, |F (f (x (i+1)))-F (f (x i))| ≤ 2 := by
  apply variation_le_two (fun i _ => hFrange (f (x i)))
  intro i j k hij hjk _
  rw [← hF.map_min]
  exact hF (min_le_of_quasiconcave hf.quasiconcaveOn (hx hij) (hx hjk))

lemma sigmoid_variation {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      |Real.sigmoid (f (x (i+1))/ε)-Real.sigmoid (f (x i)/ε)| ≤ 2 := by
  apply concave_cdf_variation hf
    (fun _ _ h => Real.sigmoid_strictMono.monotone (div_le_div_of_nonneg_right h hε.le))
    (fun _ => ⟨(Real.sigmoid_pos _).le,(Real.sigmoid_lt_one _).le⟩) x hx n

lemma smoothed_variation {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      |smoothed g ε (x (i+1),f (x (i+1)))-smoothed g ε (x i,f (x i))| ≤ 2 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hterm (i : ℕ) :
      |smoothed g ε (x (i+1),f (x (i+1)))-smoothed g ε (x i,f (x i))| ≤
        (∑ j, |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
                Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := by
    unfold smoothed
    rw [← sub_div,abs_div,abs_of_pos hmR,← Finset.sum_sub_distrib]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hmR.le
  calc
    _ ≤ ∑ i ∈ Finset.range n, (∑ j, |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
        Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ j : Fin m, ∑ i ∈ Finset.range n,
        |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
          Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := by
      rw [← Finset.sum_div,Finset.sum_comm]
    _ ≤ (∑ _j : Fin m, (2 : ℝ))/m := by
      apply div_le_div_of_nonneg_right _ hmR.le
      exact Finset.sum_le_sum (fun j _ => sigmoid_variation (hf.sub (hg j)) hε x hx n)
    _ = 2 := by simp; field_simp

end PlanarHalving.RankCoordinates

end OAI
