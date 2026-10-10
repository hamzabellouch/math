import OAI.Combinatorics.HalvingLines.Densities

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter
open scoped Topology unitInterval

lemma exists_positive_inside (μ : Measure I) [NullSingletonClass μ]
    {s t : I} (hpos : μ (Ioo s t) ≠ 0) :
    ∃ J : Window, s < lower J ∧ upper J < t ∧ μ (carrier J) ≠ 0 := by
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  obtain ⟨x,hx,hxs,hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    ((hsupp.and (ae_avoid_boundaries μ)).filter_mono ae_restrict_le)
  have hmesh : Tendsto (fun m : ℕ => 1/(2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hsx : (s : ℝ) < x := hx.1
  have hxt : (x : ℝ) < t := hx.2
  obtain ⟨m,hm⟩ := (hmesh.eventually (gt_mem_nhds
    (show 0 < min ((x:ℝ)-s) ((t:ℝ)-x) by positivity))).exists
  obtain ⟨i,hi⟩ := UniformPartition.mem_some_cell (2^m) x
  let J : Window := ⟨m,i⟩
  have hJ := carrier_subset_Icc J hi
  have hxi : x ∈ Ioo (lower J) (upper J) :=
    ⟨lt_of_le_of_ne hJ.1 (Ne.symm (hxb m i.castSucc)),
      lt_of_le_of_ne hJ.2 (hxb m i.succ)⟩
  have hw := upper_sub_lower J
  have hj1 : (lower J : ℝ) ≤ x := hJ.1
  have hj2 : (x : ℝ) ≤ upper J := hJ.2
  have hm1 := (lt_min_iff.mp hm).1
  have hm2 := (lt_min_iff.mp hm).2
  dsimp [J] at hw
  refine ⟨J,?_,?_,?_⟩
  · change (s : ℝ) < lower J
    linarith
  · change (upper J : ℝ) < t
    linarith
  · exact ne_of_gt ((measure_mono (Ioo_subset_carrier J)).trans_lt'
      ((Measure.mem_support_iff_forall x).mp hxs _ (Ioo_mem_nhds hxi.1 hxi.2)))

lemma carrier_subset_of_inside {J K : Window}
    (hlo : lower K < lower J) (hhi : upper J < upper K) : carrier J ⊆ carrier K := by
  intro x hx
  have h := carrier_subset_Icc J hx
  exact Ioo_subset_carrier K ⟨hlo.trans_le h.1,h.2.trans_lt hhi⟩

end PlanarHalving.TimeWindows
namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter
open scoped Topology unitInterval

lemma nullSingleton_map_coe (μ : Measure I) [NullSingletonClass μ] :
    NullSingletonClass (μ.map (Subtype.val : I → ℝ)) := by
  constructor
  intro x
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply Subtype.ext
  exact (mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm

lemma measure_interior_eq (μ : Measure I) [NullSingletonClass μ] (K : Window) :
    μ (Ioo (lower K) (upper K)) = μ (carrier K) := by
  apply le_antisymm (measure_mono (Ioo_subset_carrier K))
  calc
    μ (carrier K) ≤ μ (Icc (lower K) (upper K)) := measure_mono (carrier_subset_Icc K)
    _ = μ (Ioo (lower K) (upper K)) := measure_congr Ioo_ae_eq_Icc.symm

end PlanarHalving.TimeWindows

namespace PlanarHalving.RankLimits
open MeasureTheory Set Filter TimeWindows
open scoped Topology unitInterval

lemma three_directions_of_independent (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K) ≠ 0)
    (Q : Point ≃L[ℝ] Point) (g : Subwindows K → Point →L[ℝ] ℝ)
    (hne : ∀ t : I, t ∈ Ioo (lower K) (upper K) →
      (Directions.allowed Q g (fun i => (lower i.val : ℝ))
        (fun i => (upper i.val : ℝ)) t).Nonempty)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point => (g i v,g j v))) :
    ∃ t₁ t₂ t₃ : I, ∃ d₁ d₂ d₃ : ℝ,
      t₁∈Ioo (lower K) (upper K) ∧ t₂∈Ioo (lower K) (upper K) ∧
      t₃∈Ioo (lower K) (upper K) ∧ t₁<t₂ ∧ t₂<t₃ ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₁={d₁} ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₂={d₂} ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₃={d₃} ∧
      d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  let ν := μ.map (Subtype.val : I → ℝ)
  let : NullSingletonClass ν := nullSingleton_map_coe μ
  let U : Set ℝ := Ioo (lower K : ℝ) (upper K : ℝ)
  have hU : 0 < ν U := by
    rw [show ν U=μ (Ioo (lower K) (upper K)) by
      rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioo]; rfl,
      measure_interior_eq μ K]
    exact pos_iff_ne_zero.mpr hpos
  have hmem {t : ℝ} (ht : t ∈ U) : t ∈ Icc (0:ℝ) 1 :=
    ⟨(lower K).property.1.trans ht.1.le,ht.2.le.trans (upper K).property.2⟩
  obtain ⟨t₁,t₂,t₃,d₁,d₂,d₃,ht₁,ht₂,ht₃,h12,h23,he1,he2,he3,hd12,hd23,hd13⟩ :=
    Directions.three_allowed_directions ν U (Metric.isBounded_Ioo _ _) hU Q g
      (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ))
      (fun t ht => hne ⟨t,hmem ht⟩ ht) (by
        intro s hs t ht hst hp
        let s' : I := ⟨s,hmem hs⟩
        let t' : I := ⟨t,hmem ht⟩
        have hμ : μ (Ioo s' t') ≠ 0 := by
          apply ne_of_gt
          rw [show ν (Ioo s t)=μ (Ioo s' t') by
            rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioo]; rfl] at hp
          exact hp
        obtain ⟨J,hsJ,hJt,hJ⟩ := exists_positive_inside μ hμ
        have hJK : carrier J ⊆ carrier K := carrier_subset_of_inside
          (lt_trans hs.1 hsJ) (lt_trans hJt ht.2)
        obtain ⟨i,j,hi,hj,hij⟩ := hind ⟨J,hJK⟩ hJ
        refine ⟨i,j,?_,?_,?_,?_,hij⟩
        · exact hsJ.trans_le (endpoints_of_subset hi).1
        · exact ((endpoints_of_subset hi).2).trans_lt hJt
        · exact hsJ.trans_le (endpoints_of_subset hj).1
        · exact ((endpoints_of_subset hj).2).trans_lt hJt)
  exact ⟨⟨t₁,hmem ht₁⟩,⟨t₂,hmem ht₂⟩,⟨t₃,hmem ht₃⟩,d₁,d₂,d₃,
    ht₁,ht₂,ht₃,h12,h23,he1,he2,he3,hd12,hd23,hd13⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.Directions
open Set Filter
open scoped Topology

lemma quadrant_allowed {ι : Type*} (Q : Plane ≃L[ℝ] Plane)
    (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ) (t : ℝ) {d : Plane}
    (h₁ : 0 ≤ (Q.symm d).1) (h₂ : 0 ≤ (Q.symm d).2) (hd : d ≠ 0)
    (hineq : ∀ i, (hi i < t → 0 ≤ g i d) ∧ (t < lo i → g i d ≤ 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ z ∈ allowed Q g lo hi t, d = r • Q (simplex z) := by
  let a := Q.symm d
  have ha : a ≠ 0 := by
    intro he
    apply hd
    simpa only [a,Q.apply_symm_apply,map_zero] using congrArg Q he
  have hp : 0 < a.1+a.2 := by
    by_contra hn
    have he : a.1=0 ∧ a.2=0 := by constructor <;> linarith
    exact ha (Prod.ext he.1 he.2)
  let r := a.1+a.2
  let z := a.1/r
  have hz : z ∈ Icc (0:ℝ) 1 := ⟨div_nonneg h₁ hp.le,
    (div_le_one hp).mpr (by change a.1 ≤ a.1+a.2; linarith [h₂])⟩
  have hr : r ≠ 0 := hp.ne'
  have hd' : d = r • Q (simplex z) := by
    apply Q.symm.injective
    rw [map_smul,Q.symm_apply_apply]
    change a = r • simplex z
    ext <;> dsimp [simplex,z]
    · field_simp [hr]
    · field_simp [hr]; dsimp [r]; ring
  refine ⟨r,hp,z,⟨hz,?_⟩,hd'⟩
  intro i
  have hgd : g i d = r * g i (Q (simplex z)) := by rw [hd',map_smul]; rfl
  constructor
  · intro hit
    have h := (hineq i).1 hit
    rw [hgd] at h
    exact nonneg_of_mul_nonneg_right h hp
  · intro hti
    have h := (hineq i).2 hti
    rw [hgd] at h
    exact nonpos_of_mul_nonpos_right h hp

end PlanarHalving.Directions

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma actual_forward_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (x y : ℕ → Point) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hxy : ∀ n, y n = x n+s n • (1,(F n).timeSlope t))
    (a b : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a))
    (hyb : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (y n)-p)) atTop (𝓝 b))
    (hjx : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (x n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i a)))
    (hjy : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (y n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i b)))
    (hab : b-a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ z ∈ Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t,
      b-a = r • reflectFirst (Directions.simplex z) := by
  have hF (n : ℕ) (q : Point) :
      (F n).rankChart hAB (hA n) (hB n) q =
        (((F n).system.labels (F n).generic q A : ℝ),-((F n).system.labels (F n).generic q B : ℝ)) := by
    rw [(F n).rankChart_apply]; rfl
  have h₁ : b.1 ≤ a.1 := by
    apply le_of_tendsto_of_tendsto ((continuous_fst.tendsto b).comp hyb) ((continuous_fst.tendsto a).comp hxa)
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_def]
    rw [hF,hF]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hh n).le)
    apply sub_le_sub_right
    rw [hxy]
    simpa only [zero_smul,add_zero] using (F n).rank_forward_before (hA n) htA (x n) (hs n)
  have h₂ : a.2 ≤ b.2 := by
    apply le_of_tendsto_of_tendsto ((continuous_snd.tendsto a).comp hxa) ((continuous_snd.tendsto b).comp hyb)
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_def]
    rw [hF,hF]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hh n).le)
    apply sub_le_sub_right
    apply neg_le_neg
    rw [hxy]
    simpa only [zero_smul,add_zero] using (F n).rank_forward_before (hB n) htB (x n) (hs n)
  apply Directions.quadrant_allowed reflectFirst D _ _ t (d:=b-a) _ _ hab
  · intro i
    constructor
    · intro hit
      have hle : D i a ≤ D i b := by
        apply le_of_tendsto_of_tendsto (hjx i) (hjy i)
        filter_upwards [hC i] with n hn
        apply div_le_div_of_nonneg_right _ (hh n).le
        apply sub_le_sub_right
        rw [hxy]
        simpa only [zero_smul,add_zero] using
          (F n).rank_forward_after hn hit.le (x n) (hs n)
      simpa only [map_sub] using sub_nonneg.mpr hle
    · intro hti
      have hle : D i b ≤ D i a := by
        apply le_of_tendsto_of_tendsto (hjy i) (hjx i)
        filter_upwards [hC i] with n hn
        apply div_le_div_of_nonneg_right _ (hh n).le
        apply sub_le_sub_right
        rw [hxy]
        simpa only [zero_smul,add_zero] using
          (F n).rank_forward_before hn hti.le (x n) (hs n)
      simpa only [map_sub] using sub_nonpos.mpr hle
  · change 0 ≤ -(b.1-a.1)
    linarith
  · change 0 ≤ b.2-a.2
    linarith

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma actual_unoriented_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) (z : ℝ)
    (hz : Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t = {z})
    (x y : ℕ → Point) (s : ℕ → ℝ)
    (hxy : ∀ n, y n = x n+s n • (1,(F n).timeSlope t))
    (a b : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a))
    (hyb : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (y n)-p)) atTop (𝓝 b))
    (hjx : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (x n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i a)))
    (hjy : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (y n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i b))) :
    ∃ r : ℝ, b-a = r • reflectFirst (Directions.simplex z) := by
  by_cases hab : b-a=0
  · exact ⟨0,by simpa only [zero_smul] using hab⟩
  by_cases hs : ∃ᶠ n in atTop, 0 ≤ s n
  · obtain ⟨ρ,hρ,hρs⟩ := extraction_of_frequently_atTop hs
    obtain ⟨r,_,u,hu,hbu⟩ := actual_forward_limit (F ∘ ρ) hAB
      (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
      (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
      t htA htB (x ∘ ρ) (y ∘ ρ) (s ∘ ρ) hρs (fun n => hxy (ρ n)) a b
      (hxa.comp hρ.tendsto_atTop) (hyb.comp hρ.tendsto_atTop)
      (fun i => (hjx i).comp hρ.tendsto_atTop) (fun i => (hjy i).comp hρ.tendsto_atTop) hab
    rw [hz,mem_singleton_iff] at hu
    exact ⟨r,hu ▸ hbu⟩
  · have hs' : ∃ᶠ n in atTop, s n ≤ 0 :=
      ((not_frequently.mp hs).mono fun _ hn => (lt_of_not_ge hn).le).frequently
    obtain ⟨ρ,hρ,hρs⟩ := extraction_of_frequently_atTop hs'
    have hxy' (n : ℕ) : x (ρ n)=y (ρ n)+(-s (ρ n)) • (1,(F (ρ n)).timeSlope t) := by
      rw [hxy (ρ n),neg_smul]; abel
    have hab' : a-b ≠ 0 := by
      intro he
      exact hab (sub_eq_zero.mpr (sub_eq_zero.mp he).symm)
    obtain ⟨r,_,u,hu,hbu⟩ := actual_forward_limit (F ∘ ρ) hAB
      (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
      (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
      t htA htB (y ∘ ρ) (x ∘ ρ) (fun n => -s (ρ n))
      (fun n => neg_nonneg.mpr (hρs n)) hxy' b a
      (hyb.comp hρ.tendsto_atTop) (hxa.comp hρ.tendsto_atTop)
      (fun i => (hjy i).comp hρ.tendsto_atTop) (fun i => (hjx i).comp hρ.tendsto_atTop) hab'
    rw [hz,mem_singleton_iff] at hu
    refine ⟨-r,?_⟩
    have hbu' : a-b = r • reflectFirst (Directions.simplex z) := hu ▸ hbu
    rw [neg_smul,← hbu',neg_sub]

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimit
open Set Filter Metric
open scoped Topology

theorem jet_diagonal {ι : Type*} [Nonempty ι] [Countable ι]
    (f : ℕ → ι → PlanarHalving.Point → ℝ) (c : ι → ℝ)
    (D : ι → PlanarHalving.Point →L[ℝ] ℝ) (p : PlanarHalving.Point)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h), dist (f n i x) (c i+D i (x-p)) < ε*h)
    (B : ℝ → ℕ → Prop) (hbad : ∃ᶠ h in 𝓝[>] (0:ℝ), ∃ᶠ n in atTop, B h n) :
    ∃ h : ℕ → ℝ, ∃ N : ℕ → ℕ, (∀ m, 0 < h m) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto N atTop atTop ∧ (∀ m, B (h m) (N m)) ∧
      ∀ i R, 0 ≤ R → TendstoUniformlyOn
        (fun m w => (f (N m) i (p+h m • w)-c i)/h m) (D i) atTop (closedBall 0 R) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat ι
  let ε (m : ℕ) : ℝ := 1/(m+1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hex (m : ℕ) : ∃ h : ℝ, ∃ n : ℕ, 0<h ∧ h<ε m ∧ m≤n ∧ B h n ∧
      ∀ k ∈ Finset.range (m+1), ∀ x ∈ closedBall p ((m+1)*h),
        dist (f n (e k) x) (c (e k)+D (e k) (x-p)) < ε m*h := by
    have hf : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ k ∈ Finset.range (m+1), ∀ᶠ n in atTop,
        ∀ x ∈ closedBall p ((m+1)*h), dist (f n (e k) x)
          (c (e k)+D (e k) (x-p)) < ε m*h := by
      apply (eventually_all_finset _).mpr
      intro k _
      exact hfirst (e k) (m+1) (by positivity) (ε m) (hε m)
    have hh : ∀ᶠ h in 𝓝[>] (0:ℝ), 0<h ∧ h<ε m := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (hε m))]
        with h h0 h1
      exact ⟨h0,h1⟩
    obtain ⟨h,hb,hh,hf⟩ := (hbad.and_eventually (hh.and hf)).exists
    have hn := (eventually_all_finset (Finset.range (m+1))).mpr hf
    obtain ⟨n,hbn,hmn,hn⟩ := (hb.and_eventually ((eventually_ge_atTop m).and hn)).exists
    exact ⟨h,n,hh.1,hh.2,hmn,hbn,hn⟩
  choose h N hh hhε hN hB hj using hex
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hhlim : Tendsto h atTop (𝓝 0) := squeeze_zero (fun m => (hh m).le)
    (fun m => (hhε m).le) hεlim
  have hNlim : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  refine ⟨h,N,hh,hhlim,hNlim,hB,?_⟩
  intro i R hR
  obtain ⟨k,rfl⟩ := he i
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hmlim : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop k,hmlim.eventually (eventually_ge_atTop R),
    hεlim.eventually (gt_mem_nhds hδ)] with m hkm hRm hεδ w hw
  have hx : p+h m • w ∈ closedBall p ((m+1)*h m) := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (hh m)]
    have hw' : ‖w‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hw
    nlinarith [mul_le_mul_of_nonneg_left (hw'.trans hRm) (hh m).le]
  have hjm := hj m k (Finset.mem_range.mpr (by omega)) _ hx
  let v : ℝ := (f (N m) (e k) (p+h m • w)-c (e k))/h m-D (e k) w
  have hv : f (N m) (e k) (p+h m • w)-(c (e k)+D (e k) (p+h m • w-p))=h m*v := by
    rw [add_sub_cancel_left,map_smul]
    dsimp [v]
    field_simp [(hh m).ne']
    ring
  rw [Real.dist_eq,hv,abs_mul,abs_of_pos (hh m)] at hjm
  have hvbound : |v| < ε m := by nlinarith [hh m]
  rw [Real.dist_eq,abs_sub_comm]
  exact hvbound.trans hεδ

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma jet_at_physical (F : ℕ → Configuration) {A B C : Window}
    (hAB : Before A B) (hC : Before C A ∧ Before C B)
    (hA : ∀ n, 0 < length (F n).R A) (hB : ∀ n, 0 < length (F n).R B)
    (hCl : ∀ᶠ n in atTop, 0 < length (F n).R C)
    (D : Point →L[ℝ] ℝ) (c : ℝ) (p : Point) (h : ℕ → ℝ) (hh : ∀ n, 0<h n)
    (hj : ∀ R, 0≤R → TendstoUniformlyOn
      (fun n w => (((F n).extendedRank true A B C (p+h n • w) : ℝ)-c)/h n)
      D atTop (closedBall 0 R))
    (x : ℕ → Point) (a : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a)) :
    Tendsto (fun n => (((F n).system.labels (F n).generic (x n) C : ℝ)-c)/h n) atTop (𝓝 (D a)) := by
  let w := fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)
  have hw : ∀ᶠ n in atTop, w n∈closedBall 0 (‖a‖+1) := by
    filter_upwards [hxa.norm.eventually (gt_mem_nhds (show ‖a‖<‖a‖+1 by linarith))] with n hn
    exact mem_closedBall_zero_iff.mpr hn.le
  have hlim := (hj (‖a‖+1) (by positivity)).tendsto_comp D.continuous.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hxa,hw⟩)
  apply hlim.congr'
  filter_upwards [hCl] with n hn
  have he : p+h n • w n=(F n).rankChart hAB (hA n) (hB n) (x n) := by
    dsimp [w]
    rw [smul_smul,mul_inv_cancel₀ (hh n).ne',one_smul]
    abel
  rw [he,(F n).rankChart_apply,(F n).extendedRank_eq true hAB (by simpa using hC) (hA n) (hB n) hn]

end PlanarHalving.RankLimits

end OAI
