import OAI.Geometry.PlaneColoring.DiskAverages

namespace OAI

noncomputable section
open Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma finite_packed_cover {X : Type*} [MetricSpace X] {A : Set X} (hA : TotallyBounded A)
    {ρ : ℝ} (hρ : 0<ρ) : ∃ C : Finset X, (↑C : Set X)⊆A ∧
      (∀ x∈A, ∃ c∈C, dist x c≤ρ) ∧
      (↑C : Set X).Pairwise (fun x y => ρ<dist x y) := by
  classical
  let e : ℝ≥0 := ⟨ρ,hρ.le⟩
  obtain ⟨D,_,hD,hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded
    (s := A) (ε := e/2) (by exact div_ne_zero (ne_of_gt (show (0 : ℝ≥0)<e from hρ)) (by norm_num) : e/2≠0) hA
  have hp : Metric.packingNumber e A≠⊤ := by
    have hh := (Metric.packingNumber_two_mul_le_externalCoveringNumber (e/2) A).trans
      hcover.externalCoveringNumber_le_encard
    have he : 2*(e/2)=e := by ring
    rw [he] at hh
    exact ne_top_of_le_ne_top hD.encard_lt_top.ne hh
  let C := Metric.maximalSeparatedSet e A
  have hCf : C.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet e A).encard≠⊤
    rwa [Metric.encard_maximalSeparatedSet hp])
  refine ⟨hCf.toFinset,?_,?_,?_⟩
  · simpa only [Set.Finite.coe_toFinset] using (Metric.maximalSeparatedSet_subset (ε := e) (A := A))
  · intro x hx
    obtain ⟨c,hc,hd⟩ := Metric.isCover_maximalSeparatedSet hp hx
    refine ⟨c,hCf.mem_toFinset.mpr hc,?_⟩
    change edist x c≤(e : ℝ≥0∞) at hd
    exact (ENNReal.ofReal_le_coe (b := e)).mp (by simpa only [edist_dist] using hd)
  · intro x hx y hy hne
    have hd := Metric.isSeparated_maximalSeparatedSet (ε := e) (A := A)
      (hCf.mem_toFinset.mp hx) (hCf.mem_toFinset.mp hy) hne
    exact (ENNReal.coe_lt_ofReal (a := e)).mp (by simpa only [edist_dist] using hd)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory Function
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma diskAverage_product_integrable (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i j : Fin k) (x : ℂ) (r : ℝ) :
    IntegrableOn (fun q => diskAverage c ε i q*diskAverage c ε j q) (Metric.ball x r) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by simpa using (lt_top_iff_ne_top.mpr (ball_ne_top x r))⟩
  apply Integrable.of_bound (((diskAverage_lipschitz hc hε i).continuous.mul
    (diskAverage_lipschitz hc hε j).continuous).aestronglyMeasurable) 1
  exact Eventually.of_forall fun q => by
    change ‖diskAverage c ε i q*diskAverage c ε j q‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (diskAverage_nonneg c ε i q) (diskAverage_nonneg c ε j q))]
    exact (mul_le_of_le_one_left (diskAverage_nonneg c ε j q)
      (diskAverage_le_one hc hε i q)).trans (diskAverage_le_one hc hε j q)
lemma finite_disk_overlap_cover (hc : Measurable c) {ε α : ℝ} (hε : 0<ε) (hα : 0<α)
    (i j : Fin k) (x : ℂ) {s r : ℝ} (hr : s+α*ε/16≤r) :
    ∃ C : Finset ℂ, (∀ q∈Metric.ball x s,
        α<diskAverage c ε i q → α<diskAverage c ε j q →
        ∃ z∈C, q∈Metric.ball z (α*ε/4)) ∧
      (C.card:ℝ)*(α*ε/4) ≤ (256/(Real.pi*α^3))*
        ((∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)/ε) := by
  classical
  let ρ := α*ε/8
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  let A := {q | q∈Metric.ball x s ∧ α<diskAverage c ε i q ∧ α<diskAverage c ε j q}
  obtain ⟨C,hCA,hcover,hsep⟩ := finite_packed_cover
    (A := A) ((isCompact_closedBall x s).totallyBounded.subset
      (fun _ hq => Metric.ball_subset_closedBall hq.1)) hρ
  have hsub : ∀ z∈C, Metric.ball z (ρ/2)⊆Metric.ball x r := by
    intro z hz q hq
    have hz' := (hCA hz).1
    have hq' : dist q z<ρ/2 := hq
    have hz'' : dist z x<s := hz'
    have hd := dist_triangle q z x
    change dist q x<r
    dsimp [ρ] at hq'
    linarith
  have hlow : ∀ z∈C, ∀ q∈Metric.ball z (ρ/2),
      α^2/4 ≤ diskAverage c ε i q*diskAverage c ε j q := by
    intro z hz q hq
    have hp (a : Fin k) (ha : α<diskAverage c ε a z) : α/2≤diskAverage c ε a q := by
      have hh := (diskAverage_lipschitz hc hε a).dist_le_mul q z
      change |diskAverage c ε a q-diskAverage c ε a z|≤(4/ε)*dist q z at hh
      have hh' := (abs_le.mp hh).1
      have hd : dist q z<ρ/2 := hq
      have hmul : (4/ε)*dist q z<α/2 := by
        calc (4/ε)*dist q z < (4/ε)*(ρ/2) := mul_lt_mul_of_pos_left hd (by positivity)
          _ = α/4 := by dsimp [ρ]; field_simp; ring
          _ < α/2 := by linarith
      linarith
    have hi := hp i (hCA hz).2.1
    have hj := hp j (hCA hz).2.2
    calc α^2/4 = (α/2)*(α/2) := by ring
      _ ≤ _ := mul_le_mul hi hj (by positivity) (diskAverage_nonneg c ε i q)
  have hdj : (↑C : Set ℂ).Pairwise (Disjoint on fun z => Metric.ball z (ρ/2)) := by
    intro z hz w hw hne
    apply Set.disjoint_left.mpr
    intro q hq hq'
    have hh := dist_triangle z q w
    have h₁ : dist q z<ρ/2 := hq
    have h₂ : dist q w<ρ/2 := hq'
    rw [dist_comm z q] at hh
    linarith [hsep hz hw hne]
  have hint : (C.card:ℝ)*(Real.pi*(ρ/2)^2*(α^2/4)) ≤
      ∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q := by
    calc (C.card:ℝ)*(Real.pi*(ρ/2)^2*(α^2/4)) =
        ∑ z∈C, ∫ _q in Metric.ball z (ρ/2), (α^2/4) := by
          simp only [setIntegral_const,smul_eq_mul,volumeReal_ball _ (by positivity : 0≤ρ/2)]
          simp
      _ ≤ ∑ z∈C, ∫ q in Metric.ball z (ρ/2), diskAverage c ε i q*diskAverage c ε j q := by
        apply Finset.sum_le_sum
        intro z hz
        apply setIntegral_mono_on (integrableOn_const (ball_ne_top z (ρ/2)))
          (diskAverage_product_integrable hc hε i j z (ρ/2)) measurableSet_ball
        exact hlow z hz
      _ = ∫ q in ⋃ z∈C, Metric.ball z (ρ/2), diskAverage c ε i q*diskAverage c ε j q := by
        exact (integral_biUnion_finset C (fun _ _ => measurableSet_ball) hdj
          (fun z _ => diskAverage_product_integrable hc hε i j z (ρ/2))).symm
      _ ≤ _ := setIntegral_mono_set (diskAverage_product_integrable hc hε i j x r)
        (Eventually.of_forall fun q => mul_nonneg (diskAverage_nonneg c ε i q) (diskAverage_nonneg c ε j q))
        (Eventually.of_forall (fun q hq => by
          obtain ⟨z,hz,hq⟩ := mem_iUnion₂.mp hq
          exact hsub z hz hq))
  refine ⟨C,?_,?_⟩
  · intro q hq hi hj
    obtain ⟨z,hz,hd⟩ := hcover q ⟨hq,hi,hj⟩
    refine ⟨z,hz,?_⟩
    change dist q z<α*ε/4
    dsimp [ρ] at hd
    nlinarith [mul_pos hα hε]
  · have hconst : 0<Real.pi*α^3 := by positivity
    rw [← mul_div_assoc (256/(Real.pi*α^3)) _ ε]
    apply (le_div_iff₀ hε).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hconst).mpr
    dsimp [ρ] at hint
    nlinarith [Real.pi_pos]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma missing_edge_disk_cover (hc : Measurable c) {i j : Fin k} (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0, ∀ s<R, ∀ α>0, ∀ η>0,
      ∃ δ>0, ∀ ε, 0<ε → ε<δ → ∃ C : Finset ℂ,
        (∀ q∈Metric.ball x s, α<diskAverage c ε i q → α<diskAverage c ε j q →
          ∃ z∈C, q∈Metric.ball z (α*ε/4)) ∧ (C.card:ℝ)*(α*ε/4)<η := by
  obtain ⟨R,hR,ht⟩ := missing_edge_overlap hc hne he
  refine ⟨R,hR,fun s hs α hα η hη => ?_⟩
  let r := (s+R)/2
  have hsr : s<r := by dsimp [r]; linarith
  have hrR : r<R := by dsimp [r]; linarith
  have hlim := (ht r hrR).const_mul (256/(Real.pi*α^3))
  rw [mul_zero] at hlim
  have he₁ := hlim.eventually (gt_mem_nhds hη)
  have he₂ : ∀ᶠ ε : ℝ in 𝓝[>] 0, s+α*ε/16<r := by
    have ht' : Tendsto (fun ε : ℝ => s+α*ε/16) (𝓝[>] 0) (𝓝 s) := by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := s)).add ((hid.const_mul α).div_const 16)
    exact ht'.eventually (gt_mem_nhds hsr)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhdsWithin_iff.mp (he₁.and he₂)
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  have hε' := hd (show ε∈Metric.ball 0 δ∩Ioi 0 from ⟨by simpa [Real.dist_eq,abs_of_pos hε] using hεδ,hε⟩)
  obtain ⟨C,hC,hb⟩ := finite_disk_overlap_cover hc hε hα i j x hε'.2.le
  exact ⟨C,hC,hb.trans_lt hε'.1⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace PlanarCover
lemma ball_simplyConnected (y : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (Metric.ball y r) := by
  let := (convex_ball y r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  change SimplyConnectedSpace (Metric.ball y r)
  infer_instance
lemma hit_center {F : ℂ → ℂ} {y : ℂ}
    (hc : ContinuousOn F (Metric.ball y 4))
    (hb : ∀ z ∈ Metric.ball y 4, ‖F z-z‖ ≤ 2) :
    y ∈ F '' Metric.ball y 4 := by
  by_contra hn
  have hzero : 0 ∉ (fun z => F z-y) '' Metric.ball y 4 := by
    rintro ⟨z,hz,he⟩
    apply hn
    exact ⟨z,hz,sub_eq_zero.mp he⟩
  obtain ⟨L,hLc,hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (ball_simplyConnected y (by norm_num : (0:ℝ)<4)) Metric.isOpen_ball
    (hc.sub continuousOn_const) hzero
  let e : ℝ → ℂ := fun t => Complex.exp (t*Complex.I)
  have ec : Continuous e := by fun_prop
  have en (t : ℝ) : ‖e t‖ = 1 := by simp [e,Complex.norm_exp]
  let γ : ℝ → ℂ := fun t => y+3*e t
  have γc : Continuous γ := by fun_prop
  have γmem (t : ℝ) : γ t ∈ Metric.ball y 4 := by
    norm_num [γ,Metric.mem_ball,dist_eq_norm,en]
  let H : ℝ → ℂ := fun t => (F (γ t)-y) / e t
  have Hc : Continuous H := (hc.comp_continuous γc γmem).sub continuous_const |>.div ec (fun t => Complex.exp_ne_zero _)
  have Hnear (t : ℝ) : ‖H t-3‖ ≤ 2 := by
    have he : e t ≠ 0 := Complex.exp_ne_zero _
    have h : H t-3 = (F (γ t)-γ t)/e t := by dsimp [H,γ]; field_simp; ring
    rw [h,norm_div,en,div_one]
    exact hb _ (γmem t)
  have Hpos (t : ℝ) : 0 < (H t).re := by
    have : |(H t-3).re| ≤ 2 := (Complex.abs_re_le_norm (H t-3)).trans (Hnear t)
    have := (abs_le.mp this).1
    norm_num at this
    linarith
  have Hslit (t : ℝ) : H t ∈ Complex.slitPlane := Or.inl (Hpos t)
  have logHc : Continuous (fun t => Complex.log (H t)) :=
    Hc.clog Hslit
  let d : ℝ → ℂ := fun t => L (γ t) - Complex.log (H t) - t*Complex.I
  have dc : Continuous d := ((hLc.comp_continuous γc γmem).sub logHc).sub (by fun_prop)
  have de (t : ℝ) : Complex.exp (d t) = 1 := by
    have hH : H t ≠ 0 := fun hz => by have := Hpos t; simp [hz] at this
    have hLe : Complex.exp (L (γ t)) = F (γ t)-y := hL (γmem t)
    simp only [d,Complex.exp_sub,Complex.exp_log hH,hLe]
    change (F (γ t)-y) / ((F (γ t)-y)/e t) / e t = 1
    have hF : F (γ t)-y ≠ 0 := fun hz => hzero ⟨_,γmem t,hz⟩
    have he : e t ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hconst : d 0 = d (2*Real.pi) :=
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_univ dc.continuousOn
      (fun a _ b _ => Subtype.ext ((de a).trans (de b).symm)) (mem_univ _) (mem_univ _)
  have e0 : e 0 = 1 := by simp [e]
  have e2 : e (2*Real.pi) = 1 := by simp [e,Complex.exp_two_pi_mul_I]
  have γeq : γ (2*Real.pi) = γ 0 := by dsimp [γ]; rw [e0,e2]
  have Heq : H (2*Real.pi) = H 0 := by dsimp [H]; rw [γeq,e0,e2]
  dsimp [d] at hconst
  rw [γeq,Heq] at hconst
  have hi := congrArg Complex.im hconst
  norm_num at hi
  nlinarith [Real.pi_pos]
end PlanarCover
end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
namespace PlanarCover
lemma affinePair_null (a b : ℂ) : volume (affineSpan ℝ ({a,b} : Set ℂ) : Set ℂ)=0 := by
  apply addHaar_affineSubspace volume
  intro he
  have hd : Submodule.span ℝ ({a-b} : Set ℂ)=⊤ := by
    change Submodule.span ℝ ({a -ᵥ b} : Set ℂ)=⊤
    rw [← vectorSpan_pair ℝ a b,← direction_affineSpan,he]
    exact AffineSubspace.direction_top _ _ _
  have hf := finrank_span_le_card (R := ℝ) ({a-b} : Set ℂ)
  rw [hd,finrank_top,Complex.finrank_real_complex] at hf
  norm_num at hf
lemma hit_center_subtype {Q : Set ℂ} {y : ℂ} (hQ : Metric.ball y 4 ⊆ Q)
    {F : Q → ℂ} (hc : Continuous F) (hb : ∀ z, ‖F z-z.val‖ ≤ 2) :
    y ∈ Set.range F := by
  classical
  let g : ℂ → ℂ := fun z => if hz:z∈Q then F ⟨z,hz⟩ else 0
  have ge (z : ℂ) (hz : z∈Q) : g z=F ⟨z,hz⟩ := dite_eq_left hz
  have hgc : ContinuousOn g (Metric.ball y 4) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hh := hc.comp (continuous_subtype_val.subtype_mk (fun z : Metric.ball y 4 => hQ z.property))
    convert hh using 1
    ext z
    exact ge _ (hQ z.property)
  obtain ⟨z,hz,he⟩ := hit_center hgc (fun z hz => by rw [ge _ (hQ hz)]; exact hb _)
  exact ⟨⟨z,hQ hz⟩,by rwa [ge _ (hQ hz)] at he⟩
lemma small_support_pair {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (hc : s.card≤2) : ∃ a b, s ⊆ {a,b} := by
  by_cases h1 : s.card=1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨a,a,by simp⟩
  · have h2 : s.card=2 := by have := hs.card_pos; omega
    obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨a,b,Finset.Subset.refl _⟩
lemma barycenter_two {ι : Type*} [Fintype ι] (p : ι → ℂ) (w : ι → ℝ)
    (hn : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (hcard : (Finset.univ.filter (fun i => w i≠0)).card≤2) :
    ∑ i,w i • p i ∈ ⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ) := by
  classical
  let s := Finset.univ.filter (fun i => w i≠0)
  have hsw : ∑ i ∈ s, w i = ∑ i, w i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [s] using hi
  have hsv : ∑ i∈s,w i=1 := hsw.trans hs
  have hne : s.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hsv
    exact zero_ne_one hsv
  obtain ⟨a,b,hab⟩ := small_support_pair hne hcard
  refine mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨b,?_⟩⟩
  have hm := (affineSpan ℝ ({p a,p b} : Set ℂ)).convex.sum_mem
    (z := p) (fun i _ => hn i) hsv (fun i hi => mem_affineSpan ℝ (by
      have hh := hab hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl|rfl <;> simp))
  have hh : ∑ i ∈ s, w i • p i = ∑ i, w i • p i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hi0 : w i = 0 := by simpa [s] using hi
    simp [hi0]
  rwa [hh] at hm
lemma finite_partition_impossible {ι : Type*} [Fintype ι] {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (p : ι → ℂ) (w : ι → C(Q,ℝ))
    (hn : ∀ i z,0≤w i z) (hs : ∀ z,∑ i,w i z=1)
    (hm : ∀ z,(Finset.univ.filter (fun i => w i z≠0)).card≤2)
    (hd : ∀ i z, w i z≠0 → ‖p i-z.val‖≤2) : False := by
  classical
  let F : Q → ℂ := fun z => ∑ i,w i z • p i
  have Fc : Continuous F := by fun_prop
  have Fb (z : Q) : ‖F z-z.val‖≤2 := by
    have he : F z-z.val=∑ i,w i z • (p i-z.val) := by
      simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hs,one_smul,F]
    rw [he]
    calc
      ‖∑ i,w i z • (p i-z.val)‖ ≤ ∑ i,‖w i z • (p i-z.val)‖ := norm_sum_le _ _
      _ ≤ ∑ i,w i z*2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i z=0
        · simp [hi]
        · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hn i z)]
          exact mul_le_mul_of_nonneg_left (hd i z hi) (hn i z)
      _ = 2 := by rw [← Finset.sum_mul,hs]; ring
  have hsub : Metric.ball (0:ℂ) 1 ⊆ Set.range F := by
    intro y hy
    apply hit_center_subtype (F := F) ?_ Fc Fb
    intro z hz
    apply hQ
    rw [Metric.mem_ball,dist_zero_right] at hy ⊢
    have hh := norm_add_le (z-y) y
    rw [sub_add_cancel] at hh
    have hz' : ‖z-y‖<4 := by simpa [Metric.mem_ball,dist_eq_norm] using hz
    exact hh.trans_lt (by linarith)
  have hnull : volume (⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ))=0 :=
    measure_iUnion_null fun a => measure_iUnion_null fun b => affinePair_null _ _
  have hfsub : Set.range F ⊆ ⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ) := by
    rintro _ ⟨z,rfl⟩
    exact barycenter_two p (fun i => w i z) (fun i => hn i z) (hs z) (hm z)
  have hz := measure_mono_null (hsub.trans hfsub) hnull
  exact (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (by norm_num : (0:ℝ)<1))).ne' hz
end PlanarCover
end

noncomputable section
open scoped Classical
open Set MeasureTheory
namespace PlanarCover
lemma finite_open_cover_impossible {ι : Type*} [Fintype ι] {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (U : ι → Set Q)
    (ho : ∀ i, IsOpen (U i)) (hcov : ∀ z : Q, ∃ i, z∈U i)
    (hm : ∀ z : Q, (Finset.univ.filter (fun i => z∈U i)).card≤2)
    (hd : ∀ i, ∀ x∈U i, ∀ y∈U i, ‖x.val-y.val‖≤2) : False := by
  classical
  obtain ⟨w,hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U ho (by
    intro z _
    exact mem_iUnion.mpr (hcov z))
  have hz0 : (0:ℂ)∈Q := hQ (Metric.mem_ball_self (by norm_num))
  let p : ι → Q := fun i => if h : (U i).Nonempty then h.choose else ⟨0,hz0⟩
  apply finite_partition_impossible hQ (fun i => (p i).val) w (w.nonneg) ?_ ?_ ?_
  · intro z
    simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ z)
  · intro z
    apply le_trans (Finset.card_le_card ?_) (hm z)
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact hw i (subset_closure hi)
  · intro i z hz
    have hzu : z∈U i := hw i (subset_closure hz)
    have hp : p i∈U i := by
      dsimp [p]
      rw [dite_eq_left ⟨z,hzu⟩]
      exact Classical.choose_spec _
    exact hd i _ hp z hzu
lemma compact_open_cover_impossible {ι : Type*} {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (hQc : IsCompact Q) (U : ι → Set Q)
    (ho : ∀ i, IsOpen (U i)) (hcov : ∀ z : Q, ∃ i, z∈U i)
    (hm : ∀ z : Q, ∀ i j l, z∈U i → z∈U j → z∈U l → i=j ∨ i=l ∨ j=l)
    (hd : ∀ i, ∀ x∈U i, ∀ y∈U i, ‖x.val-y.val‖≤2) : False := by
  classical
  have : CompactSpace Q := isCompact_iff_compactSpace.mp hQc
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U ho (by
    intro z _
    exact mem_iUnion.mpr (hcov z))
  apply finite_open_cover_impossible hQ (fun i : s => U i.val) (fun i => ho i.val) ?_ ?_ ?_
  · intro z
    rcases mem_iUnion.mp (hs (mem_univ z)) with ⟨i,hi⟩
    rcases mem_iUnion.mp hi with ⟨his,hiz⟩
    exact ⟨⟨i,his⟩,hiz⟩
  · intro z
    by_contra! hcard
    obtain ⟨i,hi,j,hj,l,hl,hij,hil,hjl⟩ := Finset.two_lt_card.mp hcard
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj hl
    rcases hm z i.val j.val l.val hi hj hl with h|h|h
    · exact hij (Subtype.ext h)
    · exact hil (Subtype.ext h)
    · exact hjl (Subtype.ext h)
  · intro i
    exact hd i.val
end PlanarCover
end

end OAI
