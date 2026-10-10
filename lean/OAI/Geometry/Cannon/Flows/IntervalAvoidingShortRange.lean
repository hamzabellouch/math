import Mathlib
import OAI.Geometry.Cannon.Flows.EscapingLevelEnergyObstruction
import OAI.Geometry.Cannon.Flows.FarDiam

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
namespace CannonPairs

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal

lemma interval_avoiding_short_range {u v l h : ℝ} (huv : u < v)
    (hshort : h-l < (v-u)/4) :
    ∃ a d e : ℝ, u < a ∧ a < d ∧ d < v ∧ 0 < e ∧
      ∀ t ∈ Icc a d, ∀ z ∈ Icc l h, e ≤ |t-z| := by
  by_cases hl : u+(v-u)/4 < l
  · refine ⟨u+(v-u)/12,u+(v-u)/6,(v-u)/12,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht z hz
    have hh : (v-u)/12 ≤ z-t := by linarith only [hl,ht.2,hz.1]
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hl' := le_of_not_gt hl
    refine ⟨u+2*(v-u)/3,u+5*(v-u)/6,(v-u)/12,by linarith,by linarith,
      by linarith,by linarith,?_⟩
    intro t ht z hz
    exact (show (v-u)/12 ≤ t-z by linarith only [huv,hshort,hl',ht.1,hz.2]).trans
      (le_abs_self _)

lemma cells_into_puncture_exterior {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) (p : ∀ n, ι n → X) (r : ℕ → ℝ)
    (hrlim : Tendsto r atTop (𝓝 0)) (b c : X) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i,
      (ball (p n i) (2*r n) ∩ {z | ρ ≤ dist z b ∧ ε ≤ dist z c}).Nonempty →
      closedBall (p n i) (2*r n) ⊆ {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c} := by
  have ht : ∀ᶠ n in atTop, 4*r n < min ρ ε/2 := by
    have hh : Tendsto (fun n => 4*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hrlim :
        Tendsto (fun n => 4*r n) atTop (𝓝 (4*0)))
    exact hh.eventually_lt_const (div_pos (lt_min hρ hε) (by norm_num))
  filter_upwards [ht] with n hn
  intro i hi z hz
  obtain ⟨t,hti,htK⟩ := hi
  have htz := dist_triangle t (p n i) z
  have hti' := mem_ball.mp hti
  have hzi := mem_closedBall.mp hz
  rw [dist_comm (p n i) z] at htz
  have hbtri := dist_triangle t z b
  have hctri := dist_triangle t z c
  have hbmin := min_le_left ρ ε
  have hcmin := min_le_right ρ ε
  obtain ⟨htb,htc⟩ := htK
  constructor <;> linarith

theorem path_forces_opposite_oscillation {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (v₀ v₁ : X) (γ : Path v₀ v₁) (hvar : W v₀ < W v₁)
    (hP : ∀ x ∈ range γ, ρ < dist x b)
    (q : ℝ) (hq : 0 < q)
    (hgap : ∀ x ∈ range γ, ∀ z ∈ closedBall b ρ, q ≤ |V x-V z|)
    (hW : ContinuousOn W (closedBall c ε))
    (hflim : TendstoUniformlyOn f W atTop (closedBall c ε))
    (hwlimP : TendstoUniformlyOn w V atTop (range γ))
    (hwlimB : TendstoUniformlyOn w V atTop (closedBall b ρ))
    (hfcont : ∀ᶠ n in atTop,
      ContinuousOn (f n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hwcont : ∀ᶠ n in atTop,
      ContinuousOn (w n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hlevels : ∀ a d : ℝ, W v₀ < a → a < d → d < W v₁ →
      ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
        IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
        (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ) :
    (W v₁-W v₀)/4 ≤ CannonCrossEnergy.oscillation W (closedBall c ε) := by
  by_contra hn
  have hshort : sSup (W '' closedBall c ε)-sInf (W '' closedBall c ε) <
      (W v₁-W v₀)/4 := lt_of_not_ge hn
  obtain ⟨a,d,e,hva,had,hdv,he,hegap⟩ := interval_avoiding_short_range hvar hshort
  have hCc : IsCompact (closedBall c ε) := isClosed_closedBall.isCompact
  have havoid : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∀ z ∈ closedBall c ε, f n z ≠ t := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hflim e he] with n hn
    intro t ht z hz hzt
    have hwr := CannonCrossEnergyLocal.mem_rangeInterval hW hCc hz
    have hg := hegap t ht (W z) hwr
    have hh := hn z hz
    rw [Real.dist_eq,hzt,abs_sub_comm] at hh
    exact (not_lt_of_ge hg) hh
  have hwgap : ∀ᶠ n in atTop, ∀ x ∈ range γ, ∀ z, dist z b = ρ →
      q/2 ≤ |w n x-w n z| := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hwlimP (q/4) (by positivity),
      Metric.tendstoUniformlyOn_iff.mp hwlimB (q/4) (by positivity)] with n hnP hnB
    intro x hx z hz
    have hzB : z ∈ closedBall b ρ := mem_closedBall.mpr hz.le
    have hxerr := hnP x hx
    have hzerr := hnB z hzB
    rw [Real.dist_eq] at hxerr hzerr
    have hg := hgap x hx z hzB
    have ha := abs_sub_le (V x) (w n x) (V z)
    have hb := abs_sub_le (w n x) (w n z) (V z)
    rw [abs_sub_comm (w n z) (V z)] at hb
    linarith
  apply escaping_level_energy_obstruction ι p r hr hpnet f w
    (fun _ => {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c}) b c ρ ε (range γ) hP a d (q/2)
    had (by positivity) (Eventually.of_forall (by
      intro n z hz
      constructor <;> linarith [hz.1,hz.2]))
    (cells_into_puncture_exterior ι p r hrlim b c hρ hε) hfcont hwcont hwgap _ hfe hwe
  filter_upwards [hlevels a d hva had hdv,havoid] with n hn hnA
  intro t ht
  obtain ⟨D,hD,hDconn,hDP,hDlev,hDesc⟩ := hn t ht
  refine ⟨D,hD,hDconn,hDP,hDlev,hDesc,?_⟩
  intro z hz
  by_contra hnz
  exact hnA t ht z (mem_closedBall.mpr (lt_of_not_ge hnz).le) (hDlev z hz)

end CannonPairs

namespace CannonPairs

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal

lemma separated_paths_avoid_short_range {X : Type*} [TopologicalSpace X]
    (V : X → ℝ) (P₀ P₁ E : Set X) (hP₀ : IsCompact P₀) (hne : P₀.Nonempty)
    (hE : IsCompact E) (hVP : ContinuousOn V P₀) (hVE : ContinuousOn V E)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ P₀, ∀ y ∈ P₁, V x+δ ≤ V y)
    (hshort : CannonCrossEnergy.oscillation V E < δ/4) :
    (∀ x ∈ P₀, ∀ z ∈ E, δ/4 ≤ |V x-V z|) ∨
    (∀ x ∈ P₁, ∀ z ∈ E, δ/4 ≤ |V x-V z|) := by
  let u₀ := sSup (V '' P₀)
  have hbound₀ : ∀ x ∈ P₀, V x ≤ u₀ := by
    intro x hx
    exact le_csSup (hP₀.image_of_continuousOn hVP).bddAbove (mem_image_of_mem V hx)
  have hbound₁ : ∀ y ∈ P₁, u₀+δ ≤ V y := by
    intro y hy
    have hh : u₀ ≤ V y-δ := csSup_le (hne.image V) (by
      rintro _ ⟨x,hx,rfl⟩
      linarith only [hsep x hx y hy])
    linarith only [hh]
  by_cases hhi : sSup (V '' E) ≤ u₀+δ/2
  · right
    intro x hx z hz
    have hzx := (CannonCrossEnergyLocal.mem_rangeInterval hVE hE hz).2
    have hxx := hbound₁ x hx
    exact (show δ/4 ≤ V x-V z by linarith only [hhi,hzx,hxx,hδ]).trans (le_abs_self _)
  · left
    have hhi' := lt_of_not_ge hhi
    intro x hx z hz
    have hzx := (CannonCrossEnergyLocal.mem_rangeInterval hVE hE hz).1
    have hxx := hbound₀ x hx
    dsimp [CannonCrossEnergy.oscillation] at hshort
    have hh : δ/4 ≤ V z-V x := by linarith only [hhi',hzx,hxx,hshort]
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)

theorem two_path_pair_alternative {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (gap δ : ℝ) (hgap : 0 < gap) (hδ : 0 < δ)
    (hvar : ∀ s, gap ≤ W (v₁ s)-W (v₀ s))
    (hP : ∀ s, ∀ x ∈ range (γ s), ρ < dist x b)
    (hsep : ∀ x ∈ range (γ false), ∀ y ∈ range (γ true), V x+δ ≤ V y)
    (hVP : ContinuousOn V (range (γ false)))
    (hVE : ContinuousOn V (closedBall b ρ))
    (hW : ContinuousOn W (closedBall c ε))
    (hflim : TendstoUniformlyOn f W atTop (closedBall c ε))
    (hwlimP : ∀ s, TendstoUniformlyOn w V atTop (range (γ s)))
    (hwlimB : TendstoUniformlyOn w V atTop (closedBall b ρ))
    (hfcont : ∀ᶠ n in atTop,
      ContinuousOn (f n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hwcont : ∀ᶠ n in atTop,
      ContinuousOn (w n) {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c})
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n)
      {z | ρ ≤ dist z b ∧ ε ≤ dist z c}) atTop (𝓝 0))
    (hlevels : ∀ s, ∀ a d : ℝ, W (v₀ s) < a → a < d → d < W (v₁ s) →
      ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
        IsCompact D ∧ IsConnected D ∧ (D ∩ range (γ s)).Nonempty ∧
        (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ) :
    gap/4 ≤ CannonCrossEnergy.oscillation W (closedBall c ε) ∨
      δ/4 ≤ CannonCrossEnergy.oscillation V (closedBall b ρ) := by
  by_cases hv : δ/4 ≤ CannonCrossEnergy.oscillation V (closedBall b ρ)
  · exact Or.inr hv
  left
  have hor := separated_paths_avoid_short_range V (range (γ false)) (range (γ true))
    (closedBall b ρ) (isCompact_range (γ false).continuous) (range_nonempty _)
    isClosed_closedBall.isCompact hVP hVE δ hδ hsep (lt_of_not_ge hv)
  obtain ⟨s,hs⟩ : ∃ s : Bool, ∀ x ∈ range (γ s), ∀ z ∈ closedBall b ρ,
      δ/4 ≤ |V x-V z| := by
    rcases hor with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have hh := path_forces_opposite_oscillation ι p r hr hrlim hpnet f w W V b c ρ ε
    hρ hε (v₀ s) (v₁ s) (γ s) (by linarith only [hgap,hvar s]) (hP s) (δ/4)
    (by positivity) hs hW hflim (hwlimP s) hwlimB hfcont hwcont hfe hwe (hlevels s)
  linarith only [hh,hvar s]

end CannonPairs

end

namespace CannonPairs

open Set Metric Filter Topology CannonMagnification CannonApprox

lemma uniformly_on_preimage {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (H : ℕ → X → ℝ) (f : X → ℝ) (Ω T : Set X)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (hT : IsCompact T) (hTΩ : h.symm '' T ⊆ Ω) :
    TendstoUniformlyOn (fun n => H n ∘ h.symm) (f ∘ h.symm) atTop T :=
  ((hlim (h.symm '' T) (hT.image h.symm.continuous) hTΩ).comp h.symm).mono
    (fun _ hx => mem_image_of_mem _ hx)

lemma continuousOn_preimage {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X)
    (f : X → ℝ) (Ω T : Set X) (hf : ContinuousOn f Ω) (hTΩ : h.symm '' T ⊆ Ω) :
    ContinuousOn (f ∘ h.symm) T :=
  hf.comp h.symm.continuous.continuousOn (fun _ hx => hTΩ (mem_image_of_mem _ hx))

lemma puncture_exterior_domain {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R U A ε : ℝ) (Ω : Set X)
    (hR : 0 < R) (hA : 0 < A) (hroom : 2*U/A ≤ ε)
    (hΩ : closedBall x ε ⊆ Ω)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R) :
    h.symm '' {z | A*R/2 ≤ dist z p} ⊆ Ω := by
  rintro y ⟨z,hz,rfl⟩
  apply hΩ
  rw [mem_closedBall,dist_comm]
  have hD : 0 ≤ denominator x R (h.symm z) := hR.le.trans (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_right hz hD
  have hu := hupper (h.symm z)
  rw [h.apply_symm_apply] at hu
  have hd : denominator x R (h.symm z) ≤ 2*U/A := by
    apply (le_div_iff₀ hA).mpr
    have hh : R*(A*denominator x R (h.symm z)) ≤ R*(2*U) := by
      nlinarith only [hm,hu]
    simpa only [mul_comm A] using (mul_le_mul_iff_right₀ hR).mp hh
  exact (le_max_right _ _).trans (hd.trans hroom)

lemma pattern_puncture_distance {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R V B cutoff : ℝ)
    (hR : 0 < R) (hV : 0 < V) (hB : 1 ≤ B) (hsmall : B*R ≤ cutoff)
    (hlower : ∀ y, denominator x R y ≤ cutoff →
      R ≤ V*dist (h y) p*denominator x R y)
    (T : Set X) (hT : h.symm '' T ⊆ closedBall x (B*R)) :
    ∀ z ∈ T, 1/(V*B) ≤ dist z p := by
  intro z hz
  have hd := mem_closedBall.mp (hT (mem_image_of_mem _ hz))
  have hD : denominator x R (h.symm z) ≤ B*R := by
    apply max_le (by nlinarith only [hB,hR])
    simpa only [dist_comm] using hd
  have hh := hlower (h.symm z) (hD.trans hsmall)
  rw [h.apply_symm_apply] at hh
  have hm := mul_le_mul_of_nonneg_left hD (mul_nonneg hV.le (dist_nonneg (x:=z) (y:=p)))
  have hh' : R*1 ≤ R*(V*B*dist z p) := by nlinarith only [hh,hm]
  have hz' := (mul_le_mul_iff_right₀ hR).mp hh'
  exact (div_le_iff₀ (mul_pos hV (zero_lt_one.trans_le hB))).mpr (by nlinarith only [hz'])

lemma wide_image_enters {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x p : X) (R U A d : ℝ) (hR : 0 < R)
    (hd : 0 < d) (hA : 3*U/d < A)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (K : Set X) (hK : d ≤ diam K) :
    ∃ z ∈ h '' K, dist z p < A*R := by
  obtain ⟨y,hy,hyfar⟩ := exists_far_of_diam K d hd hK x
  have hm := mul_le_mul_of_nonneg_left (hyfar.trans (le_max_right R (dist x y)))
    (dist_nonneg (x:=h y) (y:=p))
  change dist (h y) p*(d/3) ≤ dist (h y) p*denominator x R y at hm
  have hh : dist (h y) p ≤ (3*U/d)*R := by
    apply (mul_le_mul_iff_left₀ (show 0 < d/3 by positivity)).mp
    calc
      _ ≤ U*R := hm.trans (hupper y)
      _ = ((3*U/d)*R)*(d/3) := by field_simp
  exact ⟨h y,mem_image_of_mem h hy,hh.trans_lt (mul_lt_mul_of_pos_right hA hR)⟩

theorem transformed_level_paths {X : Type*} [MetricSpace X] [CompactSpace X]
    (Ω : Set X) (H : ℕ → X → ℝ) (f : X → ℝ)
    (hfunit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (d : ℝ) (hd : 0 < d)
    (hlevels : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ d ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
      ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
        (K ∩ range γ).Nonempty)
    (h : X ≃ₜ X) (x p : X) (R U A : ℝ) (hR : 0 < R) (hA : 3*U/d < A)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (v₀ v₁ : X) (γ : Path v₀ v₁) (hγ : h.symm '' range γ ⊆ Ω)
    (a b : ℝ) (ha : f (h.symm v₀) < a) (_hab : a < b) (hb : b < f (h.symm v₁)) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
      (∀ y ∈ D, (H n ∘ h.symm) y=t) ∧ ∃ y ∈ D, dist y p < A*R := by
  let π : Path (h.symm v₀) (h.symm v₁) := γ.map h.symm.continuous
  have hπ : range π ⊆ Ω := by
    rintro y ⟨s,rfl⟩
    exact hγ (mem_image_of_mem _ (mem_range_self s))
  have huv₀ : 0 ≤ f (h.symm v₀) := (hfunit _ (hπ π.source_mem_range)).1
  have huv₁ : f (h.symm v₁) ≤ 1 := (hfunit _ (hπ π.target_mem_range)).2
  have hconv := hlim (range π) (isCompact_range π.continuous) hπ
  have ht₀ : ∀ᶠ n in atTop, H n (h.symm v₀) < a :=
    (hconv.tendsto_at π.source_mem_range).eventually_lt_const ha
  have ht₁ : ∀ᶠ n in atTop, b < H n (h.symm v₁) :=
    (hconv.tendsto_at π.target_mem_range).eventually_const_lt hb
  filter_upwards [ht₀,ht₁] with n hn₀ hn₁
  intro t ht
  have htt : t ∈ Ioo (0:ℝ) 1 := ⟨huv₀.trans_lt (ha.trans_le ht.1),ht.2.trans_lt (hb.trans_le huv₁)⟩
  obtain ⟨K,hK,hKc,hKd,hKt,hhit⟩ := hlevels n t htt
  obtain ⟨z,hz,⟨s,hs⟩⟩ := hhit _ _ π hπ (hn₀.trans_le ht.1) (ht.2.trans_lt hn₁)
  refine ⟨h '' K,hK.image h.continuous,hKc.image h h.continuous.continuousOn,?_,?_,
    wide_image_enters h x p R U A d hR hd hA hupper K hKd⟩
  · refine ⟨γ s,?_,mem_range_self s⟩
    refine ⟨z,hz,?_⟩
    rw [← hs]
    exact h.apply_symm_apply (γ s)
  · rintro y ⟨z,hz,rfl⟩
    simpa only [Function.comp_apply,h.symm_apply_apply] using hKt z hz

end CannonPairs

open Set Filter Metric Topology CannonMagnification CannonApprox

namespace CannonPairs

theorem fixed_source_pair {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (Ω : Set X) (H : ℕ → X → ℝ) (f : X → ℝ)
    (hf : ContinuousOn f Ω) (hH : ∀ n, ContinuousOn (H n) Ω)
    (hfunit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K)
    (d : ℝ) (hd : 0 < d)
    (hlevels : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ d ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
      ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
        (K ∩ range γ).Nonempty)
    (hi hj : X ≃ₜ X) (xi xj pi pj : X) (R U A ε : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hwide : 3*U/d < A)
    (hroom : 2*U/A ≤ ε) (hΩi : closedBall xi ε ⊆ Ω) (hΩj : closedBall xj ε ⊆ Ω)
    (hui : ∀ y, dist (hi y) pi*denominator xi R y ≤ U*R)
    (huj : ∀ y, dist (hj y) pj*denominator xj R y ≤ U*R)
    (hfar : 2*A*R ≤ dist pi pj)
    (v₀ v₁ : Bool → X) (γ : ∀ s, Path (v₀ s) (v₁ s))
    (hP : ∀ s z, z ∈ range (γ s) → A*R < dist z pi ∧ A*R < dist z pj)
    (gap δ : ℝ) (hgap : 0 < gap) (hδ : 0 < δ)
    (hvar : ∀ s, gap ≤ f (hi.symm (v₁ s))-f (hi.symm (v₀ s)))
    (hsep : ∀ x ∈ range (γ false), ∀ y ∈ range (γ true),
      f (hj.symm x)+δ ≤ f (hj.symm y))
    (hei : ∀ K : Set X, IsCompact K → hi.symm '' K ⊆ Ω →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (H n ∘ hi.symm) K) atTop (𝓝 0))
    (hej : ∀ K : Set X, IsCompact K → hj.symm '' K ⊆ Ω →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (H n ∘ hj.symm) K) atTop (𝓝 0)) :
    gap/4 ≤ CannonCrossEnergy.oscillation f (hi.symm '' closedBall pj (A*R)) ∨
      δ/4 ≤ CannonCrossEnergy.oscillation f (hj.symm '' closedBall pi (A*R)) := by
  have hρ : 0 < A*R := mul_pos hA hR
  have hDi := puncture_exterior_domain hi xi pi R U A ε Ω hR hA hroom hΩi hui
  have hDj := puncture_exterior_domain hj xj pj R U A ε Ω hR hA hroom hΩj huj
  have hbi : hi.symm '' closedBall pj (A*R) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDi
    intro z hz
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle pi z pj
    rw [dist_comm pi z] at htri
    change A*R/2 ≤ dist z pi
    linarith only [hfar,htri,hz',hρ]
  have hbj : hj.symm '' closedBall pi (A*R) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDj
    intro z hz
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle pi z pj
    rw [dist_comm pi z] at htri
    change A*R/2 ≤ dist z pj
    linarith only [hfar,htri,hz',hρ]
  have hpathi (s : Bool) : hi.symm '' range (γ s) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDi
    intro z hz
    change A*R/2 ≤ dist z pi
    linarith only [(hP s z hz).1,hρ]
  have hpathj (s : Bool) : hj.symm '' range (γ s) ⊆ Ω := by
    apply Subset.trans (image_mono ?_) hDj
    intro z hz
    change A*R/2 ≤ dist z pj
    linarith only [(hP s z hz).2,hρ]
  let T : Set X := {z | A*R/2 ≤ dist z pi ∧ A*R/2 ≤ dist z pj}
  let K : Set X := {z | A*R ≤ dist z pi ∧ A*R ≤ dist z pj}
  have hTi : hi.symm '' T ⊆ Ω :=
    (image_mono (fun _ hz => hz.1)).trans hDi
  have hTj : hj.symm '' T ⊆ Ω :=
    (image_mono (fun _ hz => hz.2)).trans hDj
  have hKT : K ⊆ T := by
    intro z hz
    exact ⟨(by linarith only [hρ] : A*R/2 ≤ A*R).trans hz.1,
      (by linarith only [hρ] : A*R/2 ≤ A*R).trans hz.2⟩
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hh := two_path_pair_alternative ι p r hr hrlim hpnet
    (fun n => H n ∘ hi.symm) (fun n => H n ∘ hj.symm)
    (f ∘ hi.symm) (f ∘ hj.symm) pi pj (A*R) (A*R) hρ hρ v₀ v₁ γ gap δ
    hgap hδ hvar (fun s z hz => (hP s z hz).1) hsep
    (continuousOn_preimage hj f Ω _ hf (hpathj false))
    (continuousOn_preimage hj f Ω _ hf hbj)
    (continuousOn_preimage hi f Ω _ hf hbi)
    (uniformly_on_preimage hi H f Ω _ hlim isClosed_closedBall.isCompact hbi)
    (fun s => uniformly_on_preimage hj H f Ω _ hlim (isCompact_range (γ s).continuous) (hpathj s))
    (uniformly_on_preimage hj H f Ω _ hlim isClosed_closedBall.isCompact hbj)
    (Eventually.of_forall (fun n => continuousOn_preimage hi (H n) Ω T (hH n) hTi))
    (Eventually.of_forall (fun n => continuousOn_preimage hj (H n) Ω T (hH n) hTj))
    (hei K hK ((image_mono hKT).trans hTi))
    (hej K hK ((image_mono hKT).trans hTj))
    (fun s a b ha hab hb => transformed_level_paths Ω H f hfunit hlim d hd hlevels
      hi xi pi R U A hR hwide hui (v₀ s) (v₁ s) (γ s) (hpathi s) a b ha hab hb)
  simpa only [CannonCrossEnergy.oscillation, image_comp] using hh

end CannonPairs

end

end
end
end
end
end
end
end
end

end OAI
