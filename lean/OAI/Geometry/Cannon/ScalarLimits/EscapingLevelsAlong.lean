import Mathlib
import OAI.Geometry.Cannon.Flows.EscapingLevelEnergyObstruction
import OAI.Geometry.Cannon.ScalarLimits.IntervalAvoiding

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
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonVariation

open Set Metric Filter Topology

theorem exists_variation_path {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (F : X → ℝ) (x : X) (hx : NonconstantAt F x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ v w : X, ∃ γ : Path v w, range γ ⊆ U ∧ F v < F w := by
  classical
  let V := pathComponentIn U x
  have hVo : IsOpen V := hU.pathComponentIn x
  have hxV : x ∈ V := mem_pathComponentIn_self hxU
  have hy : ∃ y ∈ V, F y ≠ F x := by
    by_contra h
    push Not at h
    exact hx (Filter.mem_of_superset (hVo.mem_nhds hxV) h)
  obtain ⟨y,hyV,hyF⟩ := hy
  have hxy : JoinedIn U x y := hyV
  rcases lt_or_gt_of_ne hyF with hlt | hgt
  · exact ⟨y,x,hxy.symm.somePath,by
      rintro _ ⟨t,rfl⟩
      exact hxy.symm.somePath_mem t,hlt⟩
  · exact ⟨x,y,hxy.somePath,by
      rintro _ ⟨t,rfl⟩
      exact hxy.somePath_mem t,hgt⟩

end CannonVariation

namespace CannonComparison

open Set Metric Filter Topology CannonApprox CannonCrossEnergyLocal CannonVariation

def EscapingLevelsAlong {X : Type*} [MetricSpace X]
    (f : ℕ → X → ℝ) (W : X → ℝ) (b : X) : Prop :=
  ∀ v w : X, ∀ γ : Path v w, ∀ a d ρ : ℝ,
    range γ ⊆ ({b}ᶜ : Set X) → W v < a → a < d → d < W w → 0 < ρ →
    ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∃ D : Set X,
      IsCompact D ∧ IsConnected D ∧ (D ∩ range γ).Nonempty ∧
      (∀ x ∈ D, f n x = t) ∧ ∃ z ∈ D, dist z b < ρ

theorem comparison_across_punctures {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (W V : X → ℝ) (b c : X) (hbc : b ≠ c)
    (hW : ContinuousOn W ({b}ᶜ : Set X)) (hV : ContinuousOn V ({c}ᶜ : Set X))
    (hfcont : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (f n) K)
    (hwcont : ∀ K : Set X, IsCompact K → c ∉ K →
      ∀ᶠ n in atTop, ContinuousOn (w n) K)
    (hflim : ∀ K : Set X, IsCompact K → b ∉ K → TendstoUniformlyOn f W atTop K)
    (hwlim : ∀ K : Set X, IsCompact K → c ∉ K → TendstoUniformlyOn w V atTop K)
    (hfe : ∀ K : Set X, IsCompact K → b ∉ K →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n) K) atTop (𝓝 0))
    (hwe : ∀ K : Set X, IsCompact K → c ∉ K →
      Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n) K) atTop (𝓝 0))
    (hlevels : EscapingLevelsAlong f W b)
    (x : X) (hxb : x ≠ b) (hxc : x ≠ c) (hx : NonconstantAt W x) : V x = V b := by
  classical
  by_contra hneq
  let η := |V x-V b|/8
  have hη : 0 < η := div_pos (abs_pos.mpr (sub_ne_zero.mpr hneq)) (by norm_num)
  have hVx : ContinuousAt V x := hV.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hxc)
  obtain ⟨δx,hδx,hδxV⟩ := Metric.continuousAt_iff.mp hVx η hη
  let U : Set X := ball x δx ∩ {b}ᶜ ∩ {c}ᶜ
  have hU : IsOpen U := (isOpen_ball.inter isClosed_singleton.isOpen_compl).inter
    isClosed_singleton.isOpen_compl
  obtain ⟨v₀,v₁,γ,hγU,hγvar⟩ := exists_variation_path W x hx U hU ⟨⟨mem_ball_self hδx,hxb⟩,hxc⟩
  let P : Set X := range γ
  have hP : IsCompact P := isCompact_range γ.continuous
  have hbP : b ∉ P := fun h => (hγU h).1.2 rfl
  have hcP : c ∉ P := fun h => (hγU h).2 rfl
  have hPV : ∀ y ∈ P, 4*η ≤ |V y-V b| := by
    intro y hy
    have hxy := hδxV (hγU hy).1.1
    rw [Real.dist_eq] at hxy
    have hh := abs_sub_le (V x) (V y) (V b)
    rw [abs_sub_comm (V x) (V y)] at hh
    have ha := abs_nonneg (V x-V b)
    dsimp [η] at hxy ⊢
    linarith
  obtain ⟨a,d,e,hva,had,hdv,he,hegap⟩ := exists_interval_avoiding hγvar (W c)
  have hWc : ContinuousAt W c := hW.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hbc.symm)
  obtain ⟨δc,hδc,hδcW⟩ := Metric.continuousAt_iff.mp hWc (e/4) (by positivity)
  let ε := min (δc/2) (dist c b/4)
  have hε : 0 < ε := lt_min (by positivity) (div_pos (dist_pos.mpr hbc.symm) (by norm_num))
  have hεδ : ε < δc := (min_le_left _ _).trans_lt (by linarith)
  have hεdist : ε < dist c b := (min_le_right _ _).trans_lt (by have := dist_pos.mpr hbc.symm; linarith)
  let Cc : Set X := closedBall c ε
  have hCc : IsCompact Cc := isClosed_closedBall.isCompact
  have hbCc : b ∉ Cc := by
    intro h
    have hh := mem_closedBall.mp h
    rw [dist_comm] at hh
    exact (not_le_of_gt hεdist) hh
  have hcW : ∀ z ∈ Cc, |W z-W c| < e/4 := by
    intro z hz
    exact hδcW ((mem_closedBall.mp hz).trans_lt hεδ)
  have hcFn : ∀ᶠ n in atTop, ∀ t ∈ Icc a d, ∀ z ∈ Cc, f n z ≠ t := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hflim Cc hCc hbCc) (e/4) (by positivity)] with n hn
    intro t ht z hz hzt
    have hh := hn z hz
    rw [Real.dist_eq,hzt,abs_sub_comm] at hh
    have hh' := abs_sub_le t (W z) (W c)
    have hg := hegap t ht
    have hwz := hcW z hz
    linarith
  obtain ⟨y,hyP,hymin⟩ := hP.exists_isMinOn (range_nonempty _) (continuous_id.dist continuous_const).continuousOn
  have hyb : y ≠ b := fun h => hbP (h ▸ hyP)
  have hydist : 0 < dist y b := dist_pos.mpr hyb
  have hVb : ContinuousAt V b := hV.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hbc)
  obtain ⟨δb,hδb,hδbV⟩ := Metric.continuousAt_iff.mp hVb η hη
  let ρ := min (δb/2) (min (dist b c/4) (dist y b/2))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min
    (div_pos (dist_pos.mpr hbc) (by norm_num)) (by positivity))
  have hρδ : ρ < δb := (min_le_left _ _).trans_lt (by linarith)
  have hρdist : ρ < dist b c := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (by have := dist_pos.mpr hbc; linarith)
  have hρP : ∀ z ∈ P, ρ < dist z b := by
    intro z hz
    have hρy : ρ < dist y b := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
    exact hρy.trans_le (hymin hz)
  let Cb : Set X := closedBall b ρ
  have hCb : IsCompact Cb := isClosed_closedBall.isCompact
  have hcCb : c ∉ Cb := by
    intro h
    have hh := mem_closedBall.mp h
    rw [dist_comm] at hh
    exact (not_le_of_gt hρdist) hh
  have hbV : ∀ z ∈ Cb, |V z-V b| < η := by
    intro z hz
    exact hδbV ((mem_closedBall.mp hz).trans_lt hρδ)
  have hgap : ∀ᶠ n in atTop, ∀ z ∈ P, ∀ t, dist t b = ρ → η ≤ |w n z-w n t| := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hwlim P hP hcP) η hη,
      Metric.tendstoUniformlyOn_iff.mp (hwlim Cb hCb hcCb) η hη] with n hnP hnB
    intro z hz t ht
    have htB : t ∈ Cb := mem_closedBall.mpr ht.le
    have he₁ := hnP z hz
    have he₂ := hnB t htB
    rw [Real.dist_eq] at he₁ he₂
    have he₃ := hbV t htB
    have he₄ := hPV z hz
    have ha₁ := abs_sub_le (V z) (w n z) (V b)
    have ha₂ := abs_sub_le (w n t) (V t) (V b)
    rw [abs_sub_comm (w n t) (V t)] at ha₂
    have ha₃ := abs_sub_le (w n z) (w n t) (V b)
    linarith
  let K : Set X := {z | ρ ≤ dist z b ∧ ε ≤ dist z c}
  let L : Set X := {z | ρ/2 ≤ dist z b ∧ ε/2 ≤ dist z c}
  have hK : IsCompact K := ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le continuous_const (continuous_id.dist continuous_const))).isCompact
  have hL : IsCompact L := ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le continuous_const (continuous_id.dist continuous_const))).isCompact
  have hbK : b ∉ K := by rintro ⟨h,_⟩; simp only [dist_self] at h; linarith
  have hcK : c ∉ K := by rintro ⟨_,h⟩; simp only [dist_self] at h; linarith
  have hbL : b ∉ L := by rintro ⟨h,_⟩; simp only [dist_self] at h; linarith
  have hcL : c ∉ L := by rintro ⟨_,h⟩; simp only [dist_self] at h; linarith
  have hKL : K ⊆ L := by rintro z ⟨h₁,h₂⟩; constructor <;> linarith
  have hCS : ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (2*r n) ⊆ L := by
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
  apply escaping_level_energy_obstruction ι p r hr hpnet f w (fun _ => L) b c ρ ε P hρP a d η had hη
    (Eventually.of_forall (fun _ => hKL)) hCS (hfcont L hL hbL) (hwcont L hL hcL) hgap _
    (hfe K hK hbK) (hwe K hK hcK)
  filter_upwards [hlevels v₀ v₁ γ a d ρ (fun z hz => (hγU hz).1.2) hva had hdv hρ,hcFn] with n hn hnC
  intro t ht
  obtain ⟨D,hD,hDconn,hDP,hDlev,hDesc⟩ := hn t ht
  refine ⟨D,hD,hDconn,hDP,hDlev,hDesc,?_⟩
  intro z hz
  by_contra hnz
  have hzC : z ∈ Cc := mem_closedBall.mpr (lt_of_not_ge hnz).le
  exact hnC t ht z hzC (hDlev z hz)

end CannonComparison

end
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
