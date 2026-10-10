import OAI.Geometry.Perimeter.Regularity.LocalFlatExcess
import OAI.Geometry.Perimeter.Regularity.SequentialFlatness
import OAI.Geometry.Perimeter.Regularity.NormalAdjustment

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def FullSlab (E : Set (Euc n)) (v : Euc n) (R a : ℝ) : Prop :=
  (∀ x∈perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|≤a) ∧
  (∀ᵐ x ∂volume, x∈Metric.ball 0 R → a < |inner ℝ v x| → (x∈E ↔ inner ℝ v x<0))

theorem FullSlab.mono_radius {E : Set (Euc n)} {v : Euc n} {R S a : ℝ}
    (h : FullSlab E v R a) (hSR : S≤R) : FullSlab E v S a := by
  refine ⟨fun x hx ↦ h.1 x ⟨hx.1,Metric.ball_subset_ball hSR hx.2⟩,?_⟩
  filter_upwards [h.2] with x hx
  exact fun hxS ↦ hx (Metric.ball_subset_ball hSR hxS)

theorem exists_fixed_normal_improvement_constants (n : ℕ) (hn : 1<n) :
    ∃ K B : ℝ, 0<K ∧ 0≤B ∧ ∀ (v : Euc n), ‖v‖=1 →
      IsLocallyPerimeterMinimizing {x : Euc n | inner ℝ x v<0} →
      ∀ r : ℝ, 0<r → r<1/8 → ∃ δ : ℝ, 0<δ ∧
        ∀ (E : Set (Euc n)), IsLocallyPerimeterMinimizing E → (0:Euc n)∈perimeterSupport E →
          ∀ a : ℝ, 0<a → a<δ → FullSlab E v 8 a →
            ∃ L : Euc n →L[ℝ] ℝ, L v=0 ∧ ‖L‖≤B ∧
              ∀ x∈perimeterSupport E ∩ Metric.ball 0 r,
                |inner ℝ v x-a*L x|≤a*K*r^2 := by
  obtain ⟨K,B,hK,hB,hseq⟩ := exists_sequential_flatness_constants n (n-1) hn (by omega)
  refine ⟨K,B,hK,hB,fun v hv hH r hr hr8 ↦ ?_⟩
  by_contra! hno
  have hex (i : ℕ) := hno (1/((i:ℝ)+1)) (by positivity)
  choose E hmin hzero a ha haδ hslab hfail using hex
  have hat : Tendsto a atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ (ha i).le) (fun i ↦ (haδ i).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htilt := orientedTilt_tendsto_of_local_halfspace_L1 hn hmin hv hH
    (tendsto_phase_slab_error (fun i ↦ (hmin i).1) hv a hat 8 (fun i ↦ (hslab i).2))
  have hsmall (i) := (hslab i).mono_radius (by norm_num : (4:ℝ)≤8)
  obtain ⟨σ,hσ,L,hLv,hLB,hflat⟩ := hseq E hmin hzero v hv (normalPlaneEuclideanChart hv)
    a ha hat (fun i ↦ (hsmall i).1) (fun i ↦ (hsmall i).2) htilt
  obtain ⟨i,hi⟩ := (hflat r hr hr8).exists
  have hh : ∀ x∈perimeterSupport (E (σ i)) ∩ Metric.ball 0 r,
      |inner ℝ v x-a (σ i)*L x|≤a (σ i)*K*r^2 := by
    intro x hx
    have hb := mul_le_mul_of_nonneg_left (hi x hx) (ha (σ i)).le
    have he : a (σ i)*|inner ℝ v x/a (σ i)-L x|=|inner ℝ v x-a (σ i)*L x| := by
      calc
        a (σ i)*|inner ℝ v x/a (σ i)-L x| = |a (σ i)*(inner ℝ v x/a (σ i)-L x)| := by
          rw [abs_mul, abs_of_pos (ha (σ i))]
        _ = _ := by congr 1; field_simp [(ha (σ i)).ne']
    rw [he] at hb
    simpa only [mul_assoc] using hb
  obtain ⟨x,hx,hbad⟩ := hfail (σ i) L hLv hLB
  exact (not_lt_of_ge (hh x hx)) hbad

end RPISingularHarnack

end

end OAI
