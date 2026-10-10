import OAI.Probability.GammaPassage.EndpointNet

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

def BallTravel (μ : Plane → ℝ) (D η δ s : ℝ) (w : Edge → ℝ) : Prop :=
  ∀ p q : Vertex, ‖latticeEmbed p‖ ≤ D*s → ‖latticeEmbed q‖ ≤ D*s →
    LocalTravel μ η δ s p q w

theorem ballTravel_of_net (μ : Plane → ℝ) (w : Edge → ℝ)
    (D γ β η δ κ A : ℝ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (C n : ℕ) (hn : 0 < n) (hbox : D*n+2 ≤ (C*n : ℕ))
    (hcost : η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n)
    (htube : max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n)
    (hc : ∀ p ∈ latticeBox (C*n), ∀ q ∈ latticeBox (C*n),
      pathCost w p (coordinatePath p q) < A*(latticeDistance p q : ℝ)+κ*(C*n : ℕ))
    (hm : ∀ u ∈ S, ∀ v ∈ S, LocalTravel μ (η/4) (δ/2) n
      (latticeFloor ((n : ℝ) • u.val)) (latticeFloor ((n : ℝ) • v.val)) w) :
    BallTravel μ D η δ n w := by
  intro p q hp hq
  obtain ⟨u,hu,hpu⟩ := scaled_net_approximates D γ S hS n hn p hp
  obtain ⟨v,hv,hqv⟩ := scaled_net_approximates D γ S hS n hn q hq
  let p' := latticeFloor ((n : ℝ) • u.val)
  let q' := latticeFloor ((n : ℝ) • v.val)
  have hpbox : p ∈ latticeBox (C*n) := lattice_mem_box_of_norm p (C*n) (hp.trans (by linarith))
  have hqbox : q ∈ latticeBox (C*n) := lattice_mem_box_of_norm q (C*n) (hq.trans (by linarith))
  have hp'box : p' ∈ latticeBox (C*n) := lattice_mem_box_of_norm p' (C*n)
    ((scaled_net_norm D u n).trans hbox)
  have hq'box : q' ∈ latticeBox (C*n) := lattice_mem_box_of_norm q' (C*n)
    ((scaled_net_norm D v n).trans hbox)
  have hleft : pathCost w p (coordinatePath p p') ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hd
    have hh := hc p hpbox p' hp'box
    dsimp [p'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hp' := mul_le_mul_of_nonneg_left hpu hA.le
    nlinarith
  have hright : pathCost w q' (coordinatePath q' q) ≤ (2*A)*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hd
    have hh := hc q' hq'box q hqbox
    dsimp [q'] at *
    have hd' := mul_le_mul_of_nonneg_left hd hA.le
    have hq' := mul_le_mul_of_nonneg_left hqv hA.le
    nlinarith
  obtain ⟨ds,hend,hc',ht'⟩ := localTravel_attach μ w β hβ hlip p q p' q'
    (γ*n+2) ((2*A)*(γ*n+2)+κ*(C*n : ℕ)) (η/4) (δ/2) n hpu hqv hleft hright (hm u hu v hv)
  refine ⟨ds,hend,hc'.trans (by linarith),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := ht' i hi
  exact ⟨t,ht0,ht1,hbound.trans htube⟩

theorem ballTravel_parameters (D β η δ A : ℝ)
    (hA : 0 < A)
    (hD : 0 < D) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ κ : ℝ, ∃ C : ℕ, 0 < γ ∧ 0 < κ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧ D*n+2 ≤ (C*n : ℕ) ∧
        η/4*n+2*((2*A)*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n ∧
        max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n := by
  obtain ⟨C,hC⟩ := exists_nat_gt (D+2)
  have hc : (0 : ℝ) < C := by linarith
  have hc' : 0 < C := by exact_mod_cast hc
  let γ := min (η/(8*(4*A+2*β))) (δ/12)
  let κ := η/(16*(C : ℝ))
  have hγ : 0 < γ := lt_min (div_pos hη (by positivity)) (by positivity)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hgη : (4*A+2*β)*γ ≤ η/8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8*(4*A+2*β))).mp (min_le_left _ _ : γ ≤ _)
    nlinarith
  have hgδ : γ ≤ δ/12 := min_le_right _ _
  have hk : κ*(C : ℝ)=η/16 := by dsimp [κ]; field_simp
  refine ⟨γ,κ,C,hγ,hκ,hc',?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (4*(8*A+4*β)/η)),
    hlim.eventually (eventually_ge_atTop (24/δ))] with n hn hnη hnδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hhη := (div_le_iff₀ hη).mp hnη
  have hhδ := (div_le_iff₀ hδ).mp hnδ
  have hge := mul_le_mul_of_nonneg_right hgη hn0
  have hgd := mul_le_mul_of_nonneg_right hgδ hn0
  have hcb := mul_le_mul_of_nonneg_right hC.le hn0
  simp only [Nat.cast_mul]
  refine ⟨by omega,by nlinarith,?_,?_⟩
  · have he : κ*((C : ℝ)*n)=(η/16)*n := by rw [← mul_assoc,hk]
    rw [he]
    nlinarith
  · apply max_le <;> nlinarith

theorem localTravel_mono (μ : Plane → ℝ) (w : Edge → ℝ) (p q : Vertex)
    {η δ s η' δ' s' : ℝ} (hη : η*s ≤ η'*s') (hδ : δ*s ≤ δ'*s')
    (h : LocalTravel μ η δ s p q w) : LocalTravel μ η' δ' s' p q w := by
  obtain ⟨ds,hend,hcost,htube⟩ := h
  refine ⟨ds,hend,hcost.trans (add_le_add le_rfl hη),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := htube i hi
  exact ⟨t,ht0,ht1,hbound.trans hδ⟩

theorem measurableSet_localTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) :
    MeasurableSet {w | LocalTravel μ η δ s p q w} := by
  have hm := measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e)
    measurable_pi_apply
    (fun x ds => x=p ∧ x+displacement ds=q ∧ PathIn x ds (SegmentTube p q (δ*s)))
    (fun _ _ => μ (latticeEmbed (q-p))+η*s)
  convert hm using 1
  ext w
  constructor
  · rintro ⟨ds,hend,hcost,htube⟩
    exact ⟨p,ds,⟨rfl,hend,htube⟩,hcost⟩
  · rintro ⟨x,ds,⟨rfl,hend,htube⟩,hcost⟩
    exact ⟨ds,hend,hcost,htube⟩

end GammaFPP.IntervalTravelBridge

end OAI
