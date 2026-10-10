import OAI.Probability.FirstPassage.EndpointNet

namespace OAI

namespace PlanarFPP
open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology

def BallTravel (μ : Plane → ℝ) (D η δ s : ℝ) (w : Edge → ℝ) : Prop :=
  ∀ p q : Vertex, ‖latticeEmbed p‖ ≤ D*s → ‖latticeEmbed q‖ ≤ D*s →
    LocalTravel μ η δ s p q w

theorem ballTravel_of_net (μ : Plane → ℝ) (w : Edge → ℝ)
    (D γ β η δ κ : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (C n : ℕ) (hn : 0 < n) (hbox : D*n+2 ≤ (C*n : ℕ))
    (hcost : η/4*n+2*(8*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n)
    (htube : max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n)
    (hc : ∀ p ∈ latticeBox (C*n), ∀ q ∈ latticeBox (C*n),
      pathCost w p (coordinatePath p q) < 4*(latticeDistance p q : ℝ)+κ*(C*n : ℕ))
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
  have hleft : pathCost w p (coordinatePath p p') ≤ 8*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hd
    have hh := hc p hpbox p' hp'box
    dsimp [p'] at *
    linarith
  have hright : pathCost w q' (coordinatePath q' q) ≤ 8*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hd
    have hh := hc q' hq'box q hqbox
    dsimp [q'] at *
    linarith
  obtain ⟨ds,hend,hc',ht'⟩ := localTravel_attach μ w β hβ hlip p q p' q'
    (γ*n+2) (8*(γ*n+2)+κ*(C*n : ℕ)) (η/4) (δ/2) n hpu hqv hleft hright (hm u hu v hv)
  refine ⟨ds,hend,hc'.trans (by linarith),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := ht' i hi
  exact ⟨t,ht0,ht1,hbound.trans htube⟩

theorem ballTravel_parameters (D β η δ : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ κ : ℝ, ∃ C : ℕ, 0 < γ ∧ 0 < κ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧ D*n+2 ≤ (C*n : ℕ) ∧
        η/4*n+2*(8*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n ∧
        max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n := by
  obtain ⟨C,hC⟩ := exists_nat_gt (D+2)
  have hc : (0 : ℝ) < C := by linarith
  have hc' : 0 < C := by exact_mod_cast hc
  let γ := min (η/(8*(16+2*β))) (δ/12)
  let κ := η/(16*(C : ℝ))
  have hγ : 0 < γ := lt_min (div_pos hη (by positivity)) (by positivity)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hgη : (16+2*β)*γ ≤ η/8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8*(16+2*β))).mp (min_le_left _ _ : γ ≤ _)
    nlinarith
  have hgδ : γ ≤ δ/12 := min_le_right _ _
  have hk : κ*(C : ℝ)=η/16 := by dsimp [κ]; field_simp
  refine ⟨γ,κ,C,hγ,hκ,hc',?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (4*(32+4*β)/η)),
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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem badConnections_tendsto_zero (h : ExponentialEnvironment P τ)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P.real (badConnections τ κ n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (badConnections_probability h κ)
  exact (summable_box_connection_bound hκ).tendsto_atTop_zero

theorem exponential_ball_travel_nat (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  classical
  let _ := h.probability
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨γ,κ,C,hγ,hκ,hC,hparams⟩ := ballTravel_parameters D β η δ hD hβ.le hη hδ
  obtain ⟨S,hS⟩ := finite_ball_net D γ hγ
  let A (n : ℕ) := ⋃ uv ∈ S ×ˢ S, {ω | ¬LocalTravel μ (η/4) (δ/2) n
    (latticeFloor ((n : ℝ) • uv.1.val)) (latticeFloor ((n : ℝ) • uv.2.val)) (fun e => τ e ω)}
  have hA : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    apply (tendsto_order.2 ⟨?_,?_⟩)
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
    · intro ε hε
      have hden : 0 < ((S ×ˢ S).card : ℝ)+1 := by positivity
      filter_upwards [eventually_ge_atTop 1,
        exponential_local_travel_nat h μ hμ ht (2*D+4) (η/4) (δ/2)
          (by linarith) (by linarith) (by linarith)
          (ε/(((S ×ˢ S).card : ℝ)+1)) (div_pos hε hden)] with n hn hh
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hbound : P.real (A n) ≤ ((S ×ˢ S).card : ℝ)*(ε/(((S ×ˢ S).card : ℝ)+1)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc
          _ ≤ ∑ _uv ∈ S ×ˢ S, ε/(((S ×ˢ S).card : ℝ)+1) := by
            apply sum_le_sum
            intro uv huv
            apply (hh _ _ ?_).le
            rw [latticeEmbed_sub]
            exact (norm_sub_le _ _).trans (by
              have h1 := scaled_net_norm D uv.1 n
              have h2 := scaled_net_norm D uv.2 n
              nlinarith)
          _ = _ := by simp
      apply hbound.trans_lt
      have he := (div_pos hε hden)
      have hid : ((((S ×ˢ S).card : ℝ)+1))*(ε/(((S ×ˢ S).card : ℝ)+1))=ε := by field_simp
      nlinarith
  have hCn : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  have hB := (badConnections_tendsto_zero h κ hκ).comp hCn
  have hbound : ∀ᶠ n : ℕ in atTop,
      P.real {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)} ≤
        P.real (badConnections τ κ (C*n))+P.real (A n) := by
    filter_upwards [hparams] with n hn
    have hsub : {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)} ⊆
        badConnections τ κ (C*n) ∪ A n := by
      intro ω hω
      by_contra hb
      have hc : ω ∉ badConnections τ κ (C*n) := fun hc => hb (Or.inl hc)
      have hm : ω ∉ A n := fun hm => hb (Or.inr hm)
      apply hω
      apply ballTravel_of_net μ _ D γ β η δ κ hβ.le hlip S hS C n
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      · intro p hp q hq
        by_contra hh
        exact hc (mem_iUnion₂.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hh⟩)
      · intro u hu v hv
        by_contra hh
        exact hm (mem_iUnion₂.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,hh⟩)
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound
    (by simpa using hB.add hA)

end PlanarFPP

end OAI
