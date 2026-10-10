import OAI.MeasureTheory.Falconer.Fourier.PolicyJetData
import OAI.MeasureTheory.Falconer.Graphs.GraphPolicyScales
import OAI.MeasureTheory.Falconer.Graphs.GraphTestScales
import OAI.MeasureTheory.Falconer.Graphs.JetStateGraph
import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness

namespace OAI

/-! # The direct policy witness supplies the actual graph geometry -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def graphData (P : PolicyJetData m) (k : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hσ : 0 < P.σ) (hJ : 0 < P.J) (hi : P.i+1 ≤ P.J)
    (hNlist : Classical.choose (eventual_descriptor_list_scale 3 hB hσ) ≤ P.N)
    (hNwidth : Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ) ≤ P.N)
    (d : PolicyDescriptor)
    (hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d)
    (c₀ C H : ℝ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt (m+3:ℕ) ≤ C) (hH : 0 ≤ H)
    (hlarge : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (hlargeπ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (S : Finset (Sphere (m+3))) (η : Sphere (m+3) → Sphere (m+3) → ℝ)
    (hcontrol : ∀ w ∈ S, ChartCapControl k (η w) (w : Space (m+3))
      (policyGraphRadius P.N P.a (descriptorAnchor d) P.σ c₀) H)
    (hnonneg : ∀ w ∈ S, ∀ z, 0 ≤ η w z) (hone : ∀ z, ∑ w ∈ S, η w z = 1) :
    JetStateGraphData (m+1) k (20*P.σ) B := by
  let p := descriptorAnchor d
  let g := max P.a (p-descriptorLength d)
  let δ := policyGraphRadius P.N P.a p P.σ c₀
  let τ := policyGraphWidth P.N p P.σ
  let E := descriptorListScale B P.N P.σ P.longest P.list
  let Dsymbol := max 1 E
  let Dgraph := policyGraphScale P.N P.a p P.longest P.σ c₀ C
  have hap : P.a ≤ p := hd.anchor_gt.le
  have hpN : p ≤ P.N := hd.anchor_lt.le.trans (P.base_right.trans P.base_N)
  have hag : P.a ≤ g := le_max_left _ _
  have hgp : g ≤ p := hd.g_lt.le
  have hσN : 0 ≤ P.σ*(P.N:ℝ) := by positivity
  have hdepth : (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N := by
    have hh := hd.depth_scale
    change ((p-P.a:ℕ):ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N at hh
    simpa only [Nat.cast_sub hap] using hh
  have hlength : (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N := by
    simpa only [p,longest,list,hd.maximal] using hd.length_scale
  have hscale :=
    policy_graph_scale_data (m+3) P.N_pos hσ hc₀ hcsmall hC hCdim
      hdepth hlength hd.frequency_slack hlarge hlargeπ
  have hδ := hscale.1
  have hδsmall := hscale.2.1
  have hτ := hscale.2.2.1
  have hDgraph := hscale.2.2.2.1
  have hcap := hscale.2.2.2.2.1
  have hendpoint := hscale.2.2.2.2.2.1
  have hphase := hscale.2.2.2.2.2.2.1
  have hfreq := hscale.2.2.2.2.2.2.2.1
  have hlist := (Classical.choose_spec (eventual_descriptor_list_scale 3 hB hσ))
    P.N hNlist P.longest P.list P.list_card
  have hE : E ≤ descriptorDerivativeScale P.N P.σ P.longest := by
    have hh := hlist.2
    have he : 0 ≤ E := by dsimp [E,descriptorListScale]; positivity
    linarith
  have hsymbol : Dsymbol ≤ descriptorDerivativeScale P.N P.σ P.longest :=
    max_le (by linarith [hlist.1]) hE
  have hsymbolGraph : 1+Dsymbol ≤ Dgraph := policy_graph_symbol_scale hC hc₀ hsymbol
  have hside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side = (2:ℝ)^(-(P.a:ℝ)) := by
    rw [P.Q.descendant_side,P.unit,hZ,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div]
  have hsmallside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side/(2:ℝ)^(g-P.a) = 1/(2:ℝ)^g := by
    rw [descendant_common_band_scale P.Q P.unit Z hZ hag,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hwidth : 2*τ+2*δ*(Real.sqrt (m+3:ℕ)*(1/(2:ℝ)^g)) ≤
      angularTestWidth P.N P.σ P.J (P.i+1) p := by
    have hh := (Classical.choose_spec (uniform_graph_parallel_width (m+3) hσ hJ))
      P.N hNwidth P.a g p (P.i+1) hag hi δ hδ.le
      (policyGraphRadius_le P.N P.a p P.σ c₀)
    simpa only [τ,policyGraphWidth_eq] using hh
  refine {
    Q := P.Q, unit := P.unit, ρ := P.ρ, profile := P.profile, N := P.N,
    s := P.s, lam := P.lam, regular := P.regular, N_pos := P.N_pos,
    a := P.a, p := p, g := g, ap := hap, pN := hpN, ag := hag, gp := hgp,
    σ := P.σ, σ_nonneg := hσ.le, gap := ?_, X := P.X, Y := P.Y,
    X_length := P.X_length, Y_length := P.Y_length, v := P.t,
    τ := τ, δ := δ, capBound := H, Dq := 1,
    Dmask := 8*max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)),
    Dsymbol := Dsymbol, Dgraph := Dgraph,
    τ_pos := hτ, δ_pos := hδ, δ_small := hδsmall, capBound_nonneg := hH,
    Dq_nonneg := by norm_num, Dmask_one := ?_, Dsymbol_one := le_max_left _ _,
    Dgraph_one := hDgraph, symbol_scale := hsymbolGraph, cap_scale := hcap,
    endpoint_scale := ?_, phase_error := ?_,
    frequency := by simpa only [τ,Real.rpow_natCast] using hfreq, test_scale := ?_,
    F := P.list, masks := P.masks, J := P.J, i := P.i, separated := P.separated,
    mask_scale := ?_, list_scale := le_max_right _ _, parallel := hd.companion,
    left_width := ?_, right_width := ?_, caps := S, partition := η,
    cap_control := hcontrol, cap_nonneg := hnonneg, partition_one := hone }
  · have hh := hd.g_slack
    dsimp only [g,p]
    linarith
  · have hh : 1 ≤ max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)) := le_max_left _ _
    linarith
  · simpa only [hside P.X P.X_length] using hendpoint
  · rw [descendant_common_band_scale P.Q P.unit P.X P.X_length hap,
      hside P.X P.X_length]
    simpa only [δ,τ] using hphase
  · have htau : 4*τ*((2:ℝ)^(p-P.a)/(P.Q.descendant P.X).side) =
        4*((2:ℝ)^P.N)^(30*P.σ) := by
      dsimp only [τ]
      rw [P.Q.descendant_side,P.unit,P.X_length,policyGraphWidth_eq]
      have hp : (2:ℝ)^P.a*(2:ℝ)^(p-P.a) = (2:ℝ)^p := by
        rw [← pow_add,Nat.add_sub_of_le hap]
      rw [← hp]
      field_simp
    rw [htau]
    exact Nat.le_ceil _
  · intro b hb
    exact descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)
  · simpa only [hsmallside P.X P.X_length] using hwidth
  · simpa only [hsmallside P.Y P.Y_length] using hwidth

end PolicyJetData
end Falconer

end OAI
